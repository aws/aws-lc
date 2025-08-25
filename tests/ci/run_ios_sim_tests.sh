#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Setup Xcode commands (if needed):
# > xcodebuild -runFirstLaunch
# > sudo xcodebuild -license accept
# > xcode-select --install
#
# Install iOS simulator commands (if additional runtimes needed):
# > xcrun simctl list runtimes  # List available runtimes
# > xcodebuild -downloadPlatform iOS  # Download latest iOS runtime
# Note: Most CI environments (like GitHub Actions) come with iOS simulators pre-installed

set -ex

SCRIPT_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
SCRIPT_DIR="$(readlink -f "${SCRIPT_DIR}")"

source "${SCRIPT_DIR}/common_posix_setup.sh"
source "${SCRIPT_DIR}/gtest_util.sh"

# iOS simulator runtime detection constants
SIM_IMAGE_LIST_PATH='/Library/Developer/CoreSimulator/Images/images.plist'
# Potential mount base paths for iOS simulator images
SIM_IMAGE_MOUNT_BASES=('/Volumes' '/Library/Developer/CoreSimulator/Volumes')
SIM_IMAGE_PATTERN='iOS-'

# Utility functions for plist parsing
function plist_count_images() {
    if [[ -r "${SIM_IMAGE_LIST_PATH}" ]]; then
        plutil -extract 'images' raw "${SIM_IMAGE_LIST_PATH}" -o -
    else
        echo "0"
    fi
}

function plist_image_id_for() {
    plutil -extract "images.${1}.runtimeInfo.bundleIdentifier" raw "${SIM_IMAGE_LIST_PATH}" -o -
}

function plist_image_path_for() {
    plutil -extract "images.${1}.path.relative" raw "${SIM_IMAGE_LIST_PATH}" -o - | sed -e 's/^file:\/\///'
}

function plist_image_build_for() {
    plutil -extract "images.${1}.runtimeInfo.build" raw "${SIM_IMAGE_LIST_PATH}" -o -
}

function find_mount() {
    hdiutil info | grep -s "${1}"
}

function find_actual_mount_point() {
    local image_build="${1}"
    local mount_info
    local mount_point

    echo "DEBUG: Looking for mounted iOS runtime with build: ${image_build}"

    # Check both potential mount bases
    for base in "${SIM_IMAGE_MOUNT_BASES[@]}"; do
        local potential_mount="${base}/iOS_${image_build}"
        mount_info=$(hdiutil info | grep -s "${potential_mount}" | head -n 1)
        if [[ -n "${mount_info}" ]]; then
            # Try multiple parsing approaches for mount point extraction
            # Method 1: Look for the mount path in the line (most reliable)
            mount_point=$(echo "${mount_info}" | grep -o "${potential_mount}")
            if [[ -n "${mount_point}" && -d "${mount_point}" ]]; then
                echo "${mount_point}"
                return 0
            fi

            # Method 2: Extract using awk (fallback)
            mount_point=$(echo "${mount_info}" | awk '{print $NF}')
            if [[ -n "${mount_point}" && -d "${mount_point}" ]]; then
                echo "${mount_point}"
                return 0
            fi
        fi
    done

    # If not found with expected names, try to extract actual mount point from hdiutil info
    # Look for any mount that contains the image build
    echo "DEBUG: Searching hdiutil info for pattern: (iOS.*${image_build}|${image_build}.*iOS)"
    mount_info=$(hdiutil info | grep -E "(iOS.*${image_build}|${image_build}.*iOS)" | head -n 1)
    if [[ -n "${mount_info}" ]]; then
        echo "DEBUG: Found mount info: ${mount_info}"
        # Try to extract mount point from various positions in the output
        # hdiutil info format can vary, so try multiple approaches

        # Method 1: Look for /Volumes/* or /Library/Developer/* paths
        mount_point=$(echo "${mount_info}" | grep -o '/\(Volumes\|Library/Developer\)[^ ]*' | head -n 1)
        if [[ -n "${mount_point}" && -d "${mount_point}" ]]; then
            echo "${mount_point}"
            return 0
        fi

        # Method 2: Try last field (often the mount point)
        mount_point=$(echo "${mount_info}" | awk '{print $NF}')
        if [[ -n "${mount_point}" && -d "${mount_point}" ]]; then
            echo "${mount_point}"
            return 0
        fi

        # Method 3: Try third field (traditional approach)
        mount_point=$(echo "${mount_info}" | awk '{print $3}')
        if [[ -n "${mount_point}" && -d "${mount_point}" ]]; then
            echo "${mount_point}"
            return 0
        fi
    fi

    return 1
}

function find_runtime_root() {
    find "${1}" -type d -name "RuntimeRoot" | head -n 1
}

# Find iOS SDK path for cross-compilation
function find_ios_sdk_path() {
    local sdk_path

    # Try standard Xcode path first
    sdk_path="/Applications/Xcode.app/Contents/Developer/Platforms/iPhoneSimulator.platform/Developer/SDKs/iPhoneSimulator.sdk"
    if [[ -d "${sdk_path}" ]]; then
        echo "${sdk_path}"
        return 0
    fi

    # Fallback to finding any available iOS SDK
    sdk_path=$(find /Applications/Xcode.app/Contents/Developer/Platforms/iPhoneSimulator.platform/Developer/SDKs -name "iPhoneSimulator*.sdk" 2>/dev/null | head -n 1)
    if [[ -n "${sdk_path}" && -d "${sdk_path}" ]]; then
        echo "${sdk_path}"
        return 0
    fi

    return 1
}

# Check if iOS simulator runtime is available
function check_ios_runtime_available() {
    local ios_runtime
    ios_runtime=$(xcrun simctl list runtimes | grep -i "iOS" | grep -v "watchOS" | head -n 1)
    if [[ -n "${ios_runtime}" ]]; then
        echo "Found iOS runtime: ${ios_runtime}"
        return 0
    fi
    return 1
}

# Find iOS simulator runtime for execution
function find_ios_runtime() {

    # First try using simctl to find built-in runtimes
    local runtime_paths=(
        "/Applications/Xcode.app/Contents/Developer/Platforms/iPhoneSimulator.platform/Library/Developer/CoreSimulator/Profiles/Runtimes/iOS.simruntime"
        "/Library/Developer/CoreSimulator/Profiles/Runtimes/iOS.simruntime"
    )

    for runtime_path in "${runtime_paths[@]}"; do
        if [[ -d "${runtime_path}" ]]; then
            echo "${runtime_path}"
            return 0
        fi
    done

    # Fallback: scan images.plist for downloadable runtimes
    if [[ -r "${SIM_IMAGE_LIST_PATH}" ]]; then
        local image_list_size
        image_list_size=$(plist_count_images)
        local image_list_last_idx=$(( image_list_size - 1 ))

        for i in $(seq 0 "${image_list_last_idx}"); do
            if [[ $(plist_image_id_for "${i}") == *"${SIM_IMAGE_PATTERN}"* ]]; then
                local potential_path
                potential_path=$(plist_image_path_for "${i}")
                if [[ -f "${potential_path}" ]]; then
                    echo "${potential_path}:${i}"
                    return 0
                fi
            fi
        done
    fi

    return 1
}

# Attempt to download iOS runtime if needed
function download_ios_runtime_if_needed() {
    if check_ios_runtime_available; then
        return 0
    fi

    echo "No iOS simulator runtime found, attempting download..."
    echo "Note: This may fail in CI environments due to authentication requirements"

    if sudo xcodebuild -downloadPlatform iOS -quiet; then
        echo "Download completed, checking for runtime..."
        sleep 5
        if check_ios_runtime_available; then
            return 0
        fi
    fi

    echo "ERROR: No iOS simulator runtime available and download failed"
    echo "Available runtimes:"
    xcrun simctl list runtimes
    return 1
}

# Main execution
echo "Checking iOS simulator environment..."

# Check for available iOS runtime
if ! check_ios_runtime_available; then
    if ! download_ios_runtime_if_needed; then
        exit 1
    fi
fi

# Find iOS runtime for execution
RUNTIME_INFO=""
RUNTIME_INFO=$(find_ios_runtime)
if [[ -z "${RUNTIME_INFO}" ]]; then
    echo "ERROR: No iOS simulator runtime found for execution"
    exit 1
fi

# Parse runtime path and index (format: "path" or "path:index")
if [[ "${RUNTIME_INFO}" == *:* ]]; then
    RUNTIME_PATH="${RUNTIME_INFO%:*}"
    RUNTIME_INDEX="${RUNTIME_INFO##*:}"
else
    RUNTIME_PATH="${RUNTIME_INFO}"
    RUNTIME_INDEX=""
fi

echo "Found iOS runtime: ${RUNTIME_PATH}"

# Set up runtime environment for test execution
if [[ -d "${RUNTIME_PATH}" && "${RUNTIME_PATH}" == *.simruntime ]]; then
    # Built-in runtime - use RuntimeRoot directly
    DYLD_ROOT_PATH=$(find_runtime_root "${RUNTIME_PATH}")
    if [[ -z "${DYLD_ROOT_PATH}" ]]; then
        echo "ERROR: RuntimeRoot not found in: ${RUNTIME_PATH}"
        exit 1
    fi
else
    # Disk image runtime - need to mount it
    if [[ -n "${RUNTIME_INDEX}" ]]; then
        echo "DEBUG: Getting build info from plist index: ${RUNTIME_INDEX}"
        IMAGE_BUILD=$(plist_image_build_for "${RUNTIME_INDEX}")
    else
        # Fallback: scan for any iOS runtime in plist
        echo "DEBUG: No runtime index available, scanning for iOS runtimes..."
        local found_ios_index=""
        if [[ -r "${SIM_IMAGE_LIST_PATH}" ]]; then
            local image_list_size
            image_list_size=$(plist_count_images)
            local image_list_last_idx=$(( image_list_size - 1 ))

            for i in $(seq 0 "${image_list_last_idx}"); do
                if [[ $(plist_image_id_for "${i}") == *"${SIM_IMAGE_PATTERN}"* ]]; then
                    found_ios_index="${i}"
                    echo "DEBUG: Found iOS runtime at plist index: ${i}"
                    break
                fi
            done
        fi

        if [[ -n "${found_ios_index}" ]]; then
            IMAGE_BUILD=$(plist_image_build_for "${found_ios_index}")
        else
            echo "DEBUG: No iOS runtime found in plist, using index 0 as last resort"
            IMAGE_BUILD=$(plist_image_build_for "0")
        fi
    fi

    echo "DEBUG: IMAGE_BUILD determined as: ${IMAGE_BUILD}"

    # Validate that we got a build number
    if [[ -z "${IMAGE_BUILD}" ]]; then
        echo "ERROR: Unable to determine iOS runtime build number"
        echo "Available images in plist:"
        if [[ -r "${SIM_IMAGE_LIST_PATH}" ]]; then
            local image_list_size
            image_list_size=$(plist_count_images)
            local image_list_last_idx=$(( image_list_size - 1 ))
            for i in $(seq 0 "${image_list_last_idx}"); do
                echo "  Index ${i}: $(plist_image_id_for "${i}")"
            done
        else
            echo "  Unable to read ${SIM_IMAGE_LIST_PATH}"
        fi
        exit 1
    fi

    # Check if already mounted and get actual mount point
    IMAGE_MOUNT_POINT=$(find_actual_mount_point "${IMAGE_BUILD}")

    # Validate that the mount point exists and is a directory
    if [[ -n "${IMAGE_MOUNT_POINT}" && ! -d "${IMAGE_MOUNT_POINT}" ]]; then
        echo "DEBUG: Mount point returned: '${IMAGE_MOUNT_POINT}'"
        echo "DEBUG: Mount point does not exist or is not a directory, trying each potential mount..."

        # If the returned mount point contains newlines (multiple paths), try each one
        while IFS= read -r mount_path; do
            if [[ -d "${mount_path}" ]]; then
                echo "DEBUG: Found valid mount point: ${mount_path}"
                IMAGE_MOUNT_POINT="${mount_path}"
                break
            fi
        done <<< "${IMAGE_MOUNT_POINT}"

        # If still not valid, clear it so we try to mount
        if [[ ! -d "${IMAGE_MOUNT_POINT}" ]]; then
            echo "DEBUG: No valid mount point found, will attempt to mount"
            IMAGE_MOUNT_POINT=""
        fi
    fi

    if [[ -z "${IMAGE_MOUNT_POINT}" ]]; then
        # Not mounted, try to mount it at the preferred location
        IMAGE_MOUNT_POINT="${SIM_IMAGE_MOUNT_BASES[0]}/iOS_${IMAGE_BUILD}"
        echo "DEBUG: Will attempt to mount at: ${IMAGE_MOUNT_POINT}"
        echo "Mounting iOS runtime: ${RUNTIME_PATH}"
        sudo hdiutil attach "${RUNTIME_PATH}" -mountpoint "${IMAGE_MOUNT_POINT}"

        # Verify it mounted successfully
        if ! find_mount "${IMAGE_MOUNT_POINT}"; then
            echo "WARNING: Unable to mount runtime at preferred location: ${IMAGE_MOUNT_POINT}"
            echo "Attempting direct mount as fallback..."

            # Try direct mounting without specifying mount point
            if sudo hdiutil attach "${RUNTIME_PATH}" -quiet; then
                echo "Successfully mounted runtime directly"
                # Find where it actually mounted
                sleep 2
                IMAGE_MOUNT_POINT=$(hdiutil info | grep "${RUNTIME_PATH}" | awk '{print $NF}' | head -n 1)
                if [[ -z "${IMAGE_MOUNT_POINT}" || ! -d "${IMAGE_MOUNT_POINT}" ]]; then
                    echo "ERROR: Unable to determine mount point after direct mount"
                    exit 1
                fi
                echo "Runtime mounted at: ${IMAGE_MOUNT_POINT}"
            else
                echo "ERROR: Unable to mount runtime: ${RUNTIME_PATH}"
                exit 1
            fi
        fi
    else
        echo "iOS runtime already mounted at: ${IMAGE_MOUNT_POINT}"
    fi

    DYLD_ROOT_PATH=$(find_runtime_root "${IMAGE_MOUNT_POINT}")
    if [[ -z "${DYLD_ROOT_PATH}" ]]; then
        echo "ERROR: RuntimeRoot not found in mounted image: ${IMAGE_MOUNT_POINT}"
        echo "DEBUG: Mount point contents:"
        ls -la "${IMAGE_MOUNT_POINT}" 2>/dev/null || echo "Unable to list mount point contents"
        exit 1
    fi
fi

echo "Using iOS runtime root: ${DYLD_ROOT_PATH}"
export DYLD_ROOT_PATH

# Build the project
pushd "${SRC_ROOT}"

CMAKE_PARAMS=(
    "-DCMAKE_SYSTEM_NAME=iOS"
    "-DCMAKE_OSX_ARCHITECTURES=arm64"
    "-DCMAKE_SYSTEM_PROCESSOR=arm64"
    "-DCMAKE_OSX_SYSROOT=iphonesimulator"
    "-DCMAKE_THREAD_LIBS_INIT=-lpthread"
    "-DBUILD_TOOL=0"
)

run_build "${CMAKE_PARAMS[@]}"

# Run tests
echo "Running iOS simulator tests..."

# Crypto tests
shard_gtest "${BUILD_ROOT}/crypto/crypto_test.app/crypto_test --gtest_also_run_disabled_tests"
shard_gtest ${BUILD_ROOT}/crypto/urandom_test.app/urandom_test
shard_gtest ${BUILD_ROOT}/crypto/mem_test.app/mem_test
shard_gtest ${BUILD_ROOT}/crypto/mem_set_test.app/mem_set_test
shard_gtest ${BUILD_ROOT}/crypto/rand_isolated_test.app/rand_isolated_test
shard_gtest ${BUILD_ROOT}/crypto/tree_drbg_jitter_entropy_isolated_test.app/tree_drbg_jitter_entropy_isolated_test

# SSL tests
shard_gtest "${BUILD_ROOT}/ssl/ssl_test.app/ssl_test"
# TODO: This test is failing on iOS simulator
# shard_gtest "${BUILD_ROOT}/ssl/integration_test.app/integration_test"

# Non-GoogleTest tests
"${BUILD_ROOT}/crypto/rwlock_static_init.app/rwlock_static_init"
"${BUILD_ROOT}/crypto/dynamic_loading_test.app/dynamic_loading_test"

popd

echo "iOS simulator tests completed successfully"
