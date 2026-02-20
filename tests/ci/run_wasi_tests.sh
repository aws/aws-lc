#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# CI script for testing AWS-LC WASI SDK builds
#
# This script builds AWS-LC for WebAssembly using the WASI SDK and runs the
# crypto_test, ssl_test, and urandom_test binaries using a WASI runtime.
#
# Prerequisites:
#   - WASI SDK must be installed (https://github.com/WebAssembly/wasi-sdk)
#   - WASI_SDK_PREFIX environment variable should point to WASI SDK root,
#     or the SDK should be installed at /opt/wasi-sdk
#   - CMake 3.5 or later
#   - Ninja (recommended) or Make
#   - A WASI runtime (wasmtime recommended) for running tests
#
# Environment Variables:
#   WASI_SDK_PREFIX - Path to the WASI SDK (defaults to /opt/wasi-sdk)
#   WASI_RUNTIME    - Path to WASI runtime executable (defaults to wasmtime)
#
# Note: WASI Preview 2 does not currently support pthreads. AWS-LC will be built
# in single-threaded mode. Socket APIs are also not available, so networking
# tests are excluded at compile time.

set -ex

source tests/ci/common_posix_setup.sh

# Find WASI SDK
if [ -n "$WASI_SDK_PREFIX" ]; then
    echo "Using WASI SDK from environment: $WASI_SDK_PREFIX"
elif [ -d "/opt/wasi-sdk" ]; then
    export WASI_SDK_PREFIX="/opt/wasi-sdk"
    echo "Using WASI SDK at default location: $WASI_SDK_PREFIX"
elif [ -d "$HOME/wasi-sdk" ]; then
    export WASI_SDK_PREFIX="$HOME/wasi-sdk"
    echo "Using WASI SDK at: $WASI_SDK_PREFIX"
else
    echo "WASI SDK not found. Please either:"
    echo "  1. Set WASI_SDK_PREFIX environment variable to your WASI SDK location"
    echo "  2. Install WASI SDK to /opt/wasi-sdk"
    echo "Download from: https://github.com/WebAssembly/wasi-sdk/releases"
    exit 1
fi

# Verify WASI SDK installation
if [ ! -f "$WASI_SDK_PREFIX/bin/clang" ]; then
    echo "ERROR: WASI SDK clang not found at: $WASI_SDK_PREFIX/bin/clang"
    exit 1
fi

echo "Using WASI SDK at: $WASI_SDK_PREFIX"
echo "WASI SDK clang version: $($WASI_SDK_PREFIX/bin/clang --version | head -n1)"

# Check for WASI runtime
WASI_RUNTIME="${WASI_RUNTIME:-wasmtime}"
if ! command -v "$WASI_RUNTIME" &> /dev/null; then
    echo "ERROR: WASI runtime ($WASI_RUNTIME) not found."
    echo "Please install wasmtime or another WASI runtime."
    echo "Download from: https://wasmtime.dev/"
    exit 1
fi

echo "Using WASI runtime: $WASI_RUNTIME"
$WASI_RUNTIME --version || true

# GoogleTest filter to exclude tests that require fork() or sockets (not supported in WASI)
# Threading tests are also excluded since WASI P2 doesn't support pthreads.
#
# Excluded tests:
# - *Socket*/*socket*: Require BSD sockets which WASI P2 doesn't support
# - *Fork*/*fork*: WASI doesn't support fork() for multiprocessing
# - ForkDetect.*: Fork detection tests require fork() syscall
# - *Thread*/*thread*: Threading tests require pthreads
# - BIOTest.CloseFlags: Requires dup() which WASI doesn't support
# - BIOTest.Gets: Requires temporary file creation in system temp directory
# - BIOTest.FileMode: Requires temporary file creation in system temp directory
# - SSLTest.EmptyClientCAList: Requires file I/O operations not available in WASI sandbox
WASI_GTEST_FILTER="-*Socket*:*socket*:*Fork*:*fork*:ForkDetect.*:*Thread*:*thread*:BIOTest.CloseFlags:BIOTest.Gets:BIOTest.FileMode:SSLTest.EmptyClientCAList"

# Function to build AWS-LC for WASI with testing enabled
function run_wasi_build {
    local build_type=$1
    shift
    local extra_args=("$@")

    echo "Building AWS-LC for WASI (${build_type}) with testing enabled..."

    rm -rf "${BUILD_ROOT:?}"
    mkdir -p "$BUILD_ROOT"
    cd "$BUILD_ROOT"

    ${CMAKE_COMMAND} \
        -GNinja \
        -DCMAKE_TOOLCHAIN_FILE="${SRC_ROOT}/util/wasi-sdk-toolchain.cmake" \
        -DCMAKE_BUILD_TYPE="${build_type}" \
        -DDISABLE_CPU_JITTER_ENTROPY=ON \
        -DDISABLE_GO=ON \
        -DDISABLE_PERL=ON \
        -DBUILD_TESTING=ON \
        -DBUILD_TOOL=OFF \
        "${extra_args[@]}" \
        "$SRC_ROOT"

    cmake --build . --parallel

    cd "$SRC_ROOT"
}

# Function to verify WASI build artifacts
function verify_wasi_artifacts {
    echo "Verifying WASI build artifacts..."

    # Check for libcrypto
    if [ ! -f "${BUILD_ROOT}/crypto/libcrypto.a" ]; then
        echo "ERROR: libcrypto.a not found"
        exit 1
    fi
    echo "Found: ${BUILD_ROOT}/crypto/libcrypto.a"

    # Check for libssl
    if [ ! -f "${BUILD_ROOT}/ssl/libssl.a" ]; then
        echo "ERROR: libssl.a not found"
        exit 1
    fi
    echo "Found: ${BUILD_ROOT}/ssl/libssl.a"

    # Check for test executables
    local test_binaries=(
        "crypto/crypto_test"
        "crypto/urandom_test"
        "ssl/ssl_test"
    )

    for test_binary in "${test_binaries[@]}"; do
        if [ ! -f "${BUILD_ROOT}/${test_binary}" ]; then
            echo "ERROR: ${test_binary} not found"
            exit 1
        fi
        echo "Found: ${BUILD_ROOT}/${test_binary}"
    done

    echo "Listing generated static libraries:"
    find "${BUILD_ROOT}" -name "*.a" -type f | while read -r lib; do
        echo "  $(basename "$lib"): $(du -h "$lib" | cut -f1)"
    done

    echo "WASI build artifacts verified successfully."
}

# Function to run a single WASI test using wasmtime
function run_single_wasi_test {
    local test_path=$1
    shift
    local test_args=("$@")
    local test_name
    test_name=$(basename "$test_path")

    echo ""
    echo "========================================"
    echo "Running ${test_name}..."
    echo "========================================"

    # Run WASI test via wasmtime
    # --dir=. grants access to current directory for any file operations
    if ! $WASI_RUNTIME --dir=. "${test_path}" -- "${test_args[@]}"; then
        echo "ERROR: ${test_name} failed"
        return 1
    fi

    echo "${test_name} passed"
    return 0
}

# Function to run WASI tests
function run_wasi_tests {
    echo "Running WASI tests using ${WASI_RUNTIME}..."
    echo "Threading: disabled (WASI P2 does not support pthreads)"
    echo "Sockets: disabled (WASI P2 does not support BSD sockets)"
    echo "Test filter: ${WASI_GTEST_FILTER}"

    cd "$BUILD_ROOT"

    local failed_tests=()

    # Run urandom_test (simpler test, good for basic verification)
    if ! run_single_wasi_test "crypto/urandom_test"; then
        failed_tests+=("urandom_test")
    fi

    # Run crypto_test (excluding fork, socket, and thread tests)
    if ! run_single_wasi_test "crypto/crypto_test" --gtest_filter="${WASI_GTEST_FILTER}"; then
        failed_tests+=("crypto_test")
    fi

    # Run ssl_test (excluding fork, socket, and thread tests)
    if ! run_single_wasi_test "ssl/ssl_test" --gtest_filter="${WASI_GTEST_FILTER}"; then
        failed_tests+=("ssl_test")
    fi

    cd "$SRC_ROOT"

    if [ ${#failed_tests[@]} -ne 0 ]; then
        echo ""
        echo "========================================"
        echo "FAILED TESTS: ${failed_tests[*]}"
        echo "========================================"
        exit 1
    fi

    echo ""
    echo "All WASI tests passed successfully!"
}

# Main execution

echo "========================================"
echo "AWS-LC WASI SDK Build & Test"
echo "========================================"
echo ""
echo "Testing AWS-LC WASI build in Release mode."
echo "Threading support: disabled (WASI P2 does not support pthreads)"
echo "Socket support: disabled (WASI P2 does not support BSD sockets)"
echo ""

# Run WASI build and tests in Release mode
run_wasi_build Release
verify_wasi_artifacts
run_wasi_tests

echo ""
echo "========================================"
echo "Build Summary"
echo "========================================"
echo "Build type: Release"
echo "Target: wasm32-wasip2"
echo "Libraries built:"
echo "  - libcrypto.a: $(du -h "${BUILD_ROOT}/crypto/libcrypto.a" | cut -f1)"
echo "  - libssl.a: $(du -h "${BUILD_ROOT}/ssl/libssl.a" | cut -f1)"
echo ""
echo "All WASI build and test runs completed successfully!"
