#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Setup Xcode commands:
# > xcodebuild -runFirstLaunch
# > sudo xcodebuild -license accept
# > xcode-select --install
#
# Install iOS simulator commands:
# > xcodebuild -downloadPlatform iOS -exportPath ~/Download -buildVersion 17.0

set -ex

SCRIPT_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
SCRIPT_DIR="$(readlink -f "${SCRIPT_DIR}")"

source "${SCRIPT_DIR}/common_posix_setup.sh"
source "${SCRIPT_DIR}/gtest_util.sh"

SIM_IMAGE_LIST_PATH='/Library/Developer/CoreSimulator/Images/images.plist'
SIM_IMAGE_MOUNT_BASE='/Volumes'
SIM_IMAGE_PATTERN='iOS-17'

if [[ ! -r "${SIM_IMAGE_LIST_PATH}" ]]; then
  echo ERROR: Image list not found: "${SIM_IMAGE_LIST_PATH}"
  exit 1
fi

function plist_count_images() {
  plutil -extract 'images' raw  "${SIM_IMAGE_LIST_PATH}" -o -
}

function plist_image_id_for() {
  plutil -extract "images.${1}.runtimeInfo.bundleIdentifier" raw  "${SIM_IMAGE_LIST_PATH}" -o -
}

function plist_image_path_for() {
  plutil -extract "images.${1}.path.relative" raw  "${SIM_IMAGE_LIST_PATH}" -o - | sed -e 's/^file:\/\///'
}

function plist_image_build_for() {
  plutil -extract "images.${1}.runtimeInfo.build" raw  "${SIM_IMAGE_LIST_PATH}" -o -
}

function find_mount() {
  hdiutil info | grep -s "${1}"
}

function find_runtime_root() {
  find "${1}" -type d -name "RuntimeRoot" | head -n 1
}

IMAGE_LIST_SIZE=$(plist_count_images)
IMAGE_LIST_LAST_IDX=$(( "${IMAGE_LIST_SIZE}" - 1 ))
IMAGE_PATH=''
IMAGE_BUILD=''

for i in $(seq 0 "${IMAGE_LIST_LAST_IDX}"); do
  if [[ $(plist_image_id_for "${i}") == *"${SIM_IMAGE_PATTERN}"* ]]; then
    IMAGE_PATH=$(plist_image_path_for "${i}")
    IMAGE_BUILD=$(plist_image_build_for "${i}")
  fi
done

if [[ -z ${IMAGE_PATH} ]]; then
  echo ERROR: ${SIM_IMAGE_PATTERN} image not found.
  exit 1
fi

IMAGE_MOUNT_POINT="${SIM_IMAGE_MOUNT_BASE}/iOS_${IMAGE_BUILD}"

if ! find_mount "${IMAGE_MOUNT_POINT}"; then
  sudo hdiutil attach "${IMAGE_PATH}" -mountpoint "${IMAGE_MOUNT_POINT}"
fi

if ! find_mount "${IMAGE_MOUNT_POINT}"; then
  echo ERROR: Unable to mount runtime
  exit 1
fi

DYLD_ROOT_PATH=''
DYLD_ROOT_PATH=$(find_runtime_root "${IMAGE_MOUNT_POINT}")

if [[ -z "${DYLD_ROOT_PATH}" ]]; then
  echo ERROR: RuntimeRoot not found: "${IMAGE_MOUNT_POINT}"
  exit 1
fi

export DYLD_ROOT_PATH

pushd "${SRC_ROOT}"

CMAKE_PARAMS=("-DCMAKE_SYSTEM_NAME=iOS" "-DCMAKE_OSX_ARCHITECTURES=arm64" "-DCMAKE_SYSTEM_PROCESSOR=arm64"
  "-DCMAKE_OSX_SYSROOT=iphonesimulator" "-DCMAKE_THREAD_LIBS_INIT=-lpthread" "-DBUILD_TOOL=0")
run_build "${CMAKE_PARAMS[@]}"

shard_gtest "${BUILD_ROOT}/crypto/crypto_test.app/crypto_test --gtest_also_run_disabled_tests"
shard_gtest ${BUILD_ROOT}/crypto/urandom_test.app/urandom_test
shard_gtest ${BUILD_ROOT}/crypto/mem_test.app/mem_test
shard_gtest ${BUILD_ROOT}/crypto/mem_set_test.app/mem_set_test
shard_gtest ${BUILD_ROOT}/crypto/rwlock_static_init.app/rwlock_static_init

shard_gtest ${BUILD_ROOT}/ssl/ssl_test.app/ssl_test
# TODO: This test is failing on iOS simulator
#${BUILD_ROOT}/ssl/integration_test.app/integration_test

# Due to its special linkage, this does not use GoogleTest
${BUILD_ROOT}/crypto/dynamic_loading_test.app/dynamic_loading_test

popd



