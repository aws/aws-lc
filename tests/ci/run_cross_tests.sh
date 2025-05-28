#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

TARGET_CPU="${1}"
TARGET_PLATFORM="${2}"
BUILD_OPTIONS=("${@:3:5}")

if [ "${#BUILD_OPTIONS[@]}" -lt 1 ]; then
    echo "Must pass build parameters"
    exit 1
fi

SCRIPT_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
SCRIPT_DIR="$(readlink -f "${SCRIPT_DIR}")"

source "${SCRIPT_DIR}/common_posix_setup.sh"
source "${SCRIPT_DIR}/gtest_util.sh"

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SYS_ROOT}/SCRATCH_${TARGET_CPU}"

if [ -e "${SCRATCH_FOLDER}" ]; then
    # Some directories in the archive lack write permission, preventing deletion of files
    chmod +w -R "${SCRATCH_FOLDER}"
    rm -rf "${SCRATCH_FOLDER:?}"
fi
mkdir -p "${SCRATCH_FOLDER}"

pushd "${SCRATCH_FOLDER}"

wget -q https://aws-libcrypto.s3.us-west-2.amazonaws.com/cross-compile-toolchains/host-x86_64-pc-linux-gnu/${TARGET_CPU}-x-tools.tar.xz
tar Jxf ${TARGET_CPU}-x-tools.tar.xz --no-same-owner --no-same-permissions

cat <<EOF > ${TARGET_CPU}.cmake
# Specify the target system
set(CMAKE_SYSTEM_NAME Linux)
# For "armv6" we need to strip off the "v6", so it's just "arm"
set(CMAKE_SYSTEM_PROCESSOR ${TARGET_CPU/v6/})

# Specify the cross-compiler
set(CMAKE_C_COMPILER ${SCRATCH_FOLDER}/${TARGET_PLATFORM}/bin/${TARGET_PLATFORM}-gcc)
set(CMAKE_CXX_COMPILER ${SCRATCH_FOLDER}/${TARGET_PLATFORM}/bin/${TARGET_PLATFORM}-g++)

# Specify the sysroot for the target system
set(CMAKE_SYSROOT ${SCRATCH_FOLDER}/${TARGET_PLATFORM}/${TARGET_PLATFORM}/sysroot)
set(CMAKE_SYSTEM_INCLUDE_PATH ${SCRATCH_FOLDER}/${TARGET_PLATFORM}/${TARGET_PLATFORM}/sysroot/usr/include)

set(CMAKE_GENERATOR Ninja)
EOF

cat ${TARGET_CPU}.cmake

export QEMU_LD_PREFIX="${SCRATCH_FOLDER}/${TARGET_PLATFORM}/${TARGET_PLATFORM}/sysroot"
export LD_LIBRARY_PATH="${SCRATCH_FOLDER}/${TARGET_PLATFORM}/${TARGET_PLATFORM}/sysroot/lib"

echo "Testing AWS-LC shared library for ${TARGET_CPU}."

for BO in "${BUILD_OPTIONS[@]}"; do
  run_build -DCMAKE_TOOLCHAIN_FILE="${SCRATCH_FOLDER}/${TARGET_CPU}.cmake" ${BO}

  shard_gtest "${BUILD_ROOT}/crypto/crypto_test"
  shard_gtest ${BUILD_ROOT}/crypto/urandom_test
  shard_gtest ${BUILD_ROOT}/crypto/mem_test
  shard_gtest ${BUILD_ROOT}/crypto/mem_set_test
  shard_gtest ${BUILD_ROOT}/crypto/rand_isolated_test
  shard_gtest ${BUILD_ROOT}/crypto/rwlock_static_init

  shard_gtest ${BUILD_ROOT}/ssl/ssl_test
  shard_gtest ${BUILD_ROOT}/ssl/integration_test

  # Due to its special linkage, this does not use GoogleTest
  ${BUILD_ROOT}/crypto/dynamic_loading_test
done
popd
