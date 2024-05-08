#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

TARGET_CPU="${1}"
TARGET_PLATFORM="${2}"
BUILD_OPTIONS=("${@:3:5}")
GCC_VERSION="10"
THREAD_MODEL="posix"

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

cat <<EOF > ${TARGET_CPU}-${TARGET_PLATFORM}.cmake
# Specify the target system
set(CMAKE_SYSTEM_NAME Windows)
set(CMAKE_SYSTEM_PROCESSOR ${TARGET_CPU})

# Specify the cross-compiler
set(CMAKE_C_COMPILER /usr/bin/${TARGET_CPU}-${TARGET_PLATFORM}-gcc-${THREAD_MODEL})
set(CMAKE_CXX_COMPILER /usr/bin/${TARGET_CPU}-${TARGET_PLATFORM}-g++-${THREAD_MODEL})

# Specify the sysroot for the target system
set(CMAKE_SYSROOT /usr/lib/gcc/${TARGET_CPU}-${TARGET_PLATFORM}/${GCC_VERSION}-${THREAD_MODEL}/)
set(CMAKE_SYSTEM_INCLUDE_PATH /usr/lib/gcc/${TARGET_CPU}-${TARGET_PLATFORM}/${GCC_VERSION}-${THREAD_MODEL}/include)

set(CMAKE_FIND_ROOT_PATH /usr/lib/gcc/${TARGET_CPU}-${TARGET_PLATFORM}/${GCC_VERSION}-${THREAD_MODEL}/)
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)

# Static to minimize runtime linking requirements
set(CMAKE_EXE_LINKER_FLAGS --static)

set(CMAKE_GENERATOR Ninja)
EOF

cat ${TARGET_CPU}-${TARGET_PLATFORM}.cmake

echo "Testing AWS-LC static library for ${TARGET_CPU}."

for BO in "${BUILD_OPTIONS[@]}"; do
  run_build -DCMAKE_TOOLCHAIN_FILE="${SCRATCH_FOLDER}/${TARGET_CPU}-${TARGET_PLATFORM}.cmake" ${BO}

  shard_gtest "${BUILD_ROOT}/crypto/crypto_test.exe --gtest_also_run_disabled_tests"
  shard_gtest ${BUILD_ROOT}/crypto/urandom_test.exe
  shard_gtest ${BUILD_ROOT}/crypto/mem_test.exe
  shard_gtest ${BUILD_ROOT}/crypto/mem_set_test.exe
  shard_gtest ${BUILD_ROOT}/crypto/rwlock_static_init.exe

  shard_gtest ${BUILD_ROOT}/ssl/ssl_test.exe
  shard_gtest ${BUILD_ROOT}/ssl/integration_test.exe

  # Due to its special linkage, this does not use GoogleTest
  ${BUILD_ROOT}/crypto/dynamic_loading_test.exe
done
popd
