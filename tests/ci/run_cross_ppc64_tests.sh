#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

SCRIPT_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
SCRIPT_DIR="$(readlink -f "${SCRIPT_DIR}")"

source "${SCRIPT_DIR}/common_posix_setup.sh"
source "${SCRIPT_DIR}/gtest_util.sh"

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SYS_ROOT}/SCRATCH_PPC64"

if [ -e "${SCRATCH_FOLDER}" ]; then
    # Some directories in the archive lack write permission, preventing deletion of files
    chmod +w -R "${SCRATCH_FOLDER}"
    rm -rf "${SCRATCH_FOLDER}"
fi
mkdir -p "${SCRATCH_FOLDER}"

pushd "${SCRATCH_FOLDER}"

wget -q https://aws-libcrypto.s3.us-west-2.amazonaws.com/cross-compile-toolchains/host-x86_64-pc-linux-gnu/ppc64-x-tools.tar.xz
tar Jxf ppc64-x-tools.tar.xz --no-same-owner --no-same-permissions

cat <<EOF > ppc64.cmake
# Specify the target system
set(CMAKE_SYSTEM_NAME Linux)
set(CMAKE_SYSTEM_PROCESSOR ppc64)

# Specify the cross-compiler
set(CMAKE_C_COMPILER ${SCRATCH_FOLDER}/powerpc64-unknown-linux-gnu/bin/powerpc64-unknown-linux-gnu-gcc)
set(CMAKE_CXX_COMPILER ${SCRATCH_FOLDER}/powerpc64-unknown-linux-gnu/bin/powerpc64-unknown-linux-gnu-g++)

# Specify the sysroot for the target system
set(CMAKE_SYSROOT ${SCRATCH_FOLDER}/powerpc64-unknown-linux-gnu/powerpc64-unknown-linux-gnu/sysroot)
set(CMAKE_SYSTEM_INCLUDE_PATH ${SCRATCH_FOLDER}/powerpc64-unknown-linux-gnu/powerpc64-unknown-linux-gnu/sysroot/usr/include)

set(ENABLE_EXPERIMENTAL_BIG_ENDIAN_SUPPORT true)
set(CMAKE_GENERATOR Ninja)
EOF

export QEMU_LD_PREFIX="${SCRATCH_FOLDER}/powerpc64-unknown-linux-gnu/powerpc64-unknown-linux-gnu/sysroot"
export LD_LIBRARY_PATH="${SCRATCH_FOLDER}/powerpc64-unknown-linux-gnu/powerpc64-unknown-linux-gnu/sysroot/lib"

echo "Testing AWS-LC shared library for PPC64 big-endian."

BUILD_OPTIONS=()
BUILD_OPTIONS+=("-DCMAKE_BUILD_TYPE=Release")
BUILD_OPTIONS+=("-DCMAKE_BUILD_TYPE=Release -DFIPS=1 -DBUILD_SHARED_LIBS=1")

for BO in "${BUILD_OPTIONS[@]}"; do
  run_build -DCMAKE_TOOLCHAIN_FILE="${SCRATCH_FOLDER}/ppc64.cmake" ${BO}

  shard_gtest "${BUILD_ROOT}/crypto/crypto_test --gtest_also_run_disabled_tests"
  shard_gtest ${BUILD_ROOT}/crypto/urandom_test
  shard_gtest ${BUILD_ROOT}/crypto/mem_test
  shard_gtest ${BUILD_ROOT}/crypto/mem_set_test

  shard_gtest ${BUILD_ROOT}/ssl/ssl_test
  shard_gtest ${BUILD_ROOT}/ssl/integration_test

  # Due to its special linkage, this is now a Google Test
  ${BUILD_ROOT}/crypto/dynamic_loading_test
done
popd
