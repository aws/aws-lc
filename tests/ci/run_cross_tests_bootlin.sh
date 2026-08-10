#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Runs a cross-compile build-and-test pass against a Bootlin toolchain
# (https://toolchains.bootlin.com). Bootlin tarballs use a different
# directory layout than the aws-libcrypto S3 mirror consumed by
# run_cross_tests.sh, so this script is separate rather than reusing that one.
#
# Usage:
#   run_cross_tests_bootlin.sh <target-cpu>             \
#                              <toolchain-name>         \
#                              <toolchain-triple>       \
#                              <tarball-extension>      \
#                              <expected-sha256>        \
#                              <cmake-system-processor> \
#                              <cmake-args>...
#
# Bootlin switched archive format at some point: older stable releases are
# distributed as .tar.bz2, newer ones as .tar.xz. The extension is an
# explicit parameter so the workflow can pin to the exact archive that
# matches <expected-sha256>.
#
# Example (armv7 uclibc, pre-<sys/auxv.h>):
#   run_cross_tests_bootlin.sh armv7                                         \
#     armv7-eabihf--uclibc--stable-2022.08-1                                 \
#     arm-buildroot-linux-uclibcgnueabihf                                    \
#     tar.bz2                                                                \
#     9e4191ab996fdf5f4e8de7e4617c67cbf46127ca2754fca0ad45d60e393ace05       \
#     arm                                                                    \
#     "-DCMAKE_BUILD_TYPE=Release"

set -ex

TARGET_CPU="${1}"
TOOLCHAIN_NAME="${2}"
TOOLCHAIN_TRIPLE="${3}"
TARBALL_EXT="${4}"
EXPECTED_SHA256="${5}"
CMAKE_SYSTEM_PROCESSOR="${6}"
BUILD_OPTIONS=("${@:7}")

if [ "${#BUILD_OPTIONS[@]}" -lt 1 ]; then
    echo "Must pass build parameters"
    exit 1
fi

SCRIPT_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
SCRIPT_DIR="$(readlink -f "${SCRIPT_DIR}")"

source "${SCRIPT_DIR}/common_posix_setup.sh"
source "${SCRIPT_DIR}/gtest_util.sh"

# The Bootlin archive layout on disk looks like:
#   <TOOLCHAIN_NAME>/
#     bin/<TOOLCHAIN_TRIPLE>-gcc
#     bin/<TOOLCHAIN_TRIPLE>-g++
#     <TOOLCHAIN_TRIPLE>/sysroot/...
SCRATCH_FOLDER="${SYS_ROOT}/SCRATCH_${TARGET_CPU}_bootlin"

if [ -e "${SCRATCH_FOLDER}" ]; then
    # Some directories in the archive lack write permission, preventing deletion of files
    chmod +w -R "${SCRATCH_FOLDER}"
    rm -rf "${SCRATCH_FOLDER:?}"
fi
mkdir -p "${SCRATCH_FOLDER}"

pushd "${SCRATCH_FOLDER}"

# The URL path segment is the "family" (everything up to the first '--').
# For "armv7-eabihf--uclibc--stable-2025.08-1" this is "armv7-eabihf".
TOOLCHAIN_FAMILY="${TOOLCHAIN_NAME%%--*}"
TARBALL="${TOOLCHAIN_NAME}.${TARBALL_EXT}"
TARBALL_URL="https://toolchains.bootlin.com/downloads/releases/toolchains/${TOOLCHAIN_FAMILY}/tarballs/${TARBALL}"

wget -q "${TARBALL_URL}"
echo "${EXPECTED_SHA256}  ${TARBALL}" | sha256sum --check --strict
tar xf "${TARBALL}"

TOOLCHAIN_DIR="${SCRATCH_FOLDER}/${TOOLCHAIN_NAME}"
SYSROOT_DIR="${TOOLCHAIN_DIR}/${TOOLCHAIN_TRIPLE}/sysroot"

# Record whether the sysroot actually exposes <sys/auxv.h>. This is purely
# informational -- the detection logic in cpu_getauxval_linux.h handles both
# cases -- but surfacing it in CI logs makes it obvious which code path is
# being exercised (real libc getauxval vs. /proc/self/auxv fallback).
if [ -e "${SYSROOT_DIR}/usr/include/sys/auxv.h" ]; then
    echo "INFO: ${TOOLCHAIN_NAME} ships <sys/auxv.h>; natural detection will use libc getauxval."
else
    echo "INFO: ${TOOLCHAIN_NAME} does NOT ship <sys/auxv.h>; natural detection will use /proc/self/auxv fallback."
fi

cat <<EOF > ${TARGET_CPU}_bootlin.cmake
set(CMAKE_SYSTEM_NAME Linux)
set(CMAKE_SYSTEM_PROCESSOR ${CMAKE_SYSTEM_PROCESSOR})

set(CMAKE_C_COMPILER   ${TOOLCHAIN_DIR}/bin/${TOOLCHAIN_TRIPLE}-gcc)
set(CMAKE_CXX_COMPILER ${TOOLCHAIN_DIR}/bin/${TOOLCHAIN_TRIPLE}-g++)

set(CMAKE_SYSROOT ${SYSROOT_DIR})
set(CMAKE_SYSTEM_INCLUDE_PATH ${SYSROOT_DIR}/usr/include)

set(CMAKE_GENERATOR Ninja)
EOF

cat ${TARGET_CPU}_bootlin.cmake

# QEMU user-mode emulation needs the sysroot on its search path so it can
# find the target's dynamic linker and shared libraries at load time.
export QEMU_LD_PREFIX="${SYSROOT_DIR}"
export LD_LIBRARY_PATH="${SYSROOT_DIR}/lib"

echo "Testing AWS-LC for ${TARGET_CPU} against ${TOOLCHAIN_NAME}."

for BO in "${BUILD_OPTIONS[@]}"; do
  run_build -DCMAKE_TOOLCHAIN_FILE="${SCRATCH_FOLDER}/${TARGET_CPU}_bootlin.cmake" ${BO}

  shard_gtest "${BUILD_ROOT}/crypto/crypto_test"
  shard_gtest ${BUILD_ROOT}/crypto/urandom_test
  shard_gtest ${BUILD_ROOT}/crypto/mem_test
  shard_gtest ${BUILD_ROOT}/crypto/mem_set_test
  shard_gtest ${BUILD_ROOT}/crypto/rand_isolated_test
  shard_gtest ${BUILD_ROOT}/crypto/tree_drbg_jitter_entropy_isolated_test

  shard_gtest ${BUILD_ROOT}/ssl/ssl_test

  # Does not use GoogleTest
  ${BUILD_ROOT}/crypto/rwlock_static_init

  # Due to its special linkage, this does not use GoogleTest
  ${BUILD_ROOT}/crypto/dynamic_loading_test
done
popd
