#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  |
#  - SRC_ROOT(aws-lc)
#  |
#  - SCRATCH_FOLDER
#    |
#    - libgit2
#    - LIBGIT2_BUILD_FOLDER
#    - LIBGIT2_INSTALL_FOLDER
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
SCRATCH_FOLDER=${SYS_ROOT}/"LIBGIT2_SCRATCH"
LIBGIT2_SRC_FOLDER="${SCRATCH_FOLDER}/libgit2"
LIBGIT2_BUILD_FOLDER="${SCRATCH_FOLDER}/libgit2-build"
LIBGIT2_INSTALL_FOLDER="${SCRATCH_FOLDER}/libgit2-install"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

mkdir -p "${SCRATCH_FOLDER}"
rm -rf "${SCRATCH_FOLDER:?}"/*

pushd "${SCRATCH_FOLDER}"

function libgit2_build_dynamic() {
  # No patch currently needed.
  # The CRYPT_OPENSSL_DYNAMIC is needed so that `const_DES_cblock` is defined.
  # See: https://github.com/libgit2/libgit2/blob/5158b0b70ade89268b22b7c388802b5f5b6debce/deps/ntlmclient/crypt_openssl.h#L22-L61
  cmake -B "${LIBGIT2_BUILD_FOLDER}" -DBUILD_SHARED_LIBS=ON -DBUILD_TESTS=1 -DCMAKE_INSTALL_PREFIX="${LIBGIT2_INSTALL_FOLDER}" -DOPENSSL_ROOT_DIR="${AWS_LC_INSTALL_FOLDER}" -DUSE_HTTPS=openssl -DUSE_SHA1=HTTPS -DUSE_SHA256=HTTPS -DCMAKE_C_STANDARD=99 -DCMAKE_C_FLAGS="-DCRYPT_OPENSSL_DYNAMIC=1"
  cmake --build "${LIBGIT2_BUILD_FOLDER}" --target install
  ldd "${LIBGIT2_INSTALL_FOLDER}/bin/git2" | grep "${AWS_LC_INSTALL_FOLDER}/lib" | grep "libcrypto.so" || exit 1
}

function libgit2_build_static() {
  # No patch currently needed.
  # The CRYPT_OPENSSL_DYNAMIC is needed so that `const_DES_cblock` is defined.
  # See: https://github.com/libgit2/libgit2/blob/5158b0b70ade89268b22b7c388802b5f5b6debce/deps/ntlmclient/crypt_openssl.h#L22-L61
  cmake -B "${LIBGIT2_BUILD_FOLDER}" -DBUILD_SHARED_LIBS=OFF -DLINK_WITH_STATIC_LIBRARIES=1 -DBUILD_TESTS=1 -DCMAKE_INSTALL_PREFIX="${LIBGIT2_INSTALL_FOLDER}" -DOPENSSL_ROOT_DIR="${AWS_LC_INSTALL_FOLDER}" -DUSE_HTTPS=openssl -DUSE_SHA1=HTTPS -DUSE_SHA256=HTTPS -DCMAKE_C_STANDARD=99 -DCMAKE_C_FLAGS="-DCRYPT_OPENSSL_DYNAMIC=1"
  cmake --build "${LIBGIT2_BUILD_FOLDER}" --target install
  nm --defined-only /home/justsmth/repos/LIBGIT2_SCRATCH/libgit2-install/bin/git2 | grep awslc_version_string || exit 1
}

function libgit2_run_tests() {
  ctest --extra-verbose
}

# Get latest libgit2 version.
git clone https://github.com/libgit2/libgit2.git "${LIBGIT2_SRC_FOLDER}"
mkdir -p "${AWS_LC_BUILD_FOLDER}" "${AWS_LC_INSTALL_FOLDER}" "${LIBGIT2_BUILD_FOLDER}" "${LIBGIT2_INSTALL_FOLDER}"
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1
aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=0
export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib/:${AWS_LC_INSTALL_FOLDER}/lib64/:${LD_LIBRARY_PATH:-}"

pushd "${LIBGIT2_SRC_FOLDER}"
libgit2_build_dynamic
popd

pushd "${LIBGIT2_BUILD_FOLDER}"
libgit2_run_tests
popd

rm -rf "${LIBGIT2_BUILD_FOLDER}"/* "${LIBGIT2_INSTALL_FOLDER}"/*

pushd "${LIBGIT2_SRC_FOLDER}"
libgit2_build_static
popd

pushd "${LIBGIT2_BUILD_FOLDER}"
libgit2_run_tests
popd

popd


