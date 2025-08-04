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
#    - libssh2
#    - LIBSSH2_BUILD_FOLDER
#    - LIBSSH2_INSTALL_FOLDER
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
SCRATCH_FOLDER=${SYS_ROOT}/"LIBSSH2_SCRATCH"
LIBSSH2_SRC_FOLDER="${SCRATCH_FOLDER}/libssh2"
LIBSSH2_BUILD_FOLDER="${SCRATCH_FOLDER}/libssh2-build"
LIBSSH2_INSTALL_FOLDER="${SCRATCH_FOLDER}/libssh2-install"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

mkdir -p "${SCRATCH_FOLDER}"
rm -rf "${SCRATCH_FOLDER:?}"/*

function libssh2_build() {
  cmake "${LIBSSH2_SRC_FOLDER}" -B "${LIBSSH2_BUILD_FOLDER}" -DCRYPTO_BACKEND=OpenSSL -DBUILD_TESTS=1 -DCMAKE_INSTALL_PREFIX="${LIBSSH2_INSTALL_FOLDER}" -DOPENSSL_ROOT_DIR="${AWS_LC_INSTALL_FOLDER}" -DENABLE_WERROR=ON -DENABLE_DEBUG_LOGGING=ON
  cmake --build "${LIBSSH2_BUILD_FOLDER}" --target install
  ${SCRATCH_FOLDER}/check-linkage.sh "${LIBSSH2_INSTALL_FOLDER}/lib/libssh2.so" crypto || exit 1
}

function libssh2_run_tests() {
  pushd "${LIBSSH2_BUILD_FOLDER}"
  ctest -VV --output-on-failure
  popd
}

pushd "${SCRATCH_FOLDER}"

# Get latest libssh2 version.
git clone https://github.com/libssh2/libssh2.git "${LIBSSH2_SRC_FOLDER}"
mkdir -p "${AWS_LC_BUILD_FOLDER}" "${AWS_LC_INSTALL_FOLDER}" "${LIBSSH2_BUILD_FOLDER}" "${LIBSSH2_INSTALL_FOLDER}"
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1
cp "${AWS_LC_BUILD_FOLDER}/check-linkage.sh" ${SCRATCH_FOLDER}/
aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=0
export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

libssh2_build
libssh2_run_tests

popd

