#!/bin/bash -exu
#
# Copyright Amazon.com Inc. or its affiliates.  All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
#

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  |
#  - SRC_ROOT(aws-lc)
#  |
#  - SCRATCH_FOLDER
#    |
#    - tpm2_tss_patch
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER
#    - CURL_BUILD_FOLDER
#    - CURL_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
SCRATCH_FOLDER=${SYS_ROOT}/"TPM2_TSS_SCRATCH"
TPM2_TSS_SRC_FOLDER="${SCRATCH_FOLDER}/tpm2-tss"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"
CURL_SRC_FOLDER="${SCRATCH_FOLDER}/curl"
CURL_BUILD_FOLDER="${SCRATCH_FOLDER}/curl-build"
CURL_INSTALL_FOLDER="${SCRATCH_FOLDER}/curl-install"

mkdir -p "${SCRATCH_FOLDER}"
rm -rf "${SCRATCH_FOLDER:?}"/*

pushd "${SCRATCH_FOLDER}"

function curl_build() {
  cmake -DCMAKE_DEBUG_POSTFIX='' -DCMAKE_BUILD_TYPE=Debug -DCMAKE_PREFIX_PATH="${AWS_LC_INSTALL_FOLDER}" -DCMAKE_INSTALL_PREFIX="${CURL_INSTALL_FOLDER}" -B "${CURL_BUILD_FOLDER}" -S "${CURL_SRC_FOLDER}"
  cmake --build "${CURL_BUILD_FOLDER}" --target install -j "${NUM_CPU_THREADS}"
  ldd "${CURL_INSTALL_FOLDER}/lib/libcurl.so" | grep "${AWS_LC_INSTALL_FOLDER}/lib/libcrypto.so" || exit 1
  ldd "${CURL_INSTALL_FOLDER}/lib/libcurl.so" | grep "${AWS_LC_INSTALL_FOLDER}/lib/libssl.so" || exit 1
}

function tpm2_tss_build() {
  git apply "${SCRIPT_DIR}/tpm2_tss_patch/aws-lc-tpm2-tss.patch"
  export PKG_CONFIG_PATH="${AWS_LC_INSTALL_FOLDER}/lib/pkgconfig:${CURL_INSTALL_FOLDER}/lib/pkgconfig"
  /bin/sh ./bootstrap
  ./configure --enable-unit --with-crypto=ossl CFLAGS="-g -ggdb -O0 -I\"${AWS_LC_INSTALL_FOLDER}\"/include -I\"${CURL_INSTALL_FOLDER}\"/include -L\"${AWS_LC_INSTALL_FOLDER}\"/lib -L\"${CURL_INSTALL_FOLDER}\"/lib" LT_SYS_LIBRARY_PATH="${LD_LIBRARY_PATH}"
  make -j "${NUM_CPU_THREADS}" all VERBOSE=1
  make -j "${NUM_CPU_THREADS}" check VERBOSE=1
  ldd "${TPM2_TSS_SRC_FOLDER}/test/unit/.libs/fapi-get-web-cert" | grep "${AWS_LC_INSTALL_FOLDER}/lib/libcrypto.so" || exit 1
}

# Get latest curl and tpm2-tss
git clone https://github.com/curl/curl.git "${CURL_SRC_FOLDER}"
git clone https://github.com/tpm2-software/tpm2-tss.git "${TPM2_TSS_SRC_FOLDER}"
mkdir -p "${AWS_LC_BUILD_FOLDER}" "${AWS_LC_INSTALL_FOLDER}" "${CURL_BUILD_FOLDER}" "${CURL_INSTALL_FOLDER}"
ls

aws_lc_build "${SRC_ROOT}" "${AWS_LC_BUILD_FOLDER}" "${AWS_LC_INSTALL_FOLDER}" -DBUILD_TESTING=OFF -DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=RelWithDebInfo
export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-}:${AWS_LC_INSTALL_FOLDER}/lib/"

curl_build

export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-}:${CURL_INSTALL_FOLDER}/lib/"

pushd "${TPM2_TSS_SRC_FOLDER}"
tpm2_tss_build
popd

popd


