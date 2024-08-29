#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

source tests/ci/common_posix_setup.sh

scratch_folder=${SYS_ROOT}/"openssl-scratch"
install_dir="${scratch_folder}/libcrypto_install_dir"
openssl_url='https://github.com/openssl/openssl.git'
openssl_1_1_1_branch='OpenSSL_1_1_1-stable'
openssl_3_1_branch='openssl-3.1'
openssl_3_2_branch='openssl-3.2'
openssl_master_branch='master'

mkdir -p "${scratch_folder}"
rm -rf "${scratch_folder:?}"/*

build_openssl $openssl_1_1_1_branch
build_openssl $openssl_3_1_branch
build_openssl $openssl_3_2_branch
build_openssl $openssl_master_branch

run_build -DASAN=1

# OpenSSL 3.1.0 on switches from lib folder to lib64 folder
declare -A openssl_branches=(
  ["$openssl_1_1_1_branch"]="lib"
  ["$openssl_3_1_branch"]="lib64"
  ["$openssl_3_2_branch"]="lib64"
  ["$openssl_master_branch"]="lib64"
)

# Run X509 Comparison Tests against all OpenSSL branches
export AWSLC_TOOL_PATH="${BUILD_ROOT}/tool-openssl/openssl"
for branch in "${!openssl_branches[@]}"; do
  export OPENSSL_TOOL_PATH="${install_dir}/openssl-${branch}/bin/openssl"
  echo "Running ${test} against OpenSSL ${branch}"
  LD_LIBRARY_PATH="${install_dir}/openssl-${branch}/${openssl_branches[$branch]}" "${BUILD_ROOT}/tool-openssl/tool_openssl_test"
done

