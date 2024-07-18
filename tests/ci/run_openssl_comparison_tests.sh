#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

source tests/ci/common_posix_setup.sh

scratch_folder=${SYS_ROOT}/"openssl-scratch"
install_dir="${scratch_folder}/libcrypto_install_dir"
openssl_url='https://github.com/openssl/openssl.git'
openssl_1_1_1_branch='OpenSSL_1_1_1-stable'
openssl_1_0_2_branch='OpenSSL_1_0_2-stable'
openssl_3_1_branch='openssl-3.1'
openssl_3_2_branch='openssl-3.2'
openssl_master_branch='master'

mkdir -p "${scratch_folder}"
rm -rf "${scratch_folder:?}"/*

function build_aws_lc_fips {
  echo "building aws-lc in FIPS mode"
  run_build \
      -DCMAKE_INSTALL_PREFIX="${install_dir}/aws-lc-fips" \
      -DENABLE_DILITHIUM=ON \
      -DCMAKE_BUILD_TYPE=RelWithDebInfo \
      -DBUILD_SHARED_LIBS=1 
  pushd "$BUILD_ROOT"
  ninja install
  popd
}

function build_openssl {
    branch=$1
    echo "building OpenSSL ${branch}"
    git clone --depth 1 --branch "${branch}" "${openssl_url}" "${scratch_folder}/openssl-${branch}"
    pushd "${scratch_folder}/openssl-${branch}"
    mkdir -p "${install_dir}/openssl-${branch}"
    ./config --prefix="${install_dir}/openssl-${branch}" --openssldir="${install_dir}/openssl-${branch}" -d
    make "-j${NUM_CPU_THREADS}" > /dev/null
    make install_sw
    popd
    rm -rf "${scratch_folder}/openssl-${branch}"
}

build_aws_lc_fips
build_openssl $openssl_1_0_2_branch
build_openssl $openssl_1_1_1_branch
build_openssl $openssl_3_1_branch
build_openssl $openssl_3_2_branch
build_openssl $openssl_master_branch

run_build -DCMAKE_BUILD_TYPE=RelWithDebInfo -DCMAKE_C_STANDARD=11 -DENABLE_DILITHIUM=ON"\

open102:${install_dir}/openssl-${openssl_1_0_2_branch};\
open111:${install_dir}/openssl-${openssl_1_1_1_branch};\
open31:${install_dir}/openssl-${openssl_3_1_branch};\
open32:${install_dir}/openssl-${openssl_3_2_branch};\
openmaster:${install_dir}/openssl-${openssl_master_branch};"


export AWSLC_TOOL_PATH="${BUILD_ROOT}/tool-openssl/openssl"
openssl_branches=($openssl_1_0_2_branch $openssl_1_1_1_branch $openssl_3_1_branch $openssl_3_2_branch $openssl_master_branch)

# Run X509 Comparison Tests against all OpenSSL branches
for branch in "${openssl_branches[@]}"; do
  export OPENSSL_TOOL_PATH="${install_dir}/openssl-${branch}/apps/openssl"
  echo "Running X509ComparisonTests against OpenSSL ${branch}"
  "${BUILD_ROOT}/tool_openssl/tool_openssl_test" --gtest_filter=X509ComparisonTest.*
done

