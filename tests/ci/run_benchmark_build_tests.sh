#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

scratch_folder=${SYS_ROOT}/"benchmark-scratch"
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
      -DFIPS=1 \
      -DENABLE_DILITHIUM=ON \
      -DCMAKE_BUILD_TYPE=RelWithDebInfo \
      -DBUILD_TESTING=OFF
  pushd "$BUILD_ROOT"
  ninja install
  popd
}

function build_aws_lc_fips_2022 {
    echo "building the fips-2022-11-02 branch of aws-lc in FIPS mode"
    git clone --depth 1 --branch fips-2022-11-02 https://github.com/aws/aws-lc.git "${scratch_folder}/aws-lc-fips-2022-11-02"
    pushd "${scratch_folder}/aws-lc-fips-2022-11-02"
    cmake -GNinja \
        -DCMAKE_INSTALL_PREFIX="${install_dir}/aws-lc-fips-2022-11-02" \
        -DFIPS=1 \
        -DENABLE_DILITHIUM=ON \
        -DCMAKE_BUILD_TYPE=RelWithDebInfo \
        -DBUILD_TESTING=OFF
    ninja install
    popd
    rm -rf "${scratch_folder}/aws-lc-fips-2022-11-02"
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

# Building AWS-LC always builds bssl (which includes the speed tool) with the "local" libcrypto. We
# also support building speed.cc with an "external" aws-lc libcrypto (and openssl). This is useful
# when we want to compare the performance of a particular FIPS release against mainline if mainline
# has changes in speed.cc that could affect the comparison of the FIPS to non-FIPS, or if new
# algorithms have been added to speed.cc
build_aws_lc_fips
"${BUILD_ROOT}/tool/bssl" speed -filter RNG

build_aws_lc_fips_2022
build_openssl $openssl_1_0_2_branch
build_openssl $openssl_1_1_1_branch
build_openssl $openssl_3_1_branch
build_openssl $openssl_3_2_branch
build_openssl $openssl_master_branch

run_build -DASAN=1 -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBENCHMARK_LIBS="\
aws-lc-fips:${install_dir}/aws-lc-fips-2022-11-02;\
open102:${install_dir}/openssl-${openssl_1_0_2_branch};\
open111:${install_dir}/openssl-${openssl_1_1_1_branch};\
open31:${install_dir}/openssl-${openssl_3_1_branch};\
open32:${install_dir}/openssl-${openssl_3_2_branch};\
openmaster:${install_dir}/openssl-${openssl_master_branch};"
"${BUILD_ROOT}/tool/aws-lc-fips" -filter RNG
"${BUILD_ROOT}/tool/open102" -filter RNG
"${BUILD_ROOT}/tool/open111" -filter RNG
"${BUILD_ROOT}/tool/open31" -filter RNG
"${BUILD_ROOT}/tool/open32" -filter RNG
"${BUILD_ROOT}/tool/openmaster" -filter RNG

echo "Testing ossl_bm with OpenSSL 1.0 with the legacy build option"
run_build -DOPENSSL_1_0_INSTALL_DIR="${install_dir}/openssl-${openssl_1_0_2_branch}" -DASAN=1 -DCMAKE_BUILD_TYPE=RelWithDebInfo
"${BUILD_ROOT}/tool/ossl_1_0_bm"
