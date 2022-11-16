#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

install_dir="$(pwd)/../libcrypto_install_dir"
openssl_url='https://github.com/openssl/openssl.git'
openssl_1_1_branch='OpenSSL_1_1_1-stable'
openssl_1_0_branch='OpenSSL_1_0_2-stable'
# OpenSSL 3.0 branch still isn't stable yet, so we lock down
# a tag to prevent build failures that they introduced from
# failing our CI.
openssl_3_0_branch='openssl-3.0.5'

function build_aws_lc_fips {
  echo "building aws-lc in FIPS mode"
  run_build -DCMAKE_INSTALL_PREFIX="${install_dir}/aws-lc-fips" -DFIPS=1 -DCMAKE_BUILD_TYPE=Release
  pushd "$BUILD_ROOT"
  ninja install
  popd
}

function build_openssl_1_0 {
    echo "building OpenSSL 1.0"
    git clone --depth 1 --branch "${openssl_1_0_branch}" "${openssl_url}" "../openssl-1.0"
    pushd "../openssl-1.0"
    mkdir -p "${install_dir}/openssl-1.0"
    ./config --prefix="${install_dir}/openssl-1.0" --openssldir="${install_dir}/openssl-1.0"
    make "-j${NUM_CPU_THREADS}" > /dev/null
    make install_sw
    popd
    rm -rf "../openssl-1.0"
}

function build_openssl_1_1 {
    echo "building OpenSSL 1.1"
    git clone --depth 1 --branch "${openssl_1_1_branch}" "${openssl_url}" "../openssl-1.1"
    pushd "../openssl-1.1"
    mkdir -p "${install_dir}/openssl-1.1"
    ./config --prefix="${install_dir}/openssl-1.1" --openssldir="${install_dir}/openssl-1.1"
    make "-j${NUM_CPU_THREADS}" > /dev/null
    make install_sw
    popd
    rm -rf "../openssl-1.1"
}

function build_openssl_3_0 {
    echo "building OpenSSL 3.0"
    git clone --depth 1 --branch "${openssl_3_0_branch}" "${openssl_url}" "../openssl-3.0"
    pushd "../openssl-3.0"
    mkdir -p "${install_dir}/openssl-3.0"
    ./Configure --prefix="${install_dir}/openssl-3.0" --openssldir="${install_dir}/openssl-3.0"
    make "-j${NUM_CPU_THREADS}" > /dev/null
    make install_sw
    popd
    rm -rf "../openssl-3.0"
}

# We build each tool individually so we can have more insight into what is failing

# Building AWS-LC always builds bssl (which includes the speed tool) with the "local" libcrypto. We
# also support building speed.cc with an "external" aws-lc libcrypto (and openssl). This is useful
# when we want to compare the performance of a particular FIPS release against mainline if mainline
# has changes in speed.cc that could affect the comparison of the FIPS to non-FIPS, or if new
# algorithms have been added to speed.cc
build_aws_lc_fips
echo "Testing awslc_bm with AWS-LC FIPS"
run_build -DAWSLC_INSTALL_DIR="${install_dir}/aws-lc-fips"
"${BUILD_ROOT}/tool/awslc_bm"

build_openssl_1_0
echo "Testing ossl_bm with OpenSSL 1.0"
run_build -DOPENSSL_1_0_INSTALL_DIR="${install_dir}/openssl-1.0"
"${BUILD_ROOT}/tool/ossl_1_0_bm"

build_openssl_1_1
echo "Testing ossl_bm with OpenSSL 1.1"
run_build -DOPENSSL_1_1_INSTALL_DIR="${install_dir}/openssl-1.1"
"${BUILD_ROOT}/tool/ossl_1_1_bm"

build_openssl_3_0
echo "Testing ossl_bm with OpenSSL 3.0"
run_build -DOPENSSL_3_0_INSTALL_DIR="${install_dir}/openssl-3.0"
"${BUILD_ROOT}/tool/ossl_3_0_bm"
