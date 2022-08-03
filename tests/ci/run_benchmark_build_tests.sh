#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

install_dir="$(pwd)/../libcrypto_install_dir"
openssl_url='https://github.com/openssl/openssl.git'
openssl_1_1_branch='OpenSSL_1_1_1-stable'
openssl_1_0_branch='OpenSSL_1_0_2-stable'
openssl_3_0_branch='openssl-3.0'
# OpenSSL 3.0 branch still isn't stable yet, so we lock down
# a commit to prevent build failures that they introduced from
# failing our CI.
openssl_3_0_commit='2db226ce01be804fbd2d60b019c897305a8f091e'

function build_openssl_1_0 {
    echo "building OpenSSL 1.0"
    git clone --branch "${openssl_1_0_branch}" "${openssl_url}" "../openssl-1.0"
    pushd "../openssl-1.0"
    mkdir -p "${install_dir}/openssl-1.0"
    ./config --prefix="${install_dir}/openssl-1.0" --openssldir="${install_dir}/openssl-1.0"
    make "-j${NUM_CPU_THREADS}"
    make install
    popd
    rm -rf "../openssl-1.0"
}

function build_openssl_1_1 {
    echo "building OpenSSL 1.1"
    git clone --branch "${openssl_1_1_branch}" "${openssl_url}" "../openssl-1.1"
    pushd "../openssl-1.1"
    mkdir -p "${install_dir}/openssl-1.1"
    ./config --prefix="${install_dir}/openssl-1.1" --openssldir="${install_dir}/openssl-1.1"
    make "-j${NUM_CPU_THREADS}"
    make install
    popd
    rm -rf "../openssl-1.1"
}

function build_openssl_3_0 {
    echo "building OpenSSL 3.0"
    git clone --branch "${openssl_3_0_branch}" "${openssl_url}" "../openssl-3.0"
    pushd "../openssl-3.0"
    git checkout "${openssl_3_0_commit}"
    mkdir -p "${install_dir}/openssl-3.0"
    ./Configure --prefix="${install_dir}/openssl-3.0" --openssldir="${install_dir}/openssl-3.0"
    make "-j${NUM_CPU_THREADS}"
    make install
    popd
    rm -rf "../openssl-3.0"
}

# We build each tool individually so we can have more insight into what is failing
mkdir -p "${install_dir}"
echo "Testing awslc_bm"
mkdir -p "${install_dir}/aws_lc"
run_build -DAWSLC_INSTALL_DIR="${install_dir}/aws_lc"
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
