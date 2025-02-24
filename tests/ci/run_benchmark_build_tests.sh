#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

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
      -DBUILD_SHARED_LIBS=1 \
      -DBUILD_TESTING=OFF \
      -DENABLE_FIPS_ENTROPY_CPU_JITTER=1
  pushd "$BUILD_ROOT"
  ninja install
  popd
}

function build_aws_lc_branch {
    if [ $# -eq 0 ]; then
        echo "Branch not specified"
        exit 1
    fi
    branch="$1"
    echo "building the ${branch} branch of aws-lc in FIPS mode"
    git clone --depth 1 --branch $branch https://github.com/aws/aws-lc.git "${scratch_folder}/aws-lc-${branch}"
    pushd "${scratch_folder}/aws-lc-${branch}"
    cmake -GNinja \
        -DCMAKE_INSTALL_PREFIX="${install_dir}/aws-lc-${branch}" \
        -DFIPS=1 \
        -DENABLE_DILITHIUM=ON \
        -DCMAKE_BUILD_TYPE=RelWithDebInfo \
        -DBUILD_SHARED_LIBS=1
    ninja install
    popd
    rm -rf "${scratch_folder}/aws-lc-${branch}"
}

function build_boringssl {
  git clone --depth 1 https://github.com/google/boringssl.git "${scratch_folder}/boringssl"
  pushd "${scratch_folder}/boringssl"
  echo "install(TARGETS decrepit EXPORT OpenSSLTargets ${INSTALL_DESTINATION_DEFAULT})" >> CMakeLists.txt
  cmake -GNinja \
      -DCMAKE_INSTALL_PREFIX="${install_dir}/boringssl" \
      -DCMAKE_BUILD_TYPE=RelWithDebInfo .
  ninja install
  popd
  rm -rf "${scratch_folder}/boringssl"
}

# Building AWS-LC always builds bssl (which includes the speed tool) with the "local" libcrypto. We
# also support building speed.cc with an "external" aws-lc libcrypto (and openssl). This is useful
# when we want to compare the performance of a particular FIPS release against mainline if mainline
# has changes in speed.cc that could affect the comparison of the FIPS to non-FIPS, or if new
# algorithms have been added to speed.cc
build_aws_lc_fips
"${BUILD_ROOT}/tool/bssl" speed -timeout_ms 10 -chunks 1,2,16,256,20000

build_aws_lc_branch fips-2021-10-20
build_aws_lc_branch fips-2022-11-02
build_aws_lc_branch fips-2024-09-27
build_openssl_no_debug $openssl_1_0_2_branch
build_openssl_no_debug $openssl_1_1_1_branch
build_openssl_no_debug $openssl_3_1_branch
build_openssl_no_debug $openssl_3_2_branch
build_openssl_no_debug $openssl_master_branch
build_boringssl

run_build -DASAN=1 -DCMAKE_BUILD_TYPE=RelWithDebInfo -DCMAKE_CXX_STANDARD=17 -DCMAKE_C_STANDARD=11 -DENABLE_DILITHIUM=ON -DBENCHMARK_LIBS="\
aws-lc-fips-2021:${install_dir}/aws-lc-fips-2021-10-20;\
aws-lc-fips-2022:${install_dir}/aws-lc-fips-2022-11-02;\
aws-lc-fips-2024:${install_dir}/aws-lc-fips-2024-09-27;\
open102:${install_dir}/openssl-${openssl_1_0_2_branch};\
open111:${install_dir}/openssl-${openssl_1_1_1_branch};\
open31:${install_dir}/openssl-${openssl_3_1_branch};\
open32:${install_dir}/openssl-${openssl_3_2_branch};\
openmaster:${install_dir}/openssl-${openssl_master_branch};\
boringssl:${install_dir}/boringssl;"

LD_LIBRARY_PATH="${install_dir}/aws-lc-fips-2021-10-20/lib" "${BUILD_ROOT}/tool/aws-lc-fips-2021" -timeout_ms 10 -chunks 1,2,16,256,20000
LD_LIBRARY_PATH="${install_dir}/aws-lc-fips-2022-11-02/lib" "${BUILD_ROOT}/tool/aws-lc-fips-2022" -timeout_ms 10 -chunks 1,2,16,256,20000
LD_LIBRARY_PATH="${install_dir}/aws-lc-fips-2024-09-27/lib" "${BUILD_ROOT}/tool/aws-lc-fips-2022" -timeout_ms 10 -chunks 1,2,16,256,20000
LD_LIBRARY_PATH="${install_dir}/openssl-${openssl_1_0_2_branch}/lib" "${BUILD_ROOT}/tool/open102" -timeout_ms 10 -chunks 1,2,16,256,20000
LD_LIBRARY_PATH="${install_dir}/openssl-${openssl_1_1_1_branch}/lib" "${BUILD_ROOT}/tool/open111" -timeout_ms 10 -chunks 1,2,16,256,20000
LD_LIBRARY_PATH="${install_dir}/openssl-${openssl_3_1_branch}/lib64" "${BUILD_ROOT}/tool/open31" -timeout_ms 10 -chunks 1,2,16,256,20000
LD_LIBRARY_PATH="${install_dir}/openssl-${openssl_3_2_branch}/lib64" "${BUILD_ROOT}/tool/open32" -timeout_ms 10 -chunks 1,2,16,256,20000
LD_LIBRARY_PATH="${install_dir}/openssl-${openssl_master_branch}/lib64" "${BUILD_ROOT}/tool/openmaster" -timeout_ms 10 -chunks 1,2,16,256,20000
LD_LIBRARY_PATH="${install_dir}/boringssl" "${BUILD_ROOT}/tool/boringssl" -timeout_ms 10 -chunks 1,2,16,256,20000

echo "Testing ossl_bm with OpenSSL 1.0 with the legacy build option"
run_build -DOPENSSL_1_0_INSTALL_DIR="${install_dir}/openssl-${openssl_1_0_2_branch}" -DASAN=1 -DCMAKE_BUILD_TYPE=RelWithDebInfo
"${BUILD_ROOT}/tool/ossl_1_0_bm" -timeout_ms 10
