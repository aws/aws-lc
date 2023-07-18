#!/bin/bash -exu
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  |
#  - SRC_ROOT(aws-lc)
#  |
#  - SCRATCH_FOLDER
#    |
#    - HAPROXY_SRC
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SYS_ROOT}/"scratch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"
HAPROXY_SRC="${SCRATCH_FOLDER}/haproxy"
export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"

function build_and_test_haproxy() {
  cd ${HAPROXY_SRC}
  make CC="${CC}" -j ${NUM_CPU_THREADS} TARGET=generic USE_OPENSSL=1 SSL_INC="${AWS_LC_INSTALL_FOLDER}/include" \
      SSL_LIB="${AWS_LC_INSTALL_FOLDER}/lib/" USE_LUA=1  LUA_LIB_NAME=lua5.4

  # These tests are marked as SLOW and should be skipped.
  # TODO: update this to: make reg-tests VTEST_PROGRAM=../vtest/vtest REGTESTS_TYPES=default,bug,devel
  # ssl_dh.vtc expects to use libssl with a FFDH ciphersuite which is unsupported, it will be gracefully turned off in
  # ssl_dh.vtc with the change in https://github.com/andrewhop/haproxy/pull/1
  excluded_tests=("mcli_show_info.vtc" "mcli_start_progs.vtc" "tls_basic_sync.vtc" "tls_basic_sync_wo_stkt_backend.vtc" "acl_cli_spaces.vtc" "http_reuse_always.vtc" "ocsp_auto_update.vtc" "ssl_dh.vtc")
  test_paths=""

  for test in reg-tests/**/*; do
      if [[ "$test" == *.vtc ]] && [[ ! " ${excluded_tests[*]} " =~ $(basename "$test") ]]; then
          test_paths+="$(realpath "$test") "
      fi
  done

  make reg-tests VTEST_PROGRAM=../vtest/vtest REG_TEST_FILES="$test_paths"
}

# Make script execution idempotent.
mkdir -p ${SCRATCH_FOLDER}
rm -rf ${SCRATCH_FOLDER}/*
cd ${SCRATCH_FOLDER}

mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
git clone --depth 1 https://github.com/haproxy/haproxy.git
cd haproxy
./scripts/build-vtest.sh

# Test with static AWS-LC libraries
aws_lc_build ${SRC_ROOT} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} -DBUILD_SHARED_LIBS=0 -DBUILD_TESTING=0
build_and_test_haproxy $HAPROXY_SRC

rm -rf ${AWS_LC_INSTALL_FOLDER}/*
rm -rf ${AWS_LC_BUILD_FOLDER}/*

# Test with shared AWS-LC libraries
aws_lc_build ${SRC_ROOT} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} -DBUILD_SHARED_LIBS=1 -DBUILD_TESTING=0
build_and_test_haproxy $HAPROXY_SRC
