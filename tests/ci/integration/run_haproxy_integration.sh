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

function build_and_test_haproxy() {
  cd ${HAPROXY_SRC}

  make CC="${CC}" -j ${NUM_CPU_THREADS} TARGET=generic USE_OPENSSL=1 SSL_INC="${AWS_LC_INSTALL_FOLDER}/include" SSL_LIB="${AWS_LC_INSTALL_FOLDER}/lib/"
  ./scripts/build-vtest.sh
  export VTEST_PROGRAM=$(realpath ../vtest/vtest)

  # These tests pass when run local but are not supported in CodeBuild CryptoAlg-1965
  excluded_tests=("mcli_show_info.vtc" "mcli_start_progs.vtc" "tls_basic_sync.vtc" "tls_basic_sync_wo_stkt_backend.vtc" "acl_cli_spaces.vtc" "http_reuse_always.vtc")
  test_paths=""

  for test in reg-tests/**/*; do
      if [[ "$test" == *.vtc ]] && [[ ! " ${excluded_tests[*]} " =~ $(basename "$test") ]]; then
          test_paths+="$(realpath "$test") "
      fi
  done

  ./scripts/run-regtests.sh "$test_paths"
}

# Make script execution idempotent.
mkdir -p ${SCRATCH_FOLDER}
rm -rf ${SCRATCH_FOLDER}/*
cd ${SCRATCH_FOLDER}

mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
git clone --depth 1 https://github.com/haproxy/haproxy.git
ls

# Test with static AWS-LC libraries
aws_lc_build ${SRC_ROOT} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} -DBUILD_SHARED_LIBS=0
build_and_test_haproxy $HAPROXY_SRC

rm -rf "$AWS_LC_INSTALL_FOLDER/*"
rm -rf "$AWS_LC_BUILD_FOLDER/*"

# Test with shared AWS-LC libraries
aws_lc_build ${SRC_ROOT} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} -DBUILD_SHARED_LIBS=1
build_and_test_haproxy $HAPROXY_SRC