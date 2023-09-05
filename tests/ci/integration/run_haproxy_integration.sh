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
  make CC="${CC}" -j ${NUM_CPU_THREADS} TARGET=generic USE_OPENSSL_AWSLC=1 SSL_INC="${AWS_LC_INSTALL_FOLDER}/include" \
      SSL_LIB="${AWS_LC_INSTALL_FOLDER}/lib/" USE_LUA=1  LUA_LIB_NAME=lua5.4

  make reg-tests VTEST_PROGRAM=../vtest/vtest REGTESTS_TYPES=default,bug,devel
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
