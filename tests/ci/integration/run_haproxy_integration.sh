#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Set up environment.

# SRC_ROOT(aws-lc)
#  - SCRATCH_FOLDER
#    - HAPROXY_SRC
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SRC_ROOT}/"scratch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"
HAPROXY_SRC="${SCRATCH_FOLDER}/haproxy"
export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"

function build_and_test_haproxy() {
  cd ${HAPROXY_SRC}
  make CC="${CC}" -j ${NUM_CPU_THREADS} TARGET=linux-glibc USE_OPENSSL_AWSLC=1 SSL_INC="${AWS_LC_INSTALL_FOLDER}/include" \
      SSL_LIB="${AWS_LC_INSTALL_FOLDER}/lib/"

  set +e
  make reg-tests VTEST_PROGRAM=../vtest/vtest REGTESTS_TYPES=default,bug,devel
  make_exit_status=$?
  set -e
  if [ $make_exit_status -ne 0 ]; then
      echo "Regression tests failed with ${make_exit_status}"
      for folder in /tmp/haregtests-*/vtc.*; do
        echo $folder
        cat $folder/INFO
        cat $folder/LOG
      done
      exit 1
    else
      echo "Regression tests passed"
    fi
}

# Make script execution idempotent.
mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
git clone --depth 1 https://github.com/haproxy/haproxy.git
cd haproxy
./scripts/build-vtest.sh

# Test with static AWS-LC libraries
aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=0
build_and_test_haproxy

rm -rf "${AWS_LC_INSTALL_FOLDER:?}"/*
rm -rf "${AWS_LC_BUILD_FOLDER:?}"/*

# Test with shared AWS-LC libraries
aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1
build_and_test_haproxy

${AWS_LC_BUILD_FOLDER}/check-linkage.sh "${HAPROXY_SRC}/haproxy" crypto || exit 1
