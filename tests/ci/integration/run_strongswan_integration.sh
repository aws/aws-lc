#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#    - SCRATCH_FOLDER
#      - AWS_LC_BUILD_FOLDER
#      - AWS_LC_INSTALL_FOLDER
#      - STRONGSWAN_SRC_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SRC_ROOT}/STRONGSWAN_BUILD_ROOT"
STRONGSWAN_SRC_FOLDER="${SCRATCH_FOLDER}/strongswan"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

function strongswan_build() {
  export CFLAGS="-I${AWS_LC_INSTALL_FOLDER}/include"
  export LDFLAGS="-L${AWS_LC_INSTALL_FOLDER}/lib"
  autoreconf -ivf
  # Mirror the configuration flags set by strongSwan's CI by taking all of the
  # flags specified within CONFIG when TEST is openssl-awslc in their test.sh.
  # https://github.com/strongswan/strongswan/blob/44e241fccc166211ccfdd322047c1213ff3ae73c/scripts/test.sh#L468
  ./configure --disable-defaults --enable-pki --enable-openssl --enable-pem \
  --disable-dependency-tracking --enable-silent-rules --enable-test-vectors \
  --enable-monolithic=no --enable-leak-detective=no --enable-asan --enable-drbg
  make -j ${NUM_CPU_THREADS}
  local openssl_plugin="${STRONGSWAN_SRC_FOLDER}/src/libstrongswan/plugins/openssl/.libs/libstrongswan-openssl.so"
  ${AWS_LC_BUILD_FOLDER}/check-linkage.sh "${openssl_plugin}" crypto || exit 1
}

function strongswan_run_tests() {
  make -j ${NUM_CPU_THREADS} check
}

mkdir -p ${SCRATCH_FOLDER}
rm -rf ${SCRATCH_FOLDER}/*
cd ${SCRATCH_FOLDER}

git clone --depth 1 https://github.com/strongswan/strongswan.git ${STRONGSWAN_SRC_FOLDER}

mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}

aws_lc_build ${SRC_ROOT} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} \
-DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DBUILD_SHARED_LIBS=1

export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"

pushd ${STRONGSWAN_SRC_FOLDER}
strongswan_build
strongswan_run_tests
popd
