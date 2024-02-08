#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  |
#  - SRC_ROOT(aws-lc)
#  |
#  - SCRATCH_FOLDER
#    |
#    - curl
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER
#    - CURL_BUILD_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SYS_ROOT}/"CURL_BUILD_ROOT"
CURL_SRC_FOLDER="${SCRATCH_FOLDER}/curl"
CURL_BUILD_FOLDER="${SCRATCH_FOLDER}/curl/build"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${CURL_SRC_FOLDER}/aws-lc-install"

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

function curl_build() {
  autoreconf -fi
  ./configure --enable-warnings --enable-werror --with-openssl=${AWS_LC_INSTALL_FOLDER} --without-libpsl
  make -j "$NUM_CPU_THREADS"
  make -j "$NUM_CPU_THREADS" examples
}

function curl_run_tests() {
  make -j "$NUM_CPU_THREADS" tests
  make -j "$NUM_CPU_THREADS" test-ci
  cd ${SCRATCH_FOLDER}
}

# Get latest curl version.
git clone https://github.com/curl/curl.git ${CURL_SRC_FOLDER}
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${CURL_BUILD_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=0
cd ${CURL_SRC_FOLDER}
curl_build
curl_run_tests

