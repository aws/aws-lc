#!/bin/bash -exu
#
# Copyright Amazon.com Inc. or its affiliates.  All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
#

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  |
#  - SRC_ROOT(aws-lc)
#  |
#  - SCRATCH_FOLDER
#    |
#    - tcpdump
#    - tcpdump-install
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SYS_ROOT}/"TCPDUMP_SCRATCH"
TCPDUMP_SRC_FOLDER="${SCRATCH_FOLDER}/tcpdump"
TCPDUMP_INSTALL_FOLDER="${SCRATCH_FOLDER}/tcpdump-install"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

mkdir -p "${SCRATCH_FOLDER}"
rm -rf "${SCRATCH_FOLDER:?}"/*

pushd "${SCRATCH_FOLDER}"

function tcpdump_build() {
  autoreconf -fi
  ./configure --prefix="${TCPDUMP_INSTALL_FOLDER}" --with-openssl="${AWS_LC_INSTALL_FOLDER}"
  make -j "${NUM_CPU_THREADS}"
}

function tcpdump_run_tests() {
  make check
  make releasecheck
}

# Get latest tcpdump version.
git clone https://github.com/the-tcpdump-group/tcpdump.git "${TCPDUMP_SRC_FOLDER}"
mkdir -p "${AWS_LC_BUILD_FOLDER}" "${AWS_LC_INSTALL_FOLDER}" "${TCPDUMP_INSTALL_FOLDER}"
ls

aws_lc_build "${SRC_ROOT}" "${AWS_LC_BUILD_FOLDER}" "${AWS_LC_INSTALL_FOLDER}"

pushd "${TCPDUMP_SRC_FOLDER}"
tcpdump_build
tcpdump_run_tests
popd

popd
