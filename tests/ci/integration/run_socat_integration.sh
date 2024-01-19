#!/bin/bash -exu
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

# Set up environment.
# SRC_ROOT(aws-lc)
#  - SCRATCH_FOLDER
#    - SOCAT_SRC
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SRC_ROOT}/"scratch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"
SOCAT_SRC="${SCRATCH_FOLDER}/socat"

function build_and_test_socat() {
  pushd "$SOCAT_SRC"
  autoconf
  ./configure --enable-openssl-base="$AWS_LC_INSTALL_FOLDER"
  make -j "$NUM_CPU_THREADS"
  # test 146 OPENSSLLISTENDSA: fails because AWS-LC doesn't support FFDH ciphersuites which are needed for DSA
  # test 216 UDP6MULTICAST_UNIDIR: known flaky test in socat with newer kernels
  # test 309 OPENSSLRENEG1: AWS-LC doesn't support renegotiation by default, it can be enabled by calling SSL_set_renegotiate_mode
  # but that has caveats. See PORTING.md 'TLS renegotiation'
  # test 310 OPENSSLRENEG2: AWS-LC doesn't support renegotiation by default, it can be enabled by calling SSL_set_renegotiate_mode
  # but that has caveats. See PORTING.md 'TLS renegotiation'
  # test 492 ACCEPT_FD: uses systemd-socket-activate which doesn't inherit the LD_LIBRARY_PATH so socat can't find libcrypto.so
  ./test.sh --expect-fail 146,216,309,310,492
  popd
}

# Make script execution idempotent.
mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*

mkdir -p "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER"
git clone --depth 1 https://repo.or.cz/socat.git "$SOCAT_SRC"

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_SHARED_LIBS=1 -DBUILD_TESTING=0 -DCMAKE_BUILD_TYPE=RelWithDebInfo
export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib/:${LD_LIBRARY_PATH:-}"
build_and_test_socat

ldd "${SOCAT_SRC}/socat" | grep "${AWS_LC_INSTALL_FOLDER}/lib/libcrypto.so" || exit 1
