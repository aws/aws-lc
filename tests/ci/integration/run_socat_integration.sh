#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

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
  # See: t/V1497389456.
  # socat decreased the test wait time to 3 milliseconds, which causes failures when additional warnings/logs are written.
  # Extending the wait time to 50 milliseconds is just right for us.
  # Use Perl so the command will fail if no replacement performed:
  perl -pi -e 'BEGIN{$x=0} $x=1 if s/MICROS=\${MILLIs}000/MICROS=50000/; END{exit 1 if !$x}' ./test.sh
  # test 146 OPENSSLLISTENDSA: fails because AWS-LC doesn't support FFDH ciphersuites which are needed for DSA
  # test 216 UDP6MULTICAST_UNIDIR: known flaky test in socat with newer kernels
  # test 309 OPENSSLRENEG1: AWS-LC doesn't support renegotiation by default, it can be enabled by calling SSL_set_renegotiate_mode
  # but that has caveats. See PORTING.md 'TLS renegotiation'
  # test 310 OPENSSLRENEG2: AWS-LC doesn't support renegotiation by default, it can be enabled by calling SSL_set_renegotiate_mode
  # but that has caveats. See PORTING.md 'TLS renegotiation'
  # test 399 OPENSSL_DTLS_CLIENT: Unknown issue running openssl s_server
  # test 467 EXEC_FDS: Something broken with exec'ing and not inheriting LD_LIBRARY_PATH
  # test 468 EXEC_SNIFF: Something broken with exec'ing and not inheriting LD_LIBRARY_PATH
  # test 478 SIGUSR1_STATISTICS: GHA does not support tty
  # test 492 ACCEPT_FD: uses systemd-socket-activate which doesn't inherit the LD_LIBRARY_PATH so socat can't find libcrypto.so
  # test 498 SHELL_SOCKETPAIR: GHA does not specify expected shell environment variables
  # test 499 SHELL_PIPES: GHA does not specify expected shell environment variables
  # test 500 SHELL_PTY: GHA does not specify expected shell environment variables
  # test 501 SHELL_SOCKETPAIR_FLUSH: GHA does not specify expected shell environment variables
  # test 502 SHELL_PIPES: GHA does not specify expected shell environment variables
  # test 503 SYSTEM_SIGINT: GHA does not specify expected shell environment variables
  # test 506 CHDIR_ON_SHELL: GHA does not specify expected shell environment variables
  # test 508 UMASK_ON_SYSTEM: GHA does not specify expected shell environment variables
  # test 528 PROCAN_CTTY: GHA does not support tty
  ./test.sh -d -v --expect-fail 146,216,309,310,399,467,468,478,492,498,499,500,501,502,503,506,508,528
  popd
}

# Make script execution idempotent.
mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*

mkdir -p "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER"
git clone --depth 1 https://repo.or.cz/socat.git "$SOCAT_SRC"

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_SHARED_LIBS=1 -DBUILD_TESTING=0 -DCMAKE_BUILD_TYPE=RelWithDebInfo
export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib/:${AWS_LC_INSTALL_FOLDER}/lib64/:${LD_LIBRARY_PATH:-}"
build_and_test_socat

ldd "${SOCAT_SRC}/socat" | grep "${AWS_LC_INSTALL_FOLDER}/lib/libcrypto.so" || exit 1
ldd "${SOCAT_SRC}/socat" | grep "${AWS_LC_INSTALL_FOLDER}/lib/libssl.so" || exit 1
