#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Optional first argument: the memcached git ref (tag or branch) to test
# against. Defaults to the default branch when unset so local runs keep
# working.
MEMCACHED_REF="${1:-}"

# Set up environment.

# SYS_ROOT
#  |
#  - SRC_ROOT(aws-lc)
#  |
#  - SCRATCH_FOLDER
#    |
#    - memcached
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SYS_ROOT}/"MEMCACHED_SCRATCH"
MEMCACHED_SRC_FOLDER="${SCRATCH_FOLDER}/memcached"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

function build_and_test_memcached() {
  pushd "${MEMCACHED_SRC_FOLDER}"
  ./autogen.sh
  # memcached locates an OpenSSL-compatible library via pkg-config first, and
  # falls back to --with-libssl=PATH. Set both so the build works regardless of
  # which path configure takes.
  PKG_CONFIG_PATH="${AWS_LC_INSTALL_FOLDER}/lib/pkgconfig" \
    ./configure --enable-tls --with-libssl="${AWS_LC_INSTALL_FOLDER}"
  make -j "${NUM_CPU_THREADS}"

  ${AWS_LC_BUILD_FOLDER}/check-linkage.sh "${MEMCACHED_SRC_FOLDER}/memcached" crypto || exit 1
  ${AWS_LC_BUILD_FOLDER}/check-linkage.sh "${MEMCACHED_SRC_FOLDER}/memcached" ssl || exit 1

  # SSL_TEST=1 routes the Perl test suite's connections over TLS instead of
  # plaintext TCP, so the memcached protocol tests exercise AWS-LC. The TLS
  # tests additionally need a modern IO::Socket::SSL on the client side (see
  # the OS dependencies in .github/workflows/integrations.yml): t/ssl_ports.t
  # needs TLS 1.3 support and t/ssl_session_resumption.t needs
  # get_session_reused().
  SSL_TEST=1 make test_basic_tls
  popd
}

# Make script execution idempotent.
mkdir -p "${SCRATCH_FOLDER}"
rm -rf "${SCRATCH_FOLDER:?}"/*

pushd "${SCRATCH_FOLDER}"

# Clone memcached. When MEMCACHED_REF is set (e.g. a release tag), check out
# that ref; otherwise track the default branch.
if [[ -n "${MEMCACHED_REF}" ]]; then
  git clone --depth 1 --branch "${MEMCACHED_REF}" https://github.com/memcached/memcached.git "${MEMCACHED_SRC_FOLDER}"
else
  git clone --depth 1 https://github.com/memcached/memcached.git "${MEMCACHED_SRC_FOLDER}"
fi

mkdir -p "${AWS_LC_BUILD_FOLDER}" "${AWS_LC_INSTALL_FOLDER}"

# Test with shared AWS-LC libraries
aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1
export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
build_and_test_memcached

popd
