#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#    - SCRATCH_FOLDER
#      - sslproxy
#      - AWS_LC_BUILD_FOLDER
#      - AWS_LC_INSTALL_FOLDER
#      - SSLPROXY_BUILD_FOLDER
#      - libevent
#      - LIBEVENT_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SRC_ROOT}/SSLPROXY_BUILD_ROOT"
SSLPROXY_SRC_FOLDER="${SCRATCH_FOLDER}/sslproxy"
SSLPROXY_BUILD_FOLDER="${SCRATCH_FOLDER}/sslproxy-aws-lc"
SSLPROXY_PATCH_FOLDER="${SRC_ROOT}/tests/ci/integration/sslproxy_patch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"
LIBEVENT_SRC_FOLDER="${SCRATCH_FOLDER}/libevent"
LIBEVENT_INSTALL_FOLDER="${SCRATCH_FOLDER}/libevent-install"
EXPECTED_AWSLC_API_VERSION="22"

function libevent_install() {
  git clone https://github.com/libevent/libevent.git ${LIBEVENT_SRC_FOLDER} --depth 1
  pushd ${LIBEVENT_SRC_FOLDER}
  cmake -DOPENSSL_ROOT_DIR="${AWS_LC_INSTALL_FOLDER}" -DCMAKE_INSTALL_PREFIX="${LIBEVENT_INSTALL_FOLDER}"
  make -j "$NUM_CPU_THREADS" install
  popd
}

function sslproxy_build() {
  make -j "$NUM_CPU_THREADS" OPENSSL_BASE="${AWS_LC_INSTALL_FOLDER}" LIBEVENT_BASE="${LIBEVENT_INSTALL_FOLDER}"
}

# TODO: Remove this when we make an upstream contribution.
# There are some features in the sslproxy tests that we don't currently support.
# * prime192v1 curve
# * new session file to use in tests
function sslproxy_patch_tests() {
  # If the test file in SSLProxy needs to be updated, simply run the following code
  # against a valid SSL_SESSION from AWS-LC to generate a new file. This might occur
  # whenever we update the expected contents of SSL_SESSION.
  #
  # ```
  #  FILE *f;
  #  f = fopen("session-aws-lc.pem", "wr");
  #  PEM_write_SSL_SESSION(f, session.get());
  # ```
  for patchfile in $(find -L "${SSLPROXY_PATCH_FOLDER}" -type f -name '*.patch'); do
    echo "Apply patch $patchfile..."
    patch -p1 --quiet -i "$patchfile"
  done
}

# We run travisunittest because the CI workarounds are applicable to Codebuild as well.
function sslproxy_run_tests() {
  LD_LIBRARY_PATH="${LIBEVENT_INSTALL_FOLDER}/lib" make -j "$NUM_CPU_THREADS" OPENSSL=openssl OPENSSL_BASE="${AWS_LC_INSTALL_FOLDER}" LIBEVENT_BASE="${LIBEVENT_INSTALL_FOLDER}" travisunittest
}

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

git clone https://github.com/sonertari/SSLproxy.git ${SSLPROXY_SRC_FOLDER} --depth 1
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${SSLPROXY_BUILD_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=0

# libevent needs to be installed from source and linked to AWS-LC.
libevent_install

# Build sslproxy from source.
pushd ${SSLPROXY_SRC_FOLDER}
sslproxy_patch_tests
sslproxy_build
sslproxy_run_tests
popd

