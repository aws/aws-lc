#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SRC_ROOT}/"scratch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"
LIBEVENT_SRC="${SCRATCH_FOLDER}/libevent"
export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"

function build_and_test_libevent() {
  pushd "${LIBEVENT_SRC}"
  mkdir build && pushd build
  cmake -GNinja -DOPENSSL_ROOT_DIR="${AWS_LC_INSTALL_FOLDER}" ../
  ninja verify
  popd && popd
}

# Make script execution idempotent.
mkdir -p "${SCRATCH_FOLDER}"
rm -rf "${SCRATCH_FOLDER:?}"/*
pushd "${SCRATCH_FOLDER}"

mkdir -p "${AWS_LC_BUILD_FOLDER}" "${AWS_LC_INSTALL_FOLDER}"
git clone --depth 1 https://github.com/libevent/libevent.git

# Test with shared AWS-LC libraries
aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1
export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:+$LD_LIBRARY_PATH:}${AWS_LC_INSTALL_FOLDER}/lib"
build_and_test_libevent

${AWS_LC_BUILD_FOLDER}/check-linkage.sh "${LIBEVENT_SRC}/build/lib/libevent_openssl.so" crypto || exit 1
popd
