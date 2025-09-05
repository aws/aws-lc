#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
set -exu

source tests/ci/common_posix_setup.sh

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SRC_ROOT}/"scratch"
ACCP_SRC="${SCRATCH_FOLDER}/amazon-corretto-crypto-provider"
FIPS=${FIPS:-"false"}

function build_and_test_accp() {
  pushd "${ACCP_SRC}"
  export JAVA_HOME=$(readlink -f /usr/bin/javac | sed "s:/bin/javac::")
  export PATH=$JAVA_HOME/bin:$PATH
  ./gradlew -DAWSLC_SRC_DIR="${SRC_ROOT}" -DAWSLC_GITVERSION="HEAD" -DFIPS="$FIPS" test
  popd
}

# Make script execution idempotent.
mkdir -p "${SCRATCH_FOLDER}"
rm -rf "${SCRATCH_FOLDER:?}"/*
pushd "${SCRATCH_FOLDER}"

git clone --depth 1 https://github.com/corretto/amazon-corretto-crypto-provider.git

build_and_test_accp

popd