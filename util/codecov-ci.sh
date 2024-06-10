#!/usr/bin/env bash
#
# Copyright Amazon.com Inc. or its affiliates.  All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
#

set -xe

SRC=$(pwd)
SRC=$(readlink -f "$SRC")

# Sanity check
DIRNAME=$(basename -- "${SRC}")
if [[ "${DIRNAME}" != 'aws-lc' ]]; then
  echo "Script must be executed from aws-lc directory"
  exit 1
fi

BUILD="$1"
if [ -n "$BUILD" ]; then
  mkdir -p "${BUILD}"
  BUILD=$(readlink -f "$BUILD")
  BUILD_HTML=$(mkdir -vp "$BUILD/html")
else
  echo "Must specify a build directory."
  exit 1
fi

LCOV_PARAMS=()
LCOV_PARAMS+=(--exclude '*/third_party/*')
LCOV_PARAMS+=(--exclude '*/tool/*')
LCOV_PARAMS+=(--exclude '*_test.*')
LCOV_PARAMS+=(--exclude '*/test_*')
LCOV_PARAMS+=(--exclude '*_test_*')
LCOV_PARAMS+=(--exclude '*/gtest_*')
LCOV_PARAMS+=(--exclude '*/wycheproof_*')
if [[ "$(uname -s)" == "Darwin" ]]; then
  LCOV_PARAMS+=(--exclude '/Applications/*')
  LCOV_IGNORE_ERRORS="inconsistent,inconsistent,gcov,gcov,range,unused,unused"
  GENHTML_IGNORE_ERRORS="inconsistent,unmapped"
else
  LCOV_PARAMS+=(--exclude '/usr/*')
  LCOV_PARAMS+=(--exclude '/lib/*')
  if lcov --version | grep --silent 'LCOV version 1.'; then
    LCOV_IGNORE_ERRORS="gcov,source,graph"
  else
    LCOV_IGNORE_ERRORS="negative,mismatch,unused"
  fi
  GENHTML_IGNORE_ERRORS="inconsistent,unmapped"
fi
LCOV_PARAMS+=(--ignore-errors ${LCOV_IGNORE_ERRORS})

CMAKE_SETUP_PARAMS=(-DGCOV=1 -DDISABLE_PERL=1 -DBUILD_TESTING=1 -DBUILD_LIBSSL=1 -DCMAKE_BUILD_TYPE=Debug -S "${SRC}")

function generate_coverage() {
  mkdir -p "${BUILD}/${1}"
  BUILD_DIR="${BUILD}/${1}"

  # Build
  cmake ${2} ${CMAKE_SETUP_PARAMS} -B "${BUILD_DIR}"
  cmake --build "${BUILD_DIR}" --target all_tests --parallel

  # Collect initial coverage data
  lcov --capture "${LCOV_PARAMS[@]}" --initial --directory "${BUILD_DIR}" --output-file "${BUILD}/initial-${1}.info"

  # Run tests
  cmake --build "${BUILD_DIR}" --target run_tests

  # Collect coverage data and combine it with initial data
  lcov --capture "${LCOV_PARAMS[@]}" --directory "${BUILD_DIR}" --output-file "${BUILD}/test-${1}.info"
  lcov "${LCOV_PARAMS[@]}" --add-tracefile "${BUILD}/initial-${1}.info" --add-tracefile "${BUILD}/test-${1}.info" --output-file "${BUILD}/coverage-${1}.info"
}

# Default x86-64 build/test
generate_coverage "default" ""

# No Assembly x86-64 build/test
generate_coverage "no-asm" "-DOPENSSL_NO_ASM=1"

#genhtml --ignore-errors ${GENHTML_IGNORE_ERRORS} --output-directory "${BUILD_HTML}" "${BUILD}"/coverage-*.info
#open "${BUILD_HTML}"/index.html

