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
  mkdir -p "$BUILD/default"
  mkdir -p "$BUILD/no_asm"
  mkdir -p "$BUILD/html"
  BUILD=$(readlink -f "$BUILD")
  BUILD_DEFAULT=$(readlink -f "$BUILD/default")
  BUILD_NO_ASM=$(readlink -f "$BUILD/no_asm")
  BUILD_HTML=$(readlink -f "$BUILD/html")
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
  LCOV_IGNORE_ERRORS="inconsistent,inconsistent,gcov,gcov"
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

# Default x86-64 build/test
cmake -DGCOV=1 -DDISABLE_PERL=1 -DBUILD_TESTING=1 -DBUILD_LIBSSL=1 -DCMAKE_BUILD_TYPE=Debug -S "${SRC}" -B "${BUILD_DEFAULT}"
cmake --build "${BUILD_DEFAULT}" --target all_tests
lcov --capture "${LCOV_PARAMS[@]}" --initial --directory "${BUILD_DEFAULT}" --output-file "${BUILD}/initial-default.info"
cmake --build "${BUILD_DEFAULT}" --target run_tests

# No Assembly x86-64 build/test
cmake -DGCOV=1 -DOPENSSL_NO_ASM=1 -DDISABLE_PERL=1 -DBUILD_TESTING=1 -DBUILD_LIBSSL=1 -DCMAKE_BUILD_TYPE=Debug -S "${SRC}" -B "${BUILD_NO_ASM}"
cmake --build "${BUILD_NO_ASM}" --target all_tests
lcov --capture "${LCOV_PARAMS[@]}" --initial --directory "${BUILD_NO_ASM}" --output-file "${BUILD}/initial-no-asm.info"
cmake --build "${BUILD_NO_ASM}" --target run_tests

lcov --capture "${LCOV_PARAMS[@]}" --directory "${BUILD_DEFAULT}" --output-file "${BUILD}/test-default.info"
lcov "${LCOV_PARAMS[@]}" --add-tracefile "${BUILD}/initial-default.info" --add-tracefile "${BUILD}/test-default.info" --output-file "${BUILD}/coverage-default.info"
lcov --capture "${LCOV_PARAMS[@]}" --directory "${BUILD_NO_ASM}" --output-file "${BUILD}/test-no-asm.info"
lcov "${LCOV_PARAMS[@]}" --add-tracefile "${BUILD}/initial-no-asm.info" --add-tracefile "${BUILD}/test-no-asm.info" --output-file "${BUILD}/coverage-no-asm.info"

#genhtml --ignore-errors ${GENHTML_IGNORE_ERRORS} --output-directory "${BUILD_HTML}" "${BUILD}"/coverage-*.info
#open "${BUILD_HTML}"/index.html

