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
  if [ ! -e "$BUILD" ]; then
    mkdir -p "$BUILD/default"
    mkdir -p "$BUILD/no_asm"
    mkdir -p "$BUILD/html"
  fi
  BUILD=$(readlink -f "$BUILD")
  BUILD_DEFAULT=$(readlink -f "$BUILD/default")
  BUILD_NO_ASM=$(readlink -f "$BUILD/no_asm")
  BUILD_HTML=$(readlink -f "$BUILD/html")
else
  echo "Must specify a build directory."
  exit 1
fi

# Default x86-64 build/test
cmake -DGCOV=1 -DDISABLE_PERL=1 -DBUILD_TESTING=1 -DBUILD_LIBSSL=1 -DCMAKE_BUILD_TYPE=Debug -S "${SRC}" -B "${BUILD_DEFAULT}"
cmake --build "${BUILD_DEFAULT}" --target all_tests
cmake --build "${BUILD_DEFAULT}" --target run_tests

# No Assembly x86-64 build/test
cmake -DGCOV=1 -DOPENSSL_NO_ASM=1 -DDISABLE_PERL=1 -DBUILD_TESTING=1 -DBUILD_LIBSSL=1 -DCMAKE_BUILD_TYPE=Debug -S "${SRC}" -B "${BUILD_NO_ASM}"
cmake --build "${BUILD_NO_ASM}" --target all_tests
cmake --build "${BUILD_NO_ASM}" --target run_tests

LCOV_EXCLUDE_PARAMS=()
LCOV_EXCLUDE_PARAMS+=(--exclude '*/third_party/*')
LCOV_EXCLUDE_PARAMS+=(--exclude '*/tool/*')
LCOV_EXCLUDE_PARAMS+=(--exclude '*_test.*')
LCOV_EXCLUDE_PARAMS+=(--exclude '*/test_*')
LCOV_EXCLUDE_PARAMS+=(--exclude '*_test_*')
LCOV_EXCLUDE_PARAMS+=(--exclude '*/gtest_*')
LCOV_EXCLUDE_PARAMS+=(--exclude '*/wycheproof_')

if [[ "$(uname -s)" == "Darwin" ]]; then
  LCOV_EXCLUDE_PARAMS+=(--exclude '/Applications/*')
  lcov --capture "${LCOV_EXCLUDE_PARAMS[@]}" --ignore-errors inconsistent,inconsistent,gcov,gcov --directory "${BUILD_DEFAULT}" --output-file "${BUILD}/coverage-default.info"
  lcov --capture "${LCOV_EXCLUDE_PARAMS[@]}" --ignore-errors inconsistent,inconsistent,gcov,gcov --directory "${BUILD_NO_ASM}" --output-file "${BUILD}/coverage-no-asm.info"

  #genhtml --ignore-errors inconsistent,inconsistent,unmapped --output-directory "${BUILD_HTML}" "${BUILD}"/coverage-*.info
  #open "${BUILD_HTML}"/index.html
else
  LCOV_EXCLUDE_PARAMS+=(--exclude '/usr/*')
  LCOV_EXCLUDE_PARAMS+=(--exclude '/lib/*')
  lcov --capture "${LCOV_EXCLUDE_PARAMS[@]}" --directory "${BUILD_DEFAULT}" --output-file "${BUILD}/coverage-default.info"
  lcov --capture "${LCOV_EXCLUDE_PARAMS[@]}" --directory "${BUILD_NO_ASM}" --output-file "${BUILD}/coverage-no-asm.info"
fi
