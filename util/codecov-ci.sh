#!/usr/bin/env bash
#
# Copyright Amazon.com Inc. or its affiliates.  All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
#

set -xe

SRC=$(pwd)

# Sanity check
DIRNAME=$(basename -- "${SRC}")
if [[ "${DIRNAME}" != 'aws-lc' ]]; then
  echo "Script must be executed from aws-lc directory"
  exit 1
fi

BUILD="$1"
if [ -n "$BUILD" ]; then
  if [ ! -e "$BUILD" ]; then
    mkdir -p "$BUILD"
  fi
  BUILD=$(readlink -f "$BUILD")
else
  echo "Must specify a build directory."
  exit 1
fi

cmake -DGCOV=1 -DDISABLE_PERL=1 -DBUILD_TESTING=1 -DBUILD_LIBSSL=1 -DCMAKE_BUILD_TYPE=Debug -S "${SRC}" -B "${BUILD}"
cmake --build "${BUILD}" --target all_tests
cmake --build "${BUILD}" --target run_tests

#TODO: Use callgrind
#mkdir "$BUILD/callgrind/"
#go run "$SRC/util/all_tests.go" -build-dir "$BUILD" -callgrind -num-workers 16

shopt -s globstar

pushd "${BUILD}"
gcov --source-prefix "${SRC}" **/*.gcda
lcov --capture --exclude "/Applications/*" --exclude "/usr/*" --exclude "/lib/*" --directory . --output-file coverage.info
popd
