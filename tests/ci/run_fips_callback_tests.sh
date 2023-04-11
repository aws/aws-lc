#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

# BORINGSSL_FIPS_BREAK_TESTS allows the BCM integrity hash check to fail without calling AWS_LC_FIPS_error
#run_build -DFIPS=1 -DCMAKE_C_FLAGS="-DBORINGSSL_FIPS_BREAK_TESTS"
cd "$BUILD_ROOT"
ninja

cd "$SRC_ROOT"
"${SRC_ROOT}/util/fipstools/test-break-kat.sh"

original_test="${BUILD_ROOT}/crypto/fips_callback_test"
broken_test="${BUILD_ROOT}/crypto/fips_callback_test_broken"

# Be default the integrity test should startup
module_status=$("${BUILD_ROOT}/tool/bssl" isfips)
[[ "1" == "${module_status}" ]] || { echo >&2 "FIPS Mode validation failed for default build."; exit 1; }
# Don't define FIPS_CALLBACK_TEST_POWER_ON_TEST_FAILURE because this is a working module even with the callback installed
$original_test

# Break the tests
KATS=$(go run "${SRC_ROOT}/util/fipstools/break-kat.go" --list-tests)
for kat in $KATS; do
  go run "${SRC_ROOT}/util/fipstools/break-kat.go" "$original_test" "$kat" > "$broken_test"
  chmod +x "$broken_test"
  export FIPS_CALLBACK_TEST_POWER_ON_TEST_FAILURE="$kat"
  $broken_test --gtest_filter=FIPSCallback.PowerOnTests
  unset FIPS_CALLBACK_TEST_POWER_ON_TEST_FAILURE
done
