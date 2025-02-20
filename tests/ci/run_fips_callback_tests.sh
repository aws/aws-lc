#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
source tests/ci/common_posix_setup.sh

original_test="${BUILD_ROOT}/crypto/fips_callback_test"
broken_test="${BUILD_ROOT}/crypto/fips_callback_test_broken"

# By default, the integrity test should start up.
$original_test

# Break the tests
KATS=$(go run "${SRC_ROOT}/util/fipstools/break-kat.go" --list-tests)
for kat in $KATS; do
  go run "${SRC_ROOT}/util/fipstools/break-kat.go" "$original_test" "$kat" > "$broken_test"
  chmod +x "$broken_test"
  export FIPS_CALLBACK_TEST_EXPECTED_FAILURE="$kat"
  # When a callback is defined AWS-LC will not abort and the test should exit succesfully
  $broken_test --gtest_filter=FIPSCallback.PowerOnSelfTests
  unset FIPS_CALLBACK_TEST_EXPECTED_FAILURE
done


export FIPS_CALLBACK_TEST_EXPECTED_FAILURE="RSA_PWCT"
# Tell bcm which test to break
export BORINGSSL_FIPS_BREAK_TEST="RSA_PWCT"
$original_test --gtest_filter=FIPSCallback.RSARuntimeTest
