#!/usr/bin/env bash
set -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
source tests/ci/common_posix_setup.sh

original_test="${BUILD_ROOT}/crypto/fips_callback_test"
broken_test="${BUILD_ROOT}/crypto/fips_callback_test_broken"

# By default the test should pass
$original_test

# Break the tests
KATS=$(go run "${SRC_ROOT}/util/fipstools/break-kat.go" --list-tests)
for kat in $KATS; do
  go run "${SRC_ROOT}/util/fipstools/break-kat.go" "$original_test" "$kat" > "$broken_test"
  chmod +x "$broken_test"
  export FIPS_CALLBACK_TEST_EXPECTED_FAILURE="$kat"
  # When a callback is defined AWS-LC will not abort and the test should exit successfully
  $broken_test --gtest_filter=FIPSCallback.PowerOnSelfTests
  unset FIPS_CALLBACK_TEST_EXPECTED_FAILURE
done

for TEST in RSA_PWCT ECDSA_PWCT EDDSA_PWCT MLKEM_PWCT MLDSA_PWCT; do
    export FIPS_CALLBACK_TEST_EXPECTED_FAILURE="${TEST}"
    export BORINGSSL_FIPS_BREAK_TEST="${TEST}"
    $original_test --gtest_filter=FIPSCallback.PWCT
done
