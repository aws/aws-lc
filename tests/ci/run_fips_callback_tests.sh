#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
source tests/ci/common_posix_setup.sh

run_build -DFIPS=1 -DCMAKE_C_FLAGS="-DBORINGSSL_FIPS_BREAK_TESTS"
cd "$SRC_ROOT"
#"${SRC_ROOT}/util/fipstools/test-break-kat.sh"

original_test="${BUILD_ROOT}/crypto/fips_callback_test"
broken_test="${BUILD_ROOT}/crypto/fips_callback_test_broken"

# By default, the integrity test should start up.
module_status=$("${BUILD_ROOT}/tool/bssl" isfips)
[[ "1" == "${module_status}" ]] || { echo >&2 "FIPS Mode validation failed for default build."; exit 1; }
# Don't define FIPS_CALLBACK_TEST_EXPECTED_FAILURE because this is a working module even with the callback installed
$original_test

# Break the tests
KATS=$(go run "${SRC_ROOT}/util/fipstools/break-kat.go" --list-tests)
for kat in $KATS; do
  go run "${SRC_ROOT}/util/fipstools/break-kat.go" "$original_test" "$kat" > "$broken_test"
  chmod +x "$broken_test"
  export FIPS_CALLBACK_TEST_EXPECTED_FAILURE="$kat"
  # AWS-LC will abort the the process so the test will always fail, but based on the output we can figure out if the
  # test failed as expected
  output=$(2>&1 $broken_test --gtest_filter=FIPSCallback.PowerOnSelfTests || true)
  if  [[ $output =~ "AWS-LC FIPS callback passed" && $output =~ $kat && ! $output =~ "PASSED" && ! $output =~ "FAILED" ]]; then
      echo "✅ Found both required strings and GTest aborted before passing or failing"
  else
      echo "❌ Test didn't mention the callback, kat, or it passed when it should have failed"
      exit 1
  fi

  unset FIPS_CALLBACK_TEST_EXPECTED_FAILURE
done

# Use the original test executable that doesn't have a broken self test
# Tell our test what test is expected to fail
export FIPS_CALLBACK_TEST_EXPECTED_FAILURE="RSA_PWCT"
# Tell bcm which test to break
export BORINGSSL_FIPS_BREAK_TEST="RSA_PWCT"
output=$(2>&1 $original_test --gtest_filter=FIPSCallback.RSARuntimeTest || true)
if  [[ $output =~ "AWS-LC FIPS callback passed" && ! $output =~ "PASSED" && ! $output =~ "FAILED" ]]; then
    echo "✅ Found callback success"
else
    echo "❌ Test didn't mention the callback test passing"
    exit 1
fi

# Tell our test what test is expected to fail
export FIPS_CALLBACK_TEST_EXPECTED_FAILURE="ECDSA_PWCT"
# Tell bcm which test to break
export BORINGSSL_FIPS_BREAK_TEST="ECDSA_PWCT"
output=$(2>&1 $original_test --gtest_filter=FIPSCallback.ECDSARuntimeTest || true)
if  [[ $output =~ "AWS-LC FIPS callback passed" && ! $output =~ "PASSED" && ! $output =~ "FAILED" ]]; then
    echo "✅ Found callback success"
else
    echo "❌ Test didn't mention the callback test passing"
    exit 1
fi
