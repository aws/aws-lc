#!/usr/bin/env bash
set -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
source tests/ci/common_posix_setup.sh

# This test file is designed to replicate the internal FIPS callback build defined in the build-glue package

# This should follow AWS-LC-Build-GLue/bin/fips_tests.sh maybe_run_fips_tests
function maybe_run_fips_tests() {
  expect_fips_mode=1
  module_status=$("${BUILD_ROOT}/tool/bssl" isfips)
  [[ "${expect_fips_mode}" == "${module_status}" ]] || {
    echo >&2 "FIPS Mode validation failed."
    exit 1
  }
  # Mainline AWS-LC does not have the CAVP tests anymore so only run the test_fips branch
  "${BUILD_ROOT}/util/fipstools/test_fips"
}

# This should follow AWS-LC-Build-GLue/bin/fips_tests.sh maybe_run_fips_break_tests
function maybe_run_fips_break_tests() {
  break_kat_executable="${BUILD_ROOT}/break-kat"
  pushd "${SRC_ROOT}"
  go build -o "$break_kat_executable" "./util/fipstools/break-kat.go"
  "$break_kat_executable" -list-tests

  working_bssl="${BUILD_ROOT}/tool/bssl"
    broken_bssl="${BUILD_ROOT}/tool/brokenbssl"
  "$working_bssl" isfips

  # This breaks a local copy of bssl that will not be included in the build artifacts
  "$break_kat_executable" "$working_bssl" DRBG >"$broken_bssl"
  chmod +x "$broken_bssl"
  if ! ("$broken_bssl" isfips 2>&1 >/dev/null || true) |
    grep -q "DRBG"; then
    echo "Broken bssl did not mention DRBG failure in startup"
    exit 1
  fi
  popd
}

function run_all_break_tests() {
  original_test="${BUILD_ROOT}/crypto/crypto_test"
  broken_test="${BUILD_ROOT}/crypto/crypto_test_broken"

  # By default the test should pass
  $original_test --gtest_filter=FIPSCallback.PowerOnSelfTests
  $original_test --gtest_filter=FIPSCallback.PWCT

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
      unset FIPS_CALLBACK_TEST_EXPECTED_FAILURE
      unset BORINGSSL_FIPS_BREAK_TEST
  done

}

echo "Testing AWS-LC static breakable build with custom callback and Jitter enabled"
build_and_test -DCMAKE_BUILD_TYPE=Release \
  -DBUILD_SHARED_LIBS=OFF \
  -DFIPS=1 \
  -DCMAKE_INSTALL_LIBDIR=lib \
  -DCMAKE_INSTALL_INCLUDEDIR=include \
  -DCMAKE_INSTALL_BINDIR=bin \
  -DCMAKE_C_FLAGS="-ggdb -DBORINGSSL_FIPS_BREAK_TESTS -DAWSLC_FIPS_FAILURE_CALLBACK" \
  -DCMAKE_CXX_FLAGS="-DAWSLC_FIPS_FAILURE_CALLBACK" \
  -DBUILD_TESTING=ON -DBUILD_LIBSSL=ON \
  -DENABLE_FIPS_ENTROPY_CPU_JITTER=1

maybe_run_fips_tests
maybe_run_fips_break_tests
run_all_break_tests

echo "Testing AWS-LC static build with custom callback and Jitter enabled"
build_and_test -DCMAKE_BUILD_TYPE=Release \
  -DBUILD_SHARED_LIBS=OFF \
  -DFIPS=1 \
  -DCMAKE_INSTALL_LIBDIR=lib \
  -DCMAKE_INSTALL_INCLUDEDIR=include \
  -DCMAKE_INSTALL_BINDIR=bin \
  -DCMAKE_C_FLAGS="-ggdb -DAWSLC_FIPS_FAILURE_CALLBACK" \
  -DCMAKE_CXX_FLAGS="-DAWSLC_FIPS_FAILURE_CALLBACK" \
  -DBUILD_TESTING=ON -DBUILD_LIBSSL=ON \
  -DENABLE_FIPS_ENTROPY_CPU_JITTER=1

maybe_run_fips_tests
# Can't run maybe_run_fips_break_tests or run_all_break_tests since they require BORINGSSL_FIPS_BREAK_TESTS
