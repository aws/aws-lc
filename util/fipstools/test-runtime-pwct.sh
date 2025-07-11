# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# This script attempts to break each of the key generation pair wise consistency tests and checks that doing so
# seems to work and at least mentions the correct KAT in the output.

set -x
set -e

TEST_FIPS_BIN="test_build_dir/util/fipstools/test_fips"

if [ ! -f $TEST_FIPS_BIN ]; then
  echo "$TEST_FIPS_BIN is missing. Run this script from the top level of a"
  echo "BoringSSL checkout and ensure that ./build-fips-break-test-binaries.sh"
  echo "has been run first."
  exit 1
fi

check_test_output() {
  local test_name="$1"
  local output="$2"
  case "$test_name" in
    "EC_PWCT")  expected="EC keygen checks failed" ;;
    "RSA_PWCT")    expected="RSA keygen checks failed" ;;
    "MLKEM_PWCT")  expected="ML-KEM keygen PCT failed" ;;
    "MLDSA_PWCT")  expected="ML-DSA keygen PCT failed" ;;
    "EDDSA_PWCT")  expected="Ed25519 keygen PCT failed" ;;
    *)             echo "Unknown test: $test_name"; return 1 ;;
  esac

  if ! echo "$output" | grep -q "$expected"; then
    echo "Failure for ${test_name} did not contain expected message: '${expected}'"
    echo "Actual output was: '${output}'"
    return 1
  fi
  return 0
}

for runtime_test in EC_PWCT RSA_PWCT EDDSA_PWCT MLKEM_PWCT MLDSA_PWCT; do
  output=$(2>&1 BORINGSSL_FIPS_BREAK_TEST=$runtime_test $TEST_FIPS_BIN 2>&1 >/dev/null || true)
  echo $output
  if ! check_test_output "$runtime_test" "$output"; then
    exit 1
  fi
done

echo "All tests broken as expected"

