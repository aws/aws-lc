# Copyright (c) 2022, Google Inc.
# SPDX-License-Identifier: ISC

# This script attempts to break each of the known KATs and checks that doing so
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

KATS=$(go run util/fipstools/break-kat.go --list-tests)

for kat in $KATS; do
  go run util/fipstools/break-kat.go $TEST_FIPS_BIN $kat > break-kat-bin
  chmod u+x ./break-kat-bin
  # Only capture stderr
  output=$(2>&1 ./break-kat-bin 2>&1 >/dev/null || true)
  if ! echo "$output" | egrep -q "^${kat}"; then
    echo "Failure for $kat did not mention that name in the output"
    exit 1
  fi
  rm ./break-kat-bin
done
echo "All tests broken as expected"

go run util/fipstools/break-hash.go $TEST_FIPS_BIN ./libcrypto.so
