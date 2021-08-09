#!/bin/bash
set -exo pipefail
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# Sourcing these files check for environment variables which may be unset so wait to enable -u
source tests/ci/common_fuzz.sh
# Running the build also checks for unset variables
run_build -DCMAKE_BUILD_TYPE=RelWithDebInfo -DFUZZ=1 -DASAN=1 -DBUILD_TESTING=OFF
# After loading everything any undefined variables should fail the build
set -u
# We want our CI to take about an hour:
# ~2 minutes to build AWS-LC
# ~50 minutes (3000 seconds) for all fuzzing
# ~2 minutes for merging files
# ~3 minutes for cleanup
TOTAL_FUZZ_TEST_TIME=3000
FUZZ_TEST_TIMEOUT=5

FUZZ_TESTS=$(find test_build_dir/fuzz -type f -executable)
NUM_FUZZ_TESTS=$(echo "$FUZZ_TESTS" | wc -l)
TIME_FOR_EACH_FUZZ=$((TOTAL_FUZZ_TEST_TIME/NUM_FUZZ_TESTS))

for FUZZ_TEST_PATH in $FUZZ_TESTS;do
  FUZZ_NAME=$(basename "$FUZZ_TEST_PATH")
  SRC_CORPUS="${SRC_ROOT}/fuzz/${FUZZ_NAME}_corpus"

  run_fuzz_test
done
