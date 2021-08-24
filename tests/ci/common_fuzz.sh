# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

if [ -v CODEBUILD_FUZZING_ROOT ]; then
  CORPUS_ROOT="${CODEBUILD_FUZZING_ROOT}/fuzzing"
else
  CORPUS_ROOT="${BUILD_ROOT}/mock_efs/fuzzing"
fi
echo "$CORPUS_ROOT"

if [ -v CODEBUILD_BUILD_ID ]; then
  BUILD_ID=$CODEBUILD_BUILD_ID
else
  # Generate a random string in bash https://unix.stackexchange.com/questions/230673/how-to-generate-a-random-string
  BUILD_ID=$(tr -dc A-Za-z0-9 </dev/urandom | head -c 13 ; echo '')
fi
echo "$BUILD_ID"

PLATFORM=$(uname -m)
DATE_NOW="$(date +%Y-%m-%d)"
FAILURE_ROOT="${CORPUS_ROOT}/runs/${DATE_NOW}/${BUILD_ID}"
ALL_RUN_ROOT="${BUILD_ROOT}/fuzz_run_root"
rm -rf "$ALL_RUN_ROOT"



function put_metric_count {
  put_metric --unit Count "$@"
}

function put_metric {
  # This call to publish the metric could fail but we don't want to fail the build +e turns off exit on error
  set +e
  aws cloudwatch put-metric-data \
    --namespace AWS-LC-Fuzz \
    "$@" || echo "Publishing metric failed, continuing with the rest of the build"
  # Turn it back on for the rest of the build
  set -e
}

function run_fuzz_test {
  SHARED_CORPUS="${CORPUS_ROOT}/shared_corpus/${FUZZ_NAME}/shared_corpus"
  FUZZ_TEST_ROOT="${ALL_RUN_ROOT}/${FUZZ_NAME}"
  FUZZ_TEST_CORPUS="${FUZZ_TEST_ROOT}/run_corpus"
  ARTIFACTS_FOLDER="${FUZZ_TEST_ROOT}/artifacts"
  FUZZ_RUN_LOGS="${FUZZ_TEST_ROOT}/logs"
  SUMMARY_LOG="${FUZZ_RUN_LOGS}/summary.log"
  mkdir -p "$SHARED_CORPUS" "$FUZZ_TEST_ROOT" "$FUZZ_TEST_CORPUS" "$ARTIFACTS_FOLDER" "$FUZZ_RUN_LOGS"


    # Calculate starting metrics and post to CloudWatch
  ORIGINAL_SHARED_CORPUS_FILE_COUNT=$(find "$SHARED_CORPUS" -type f | wc -l)
  put_metric_count --metric-name SharedCorpusFileCount --value "$ORIGINAL_SHARED_CORPUS_FILE_COUNT" --dimensions "FuzzTest=$FUZZ_NAME"

  # Perform the actual fuzzing!
  # Step 1 run each fuzz test for the determined time. This will use the existing shared corpus (in EFS) and any files
  # checked into the GitHub corpus. This runs the fuzzer with three folders: the first folder is where new inputs will
  # go (FUZZ_TEST_CORPUS), all other folders will be used as input (SHARED_CORPUS and SRC_CORPUS). It will write new
  # files to the temporary run corpus.
  # https://llvm.org/docs/LibFuzzer.html#options
  #
  # Run with NUM_CPU_THREADS which will be physical cores on ARM and virtualized cores on x86 with hyper threading.
  # Looking at the overall system fuzz rate running 1:1 with virtualized cores provides a noticeable speed up. This
  # is slightly different than libfuzzer's recommendation of #cores/2.
  # This could fail and we want to capture that (+e)
  set +e
  FUZZ_RUN_FAILURE=0
  time "./${FUZZ_TEST_PATH}" -print_final_stats=1 -timeout="$FUZZ_TEST_TIMEOUT" -max_total_time="$TIME_FOR_EACH_FUZZ" \
    -jobs="$NUM_CPU_THREADS" -workers="$NUM_CPU_THREADS" \
    -artifact_prefix="$ARTIFACTS_FOLDER/" \
    "$FUZZ_TEST_CORPUS" "$SHARED_CORPUS" "$SRC_CORPUS" 2>&1 | tee "$SUMMARY_LOG"
  # This gets the status of the fuzz run which determines if we want to fail the build or not, otherwise we'd get the results of tee
  if [ "${PIPESTATUS[0]}" == 1 ]; then
    FUZZ_RUN_FAILURE=1
  fi

  # The libfuzzer logs are written to the current working directory and need to be moved after the test is done
  mv ./*.log  "${FUZZ_RUN_LOGS}/."

  if [ "$FUZZ_RUN_FAILURE" == 1 ]; then
    FUZZ_TEST_FAILURE_ROOT="${FAILURE_ROOT}/${FUZZ_NAME}"
    mkdir -p "$FUZZ_TEST_FAILURE_ROOT"

    if [[ "$FUZZ_NAME" == "cryptofuzz" ]]; then
      for ARTIFACT in "$ARTIFACTS_FOLDER"/*; do
        ARTIFACT_NAME=$(basename "$ARTIFACT")
        "./${FUZZ_TEST_PATH}" --debug "$ARTIFACT" | tee "${FUZZ_RUN_LOGS}/${ARTIFACT_NAME}.log"
      done
    fi

    cp -r "$FUZZ_TEST_ROOT" "$FAILURE_ROOT"
    cp "$FUZZ_TEST_PATH" "${FUZZ_TEST_FAILURE_ROOT}/${FUZZ_NAME}"

    # If this fuzz run has failed the below metrics wont make a lot of sense, it could fail on the first input and publish a TestCount of 1 which makes all the metrics look weird
    echo "${FUZZ_NAME} failed, see the above output for details. For all the logs see ${FAILURE_ROOT} in EFS"
    exit 1
  else
    echo "Fuzz test ${FUZZ_NAME} finished successfully, not copying run logs and run corpus"
  fi

  set -e

  # Step 2 merge any new files from the run corpus and GitHub src corpus into the shared corpus (EFS)
  time "./${FUZZ_TEST_PATH}" -merge=1 "$SHARED_CORPUS" "$FUZZ_TEST_CORPUS" "$SRC_CORPUS"

  # Calculate interesting metrics and post results to CloudWatch
  FINAL_SHARED_CORPUS_FILE_COUNT=$(find "$SHARED_CORPUS" -type f | wc -l)
  put_metric_count --metric-name SharedCorpusFileCount --value "$FINAL_SHARED_CORPUS_FILE_COUNT" --dimensions "FuzzTest=$FUZZ_NAME"

  NEW_FUZZ_FILES=$(find "$FUZZ_TEST_CORPUS" -type f | wc -l)
  put_metric_count --metric-name RunCorpusFileCount --value "$NEW_FUZZ_FILES" --dimensions "FuzzTest=$FUZZ_NAME,Platform=$PLATFORM"

  TEST_COUNT=$(grep -o "stat::number_of_executed_units: [0-9]*" "$SUMMARY_LOG" | awk '{test_count += $2} END {print test_count}')
  put_metric_count --metric-name TestCount --value "$TEST_COUNT" --dimensions "FuzzTest=$FUZZ_NAME,Platform=$PLATFORM"

  TESTS_PER_SECOND=$((TEST_COUNT/TIME_FOR_EACH_FUZZ))
  put_metric --metric-name TestRate --value "$TESTS_PER_SECOND" --unit Count/Second --dimensions "FuzzTest=$FUZZ_NAME,Platform=$PLATFORM"

  FEATURE_COVERAGE=$(grep -o "ft: [0-9]*" "$SUMMARY_LOG" | awk '{print $2}' | sort -n | tail -1)
  put_metric_count --metric-name FeatureCoverage --value "$FEATURE_COVERAGE" --dimensions "FuzzTest=$FUZZ_NAME,Platform=$PLATFORM"

  BLOCK_COVERAGE=$(grep -o "cov: [0-9]*" "$SUMMARY_LOG" | awk '{print $2}' | sort -n | tail -1)
  put_metric_count --metric-name BlockCoverage --value "$BLOCK_COVERAGE" --dimensions "FuzzTest=$FUZZ_NAME,Platform=$PLATFORM"

  echo "${FUZZ_NAME} starting shared ${ORIGINAL_SHARED_CORPUS_FILE_COUNT} final shared ${FINAL_SHARED_CORPUS_FILE_COUNT} new files ${NEW_FUZZ_FILES} total test count ${TEST_COUNT} test rate ${TESTS_PER_SECOND} code coverage ${BLOCK_COVERAGE} feature coverage ${FEATURE_COVERAGE}"
}
