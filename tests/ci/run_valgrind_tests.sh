#!/bin/bash -xu
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

################################################################################
# set -e is disabled in this script because we need the script to continue
# even if |run_valgrind| returns an error.
#
# Assumes execution from root of AWS-LC folder.
################################################################################

source tests/ci/common_posix_setup.sh

SCRIPT_EXIT_STATUS=0

VALGRIND_COMMAND=valgrind
VALGRIND_ERROR_CODE=99

# crypto_test setup
# Suppression file produced by running:
# valgrind --gen-suppressions=yes ./test_build_dir/crypto/crypto_test
CRYPTO_TEST_EXE=test_build_dir/crypto/crypto_test
VALGRIND_SUPPRESSIONS_FILE_CRYPTO_TEST=tests/ci/valgrind_suppressions_crypto_test.supp

################################################################################
# Input:
#   1: Executable to be executed under Valgrind
#   2: Valgrind suppression file for $1
# Output:
#   0                       if Valgrind exists without any errors
#   ${VALGRIND_ERROR_CODE}  if Valgrind exists with errors
################################################################################
run_valgrind () {

    TEST_EXE=$1
    VALGRIND_SUPPRESSIONS_FILE=$2
    VALGRIND_ARGS=("--error-exitcode=${VALGRIND_ERROR_CODE}" "--track-origins=yes" "--leak-check=full" "--trace-children=yes" "--suppressions=${VALGRIND_SUPPRESSIONS_FILE}")

    echo "-----Test configuration start-----"
    echo "Test executable: ${TEST_EXE}"
    echo "Valgrind arguments: ${VALGRIND_ARGS}"
    echo "Valgrind suppressions:"
    cat ${VALGRIND_SUPPRESSIONS_FILE}
    echo "-----Test configuration end-----"

    ${VALGRIND_COMMAND} "${VALGRIND_ARGS[@]}" ${TEST_EXE}

    return $?
}

################################################################################
# Input:
#   1: Error code of previous run_valgrind execution
#   2: Executable that was executed under Valgrind
################################################################################
check_and_handle_error() {

    ERROR_CODE=$1
    TEST_EXE=$2

    if [[ ${ERROR_CODE} -eq ${VALGRIND_ERROR_CODE} ]]; then
        echo "TEST FAILED"
        echo "Executable that failed under Valgrind: ${TEST_EXE}"
        # Set exit status to error in CI
        SCRIPT_EXIT_STATUS=-1
    else
        echo "TEST SUCCEEDED"
        echo "Executable that succeeded under Valgrind: ${TEST_EXE}"
    fi
}

echo "Build AWS-LC in debug mode."
run_build

echo "Run AWS-LC crypto_test with Valgrind."
run_valgrind ${CRYPTO_TEST_EXE} ${VALGRIND_SUPPRESSIONS_FILE_CRYPTO_TEST}
check_and_handle_error $? ${CRYPTO_TEST_EXE}

exit ${SCRIPT_EXIT_STATUS}
