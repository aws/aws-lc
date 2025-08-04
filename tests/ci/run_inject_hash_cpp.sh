#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -xo pipefail

# Get directory containing this script
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd "${DIR}/../.."

# Source common setup
source tests/ci/common_posix_setup.sh


run_build \
    -DCMAKE_BUILD_TYPE=RelWithDebInfo \
    -DFIPS=1 \
    -DBUILD_SHARED_LIBS=1 \
    -DUSE_CPP_INJECT_HASH=ON 
    
cd "${BUILD_ROOT}"

# Function to run test and check result
run_test() {
    local test_name="$1"
    local expected_to_fail="$2"
    shift 2
    local command=("$@")
    
    echo "Running test: ${test_name}"
    if "${command[@]}"; then
        if [[ "${expected_to_fail}" == "true" ]]; then
            echo "Test '${test_name}' was expected to fail but succeeded"
            return 1
        else
            echo "Test '${test_name}' passed as expected"
            return 0
        fi
    else
        if [[ "${expected_to_fail}" == "true" ]]; then
            echo "Test '${test_name}' failed as expected"
            return 0
        else
            echo "Test '${test_name}' failed unexpectedly"
            return 1
        fi
    fi
}

#  error counter
ERRORS=0

echo "TESTING INJECT_HASH.CPP WITH EDGE CASES..." 

# Test 1: No arguments (should fail)
run_test "No arguments test" true \
    ./util/fipstools/inject_hash_cpp/inject_hash_cpp
((ERRORS+=$?))

# Test 2: Invalid file (should fail)
run_test "Invalid file test" true \
    ./util/fipstools/inject_hash_cpp/inject_hash_cpp \
    -in-object nonexistent.file -o nonexistent.file
((ERRORS+=$?))

# Platform Specific Tests
if [[ "$OSTYPE" == "darwin"* ]]; then
    echo "MacOS specific tests..."
    
    # Test 3: macOS without -apple flag (should fail)
    run_test "macOS missing apple flag test" true \
        ./util/fipstools/inject_hash_cpp/inject_hash_cpp \
        -o ./crypto/libcrypto.dylib \
        -in-object ./crypto/libcrypto.dylib
    ((ERRORS+=$?))

    # Test 4: Create corrupted library copy and invalid hash check
    echo "Creating corrupted copy of library..."
    cp ./crypto/libcrypto.dylib ./crypto/libcrypto_corrupted.dylib
    printf '\x00' | dd of=./crypto/libcrypto_corrupted.dylib bs=1 seek=1024 count=1 conv=notrunc
    export DYLD_LIBRARY_PATH="./crypto"
    run_test "Corrupted hash verification test" true \
        ./crypto/crypto_test
    unset DYLD_LIBRARY_PATH
    ((ERRORS+=$?))

else
    echo "Linux specific tests..."
    
    # Test 4: Linux with -apple flag (should fail)
    run_test "Linux with apple flag test" true \
        ./util/fipstools/inject_hash_cpp/inject_hash_cpp \
        -o ./crypto/libcrypto.so \
        -in-object ./crypto/libcrypto.so \
        -apple
    ((ERRORS+=$?))
    # Test 6: Create corrupted library copy and invalid hash check
    echo "Creating corrupted copy of library..."
    cp ./crypto/libcrypto.so ./crypto/libcrypto_corrupted.so
    printf '\x00' | dd of=./crypto/libcrypto_corrupted.so bs=1 seek=1024 count=1 conv=notrunc
    export LD_LIBRARY_PATH="./crypto_corrupted"
    run_test "Corrupted hash verification test" true \
        ./crypto/crypto_test
    unset LD_LIBRARY_PATH
    ((ERRORS+=$?))
fi

# Clean up
rm -f ./crypto/libcrypto_corrupted.* 2>/dev/null


# Print test summary
echo "=== Summary ==="
echo "Total errors: ${ERRORS}"

if [ ${ERRORS} -gt 0 ]; then
    echo "One or more tests failed"
    exit 1
else
    echo "All tests passed"
    exit 0
fi

