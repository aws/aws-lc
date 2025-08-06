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
    # Set platform-specific variables
    LIB_EXT="dylib"
    LIB_PATH_VAR="DYLD_LIBRARY_PATH"
else
    # Set platform-specific variables
    LIB_EXT="so"
    LIB_PATH_VAR="LD_LIBRARY_PATH"
fi

# Test 3: Create corrupted library copy and invalid hash check
echo "Creating corrupted copy of library..."

# Create a separate test directory
mkdir -p ./test_corrupted
cp ./crypto/crypto_test ./test_corrupted/
cp ./crypto/libcrypto.${LIB_EXT} ./test_corrupted/libcrypto.${LIB_EXT}

# Try to find the hash directly - the most reliable method
echo "Searching for integrity hash..."
HASH_PATTERN="ae2cea2abda6f3ec977f9bf6949afc836827cba0a09f6b6fde52cde2cdff3180"
HASH_OFFSET=$(hexdump -ve '1/1 "%.2x"' ./test_corrupted/libcrypto.${LIB_EXT} | grep -b -o "$HASH_PATTERN" | head -1 | cut -d':' -f1)

if [ -n "$HASH_OFFSET" ]; then
    # Convert hex string position to binary file position (divide by 2)
    OFFSET=$((HASH_OFFSET / 2))
    echo "Found integrity hash at offset $OFFSET, corrupting"
    # Corrupt one byte of the hash
    printf '\x00' | dd of=./test_corrupted/libcrypto.${LIB_EXT} bs=1 seek=$OFFSET count=1 conv=notrunc
else
    echo "WARNING: Could not find integrity hash pattern, trying multiple offsets"
    # Try multiple offsets to increase chance of hitting FIPS module
    for OFFSET in 1024 2048 4096 8192 16384; do
        echo "Corrupting at offset $OFFSET"
        printf '\x00' | dd of=./test_corrupted/libcrypto.${LIB_EXT} bs=1 seek=$OFFSET count=1 conv=notrunc
    done
fi

# Run test with the corrupted library
run_test "Corrupted hash verification test" true \
    bash -c "cd ./test_corrupted && ${LIB_PATH_VAR}=./ ./crypto_test 2>&1 | grep -q 'integrity'"
((ERRORS+=$?))

# Clean up
rm -rf ./test_corrupted

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
