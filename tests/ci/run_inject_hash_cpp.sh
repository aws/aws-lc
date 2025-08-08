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

# Test 3: Sanity check - verify tests pass with injected hash
run_test "Sanity check" false \
    ./crypto/crypto_test
((ERRORS+=$?))

# Test 4: Create corrupted library copy and invalid hash check
echo "Creating corrupted copy of library..."

# Create a separate test directory
mkdir -p ./test_corrupted
cp ./crypto/crypto_test ./test_corrupted/
cp ./crypto/libcrypto.${LIB_EXT} ./test_corrupted/libcrypto.${LIB_EXT}

if [[ "$OSTYPE" == "darwin"* ]]; then
    START_OFFSET=$(nm ./test_corrupted/libcrypto.${LIB_EXT} | grep _BORINGSSL_bcm_text_start | cut -d' ' -f1)
    END_OFFSET=$(nm ./test_corrupted/libcrypto.${LIB_EXT} | grep _BORINGSSL_bcm_text_end | cut -d' ' -f1)
else
    START_OFFSET=$(nm ./test_corrupted/libcrypto.${LIB_EXT} | grep BORINGSSL_bcm_text_start | cut -d' ' -f1)
    END_OFFSET=$(nm ./test_corrupted/libcrypto.${LIB_EXT} | grep BORINGSSL_bcm_text_end | cut -d' ' -f1)
fi

# Convert hex to decimal
START_OFFSET=$((16#$START_OFFSET))
END_OFFSET=$((16#$END_OFFSET))

# Pick a random offset within the module
RANDOM_OFFSET=$((START_OFFSET + RANDOM % (END_OFFSET - START_OFFSET)))
echo "Corrupting FIPS module at offset $RANDOM_OFFSET"

# Read current byte
CURRENT_BYTE=$(dd if=./test_corrupted/libcrypto.${LIB_EXT} bs=1 skip=$RANDOM_OFFSET count=1 2>/dev/null | xxd -p)

# Flip the bit (XOR with 1)
FLIPPED_BYTE=$(printf "%02x" "$((0x$CURRENT_BYTE ^ 1))")

# Write back the flipped byte
echo $FLIPPED_BYTE | xxd -r -p | dd of=./test_corrupted/libcrypto.${LIB_EXT} bs=1 seek=$RANDOM_OFFSET count=1 conv=notrunc

# Change to test directory and set library path
cd ./test_corrupted
export ${LIB_PATH_VAR}=./

# Run test and capture output
OUTPUT=$( ./crypto_test 2>&1 )
echo "Test output: $OUTPUT"

# Check specifically for integrity failure
run_test "Corrupted module verification test" true \
    bash -c 'echo "$OUTPUT" | grep -q "integrity" || echo "$OUTPUT" | grep -q "FIPS"'

cd ..
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
