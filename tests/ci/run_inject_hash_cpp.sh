#!/bin/bash
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
    -in-object nonexistent.so -o nonexistent.so
((ERRORS+=$?))

# Test 3: Actual library (should succeed)
if [[ "$OSTYPE" == "darwin"* ]]; then
    run_test "Valid library test (macOS)" false \
        ./util/fipstools/inject_hash_cpp/inject_hash_cpp \
        -o ./crypto/libcrypto.dylib \
        -in-object ./crypto/libcrypto.dylib \
        -apple
    ((ERRORS+=$?))
else
    run_test "Valid library test (Linux)" false \
        ./util/fipstools/inject_hash_cpp/inject_hash_cpp \
        -o ./crypto/libcrypto.so \
        -in-object ./crypto/libcrypto.so
    ((ERRORS+=$?))
fi

#Test 4: HMAC calvulation of a test file path (should succeed)
run_test "HMAC calculation test" false \
    ./util/fipstools/inject_hash_cpp/inject_hash_cpp \
    -in-object "util/fipstools/inject_hash_cpp/CMakeLists.txt" \
    -o "util/fipstools/inject_hash_cpp/CMakeLists.txt"
((ERRORS+=$?))

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

