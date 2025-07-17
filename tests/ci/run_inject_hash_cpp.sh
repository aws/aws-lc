#!/bin/bash
set -exo pipefail

# Get directory containing this script
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd "${DIR}/../.."

# Print environment info
echo "Environment:"
go version
cmake --version
ninja --version

# Build AWS-LC with C++ inject_hash
mkdir -p build
cd build

# Configure
if [[ "$OSTYPE" == "darwin"* ]]; then
    cmake -GNinja \
        -DCMAKE_BUILD_TYPE=RelWithDebInfo \
        -DFIPS=1 \
        -DFIPS_SHARED=1 \
        -DBUILD_SHARED_LIBS=1 \
        -DUSE_CPP_INJECT_HASH=ON \
        -DCMAKE_OSX_SYSROOT=/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk \
        ..
else
    cmake -GNinja \
        -DCMAKE_BUILD_TYPE=RelWithDebInfo \
        -DFIPS=1 \
        -DFIPS_SHARED=1 \
        -DBUILD_SHARED_LIBS=1 \
        -DUSE_CPP_INJECT_HASH=ON \
        ..
fi

# First try to build just inject_hash_cpp
echo "Building inject_hash_cpp..."
ninja inject_hash_cpp

# Test 1: Check if executable runs
echo "Test 1: Basic execution"
if ./util/fipstools/inject_hash_cpp/inject_hash_cpp; then
    echo "Should have failed without arguments"
else
    echo "Correctly failed without arguments"
fi

# Test 2: Check -in-object parameter
echo "Test 2: Testing with test file"
touch test.bin
if ./util/fipstools/inject_hash_cpp/inject_hash_cpp -in-object test.bin; then
    echo "Successfully processed test file"
else
    echo "Failed to process test file"
fi

echo "=== Tests Complete ==="
# Build everything
echo "Building full project..."
ninja

# Test actual FIPS injection
echo "Testing FIPS injection..."
if [[ "$OSTYPE" == "darwin"* ]]; then
    ./util/fipstools/inject_hash_cpp/inject_hash_cpp -o ./crypto/libcrypto.dylib -in-object ./crypto/libcrypto.dylib -apple
else
    ./util/fipstools/inject_hash_cpp/inject_hash_cpp -o ./crypto/libcrypto.so -in-object ./crypto/libcrypto.so
fi

