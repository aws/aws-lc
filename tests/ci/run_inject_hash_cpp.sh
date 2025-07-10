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
cmake -GNinja \
    -DCMAKE_BUILD_TYPE=RelWithDebInfo \
    -DFIPS=1 \
    -DFIPS_SHARED=1 \
    -DBUILD_SHARED_LIBS=1 \
    -DUSE_CPP_INJECT_HASH=ON \
    ..

# First try to build just inject_hash_cpp
echo "Building inject_hash_cpp..."
ninja inject_hash_cpp

# Test inject_hash_cpp basic functionality
echo "Testing inject_hash_cpp basic functionality..."
./util/fipstools/inject_hash_cpp/inject_hash_cpp --version || echo "Version check failed"
./util/fipstools/inject_hash_cpp/inject_hash_cpp --help || echo "Help check failed"

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
