#!/bin/bash
set -exo pipefail

# Get directory containing this script
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd "${DIR}/../.."

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
    -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
    ..

# Build
ninja

# Run basic functionality test
if ! ./util/fipstools/inject_hash_cpp/inject_hash_cpp --help; then
    echo "inject_hash_cpp failed to run"
    exit 1
fi

# Build and run crypto tests
ninja crypto_test
if ! ./crypto/crypto_test; then
    echo "crypto_test failed"
    exit 1
fi

# Verify FIPS integrity
if ! ./crypto/crypto_test | grep -q "FIPS integrity verification passed"; then
    echo "FIPS integrity verification failed"
    exit 1
fi

echo "All tests passed successfully!"