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

# Configure based on build type and OS
if [[ "$OSTYPE" == "darwin"* ]]; then
    # macOS only supports shared builds
    cmake -GNinja \
        -DCMAKE_BUILD_TYPE=RelWithDebInfo \
        -DFIPS=1 \
        -DFIPS_SHARED=1 \
        -DBUILD_SHARED_LIBS=1 \
        -DUSE_CPP_INJECT_HASH=ON \
        -DCMAKE_OSX_SYSROOT=/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk \
        ..
else
    # Linux supports both static and shared builds
    if [[ "${BUILD_TYPE}" == "static" ]]; then
        cmake -GNinja \
            -DCMAKE_BUILD_TYPE=RelWithDebInfo \
            -DFIPS=1 \
            -DFIPS_SHARED=0 \
            -DBUILD_SHARED_LIBS=0 \
            -DUSE_CPP_INJECT_HASH=ON \
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
fi

ninja 

# Test actual FIPS injection
# echo "Testing FIPS injection..."
# if [[ "$OSTYPE" == "darwin"* ]]; then
#     ./util/fipstools/inject_hash_cpp/inject_hash_cpp -o ./crypto/libcrypto.dylib -in-object ./crypto/libcrypto.dylib -apple
# else
#     if [[ "${BUILD_TYPE}" == "static" ]]; then
#         ./util/fipstools/inject_hash_cpp/inject_hash_cpp -o ./crypto/libcrypto.a -in-object ./crypto/libcrypto.a
#     else
#         ./util/fipstools/inject_hash_cpp/inject_hash_cpp -o ./crypto/libcrypto.so -in-object ./crypto/libcrypto.so
#     fi
# fi
