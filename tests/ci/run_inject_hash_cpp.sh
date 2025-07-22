#!/bin/bash
set -exo pipefail

# Get directory containing this script
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd "${DIR}/../.."

# Source common setup
source tests/ci/common_posix_setup.sh

# Build AWS-LC with C++ inject_hash
if [[ "$OSTYPE" == "darwin"* ]]; then
    # macOS only supports shared builds
    run_build \
        -DCMAKE_BUILD_TYPE=RelWithDebInfo \
        -DFIPS=1 \
        -DFIPS_SHARED=1 \
        -DBUILD_SHARED_LIBS=1 \
        -DUSE_CPP_INJECT_HASH=ON \
        -DCMAKE_OSX_SYSROOT=/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk
else
    # Linux supports both static and shared builds
    # if [[ "${BUILD_TYPE}" == "static" ]]; then
    #     run_build \
    #         -DCMAKE_BUILD_TYPE=RelWithDebInfo \
    #         -DFIPS=1 \
    #         -DFIPS_SHARED=0 \
    #         -DBUILD_SHARED_LIBS=0 \
    #         -DUSE_CPP_INJECT_HASH=ON
    # else
    #skipping handling of static build for now
    run_build \
        -DCMAKE_BUILD_TYPE=RelWithDebInfo \
        -DFIPS=1 \
        -DFIPS_SHARED=1 \
        -DBUILD_SHARED_LIBS=1 \
        -DUSE_CPP_INJECT_HASH=ON
    # fi
fi

cd "${BUILD_ROOT}"

# Test actual FIPS injection
echo "TESTING INJECT_HASH.CPP WITH EDGE CASES..." 
./util/fipstools/inject_hash_cpp/inject_hash_cpp || echo "--Expected failure with no args--"

# Test with invalid file
./util/fipstools/inject_hash_cpp/inject_hash_cpp -in-object nonexistent.file -o nonexistent.file || echo "--Expected failure with invalid file--"

# Test with actual library
if [[ "$OSTYPE" == "darwin"* ]]; then
    ./util/fipstools/inject_hash_cpp/inject_hash_cpp \
        -o ./crypto/libcrypto.dylib \
        -in-object ./crypto/libcrypto.dylib \
        -apple
else
    ./util/fipstools/inject_hash_cpp/inject_hash_cpp \
        -o ./crypto/libcrypto.so \
        -in-object ./crypto/libcrypto.so
fi
