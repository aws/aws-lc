#!/bin/bash
set -exo pipefail
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# Sourcing these files check for environment variables which may be unset so wait to enable -u
source tests/ci/common_fuzz.sh
source "${FUZZ_ROOT}/fuzz_env.sh"
# After loading everything any undefined variables should fail the build
set -u

rm -rf "$BUILD_ROOT"
mkdir -p "$BUILD_ROOT"
cd "$BUILD_ROOT"

# Build AWS-LC based on https://github.com/guidovranken/cryptofuzz/blob/master/docs/openssl.md
cmake -DCMAKE_CXX_FLAGS="$CXXFLAGS" -DCMAKE_C_FLAGS="$CFLAGS" -DBORINGSSL_ALLOW_CXX_RUNTIME=1 \
  -GNinja -DBUILD_TESTING=OFF -DBUILD_LIBSSL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo ../
ninja
cd ../
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_BORINGSSL"
export OPENSSL_INCLUDE_PATH=`realpath include/`
export OPENSSL_LIBCRYPTO_A_PATH=`realpath ${BUILD_ROOT}/crypto/libcrypto.a`

# Build the common OpenSSL module with AWS-LC
cd "${CRYPTOFUZZ_SRC}/modules/openssl"
make "-j${NUM_CPU_THREADS}"

export CFLAGS="${CFLAGS} -I $OPENSSL_INCLUDE_PATH"
export CXXFLAGS="${CXXFLAGS} -I $OPENSSL_INCLUDE_PATH"
export LIBFUZZER_LINK="-fsanitize=fuzzer"

# Build the overall cryptofuzz binary
cd "$CRYPTOFUZZ_SRC"
make "-j${NUM_CPU_THREADS}" cryptofuzz

# Common AWS-LC fuzzing setup, the cryptofuzz binary is in this folder so FUZZ_TEST_PATH=FUZZ_NAME
FUZZ_NAME="cryptofuzz"
FUZZ_TEST_PATH="${CRYPTOFUZZ_SRC}/${FUZZ_NAME}"
SRC_CORPUS="$CRYPTOFUZZ_SEED_CORPUS"

# Perform the actual fuzzing. We want the total build time to be about an 45 minutes:
# 5 minutes for building AWS-LC and Cryptofuzz
# 30 minutes (1800 seconds) of fuzzing
# 10 minutes of cleanup and merging in new inputs
TIME_FOR_EACH_FUZZ=1800

# Some fuzz tests can take a while but still pass. This is a tradeoff: less false positive noise, but some inputs that take
# a long time could lead to a denial of service avenue. We're mostly interested in correctness and memory safety at this
# time so we're willing to take the fit on fuzz speed
FUZZ_TEST_TIMEOUT=30

# Call the common fuzzing logic
run_fuzz_test
