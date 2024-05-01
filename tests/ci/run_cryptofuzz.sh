#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

# Sourcing these files check for environment variables which may be unset so wait to enable -u
source tests/ci/common_fuzz.sh
source "${FUZZ_ROOT}/fuzz_env.sh"
# After loading everything any undefined variables should fail the build
set -u

rm -rf "${BUILD_ROOT:?}"
mkdir -p "$BUILD_ROOT"
cd "$BUILD_ROOT"

# Build AWS-LC based on https://github.com/guidovranken/cryptofuzz/blob/master/docs/openssl.md
${CMAKE_COMMAND} -DCMAKE_CXX_FLAGS="$CXXFLAGS" -DCMAKE_C_FLAGS="$CFLAGS" -DBORINGSSL_ALLOW_CXX_RUNTIME=1 \
  -GNinja -DBUILD_TESTING=OFF -DBUILD_LIBSSL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo ../
ninja
cd ../

# CRYPTOFUZZ_AWSLC will enable AES_256_XTS in upstream code. See `V610453347`.
# TODO: remove CRYPTOFUZZ_BORINGSSL when CRYPTOFUZZ_AWSLC is fully integrated.
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_BORINGSSL -DCRYPTOFUZZ_AWSLC"
export OPENSSL_INCLUDE_PATH=`realpath include/`
export OPENSSL_LIBCRYPTO_A_PATH=`realpath ${BUILD_ROOT}/crypto/libcrypto.a`

# For cryptofuzz development only, override CRYPTOFUZZ_SRC with CUSTOM_CRYPTOFUZZ_REPO_DIR.
CUSTOM_CRYPTOFUZZ_REPO_DIR=''
if [[ -z "${CUSTOM_CRYPTOFUZZ_REPO_DIR}" ]]; then
  echo "CUSTOM_CRYPTOFUZZ_REPO_DIR is empty."
else
  export CRYPTOFUZZ_SRC="${CUSTOM_CRYPTOFUZZ_REPO_DIR}"
  # Local development does not need differential fuzzing.
  # Remove these libs related build flags.
  export CXXFLAGS="${CXXFLAGS// -DCRYPTOFUZZ_BOTAN/}"
  export CXXFLAGS="${CXXFLAGS// -DCRYPTOFUZZ_CRYPTOPP/}"
  cd "$CRYPTOFUZZ_SRC"
  # This step is to generate required header and cpp files.
  python3 gen_repository.py
fi

# Build the common OpenSSL module with AWS-LC
cd "${CRYPTOFUZZ_SRC}/modules/openssl"
make "-j${NUM_CPU_THREADS}"

export CFLAGS="${CFLAGS} -I $OPENSSL_INCLUDE_PATH"
export CXXFLAGS="${CXXFLAGS} -I $OPENSSL_INCLUDE_PATH"
export LIBFUZZER_LINK="-fsanitize=fuzzer"

# Build the overall cryptofuzz and generate_corpus binary
cd "$CRYPTOFUZZ_SRC"
rm -rf cryptofuzz
rm -rf generate_corpus
make "-j${NUM_CPU_THREADS}" cryptofuzz generate_corpus

# Common AWS-LC fuzzing setup, the cryptofuzz binary is in this folder so FUZZ_TEST_PATH=FUZZ_NAME
FUZZ_NAME="cryptofuzz"
FUZZ_TEST_PATH="${CRYPTOFUZZ_SRC}/${FUZZ_NAME}"
SRC_CORPUS="$CRYPTOFUZZ_SEED_CORPUS"

# For cryptofuzz development only, uncomment below code to generate new corpus.
# rm -rf "${CRYPTOFUZZ_SEED_CORPUS:?}" && mkdir "$CRYPTOFUZZ_SEED_CORPUS"
# ./generate_corpus "$CRYPTOFUZZ_SEED_CORPUS"

# Perform the actual fuzzing. We want the total build time to be about 45 minutes:
# 5 minutes for building AWS-LC and Cryptofuzz
# 16 minutes (1000 seconds) of fuzzing
# 24 minutes of cleanup and merging in new inputs
TIME_FOR_EACH_FUZZ=1000

# Some fuzz tests can take a while but still pass. This is a tradeoff: less false positive noise, but some inputs that take
# a long time could lead to a denial of service avenue. We're mostly interested in correctness and memory safety at this
# time so we're willing to take the fit on fuzz speed
FUZZ_TEST_TIMEOUT=30

# Call the common fuzzing logic
run_fuzz_test
