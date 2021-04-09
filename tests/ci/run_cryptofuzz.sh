#!/bin/bash
set -exo pipefail
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_fuzz.sh
source "${FUZZ_ROOT}/fuzz_env.sh"

mkdir -p "$BUILD_ROOT"
cd "$BUILD_ROOT"

# Build AWS-LC based on https://github.com/guidovranken/cryptofuzz/blob/master/docs/openssl.md
cmake -DCMAKE_CXX_FLAGS="$CXXFLAGS" -DCMAKE_C_FLAGS="$CFLAGS" -DBORINGSSL_ALLOW_CXX_RUNTIME=1 -GNinja ../
ninja
cd ../
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_BORINGSSL"
export OPENSSL_INCLUDE_PATH=`realpath include/`
export OPENSSL_LIBCRYPTO_A_PATH=`realpath build/crypto/libcrypto.a`

cd "${CRYPTOFUZZ_SRC}/modules/openssl"
make "-j${NUM_CPU_THREADS}"

export CFLAGS="${CFLAGS} -I $OPENSSL_INCLUDE_PATH"
export CXXFLAGS="${CXXFLAGS} -I $OPENSSL_INCLUDE_PATH"

cd "$CRYPTOFUZZ_SRC"
make

FUZZ_TEST_ROOT="${BUILD_ROOT}/fuzz_run_root"
FUZZ_TEST_CORPUS="${FUZZ_TEST_ROOT}/run_corpus"
SHARED_CORPUS="${CORPUS_ROOT}/shared_corpus/${FUZZ_NAME}/shared_corpus"
ARTIFACTS_FOLDER="${FUZZ_TEST_ROOT}/artifacts"
FUZZ_RUN_LOGS="${FUZZ_TEST_ROOT}/logs"
SUMMARY_LOG="${FUZZ_RUN_LOGS}/summary.log"
FAILURE_ROOT="${CORPUS_ROOT}/runs/${DATE_NOW}/${BUILD_ID}"

mkdir -p "$SHARED_CORPUS" "$FUZZ_TEST_ROOT" "$FUZZ_TEST_CORPUS" "$ARTIFACTS_FOLDER" "$FUZZ_RUN_LOGS"

./cryptofuzz -print_final_stats=1 -timeout=5 -max_total_time=60 -dict "$CRYPTOFUZZ_DICT" \
  "$FUZZ_TEST_CORPUS" "$SHARED_CORPUS" "$CRYPTOFUZZ_SEED_CORPUS" 2>&1 | tee "$SUMMARY_LOG"