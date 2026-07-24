#!/usr/bin/env bash
set -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

sde_getenforce_check

# The generic OPENSSL_SMALL test legs run on whatever CPU the hosted runner
# happens to land on, so coverage of the CPU profiles this configuration
# cares about is probabilistic. Pin them deterministically with Intel SDE,
# but keep the battery small (the full default list is 18 CPUs):
#  - hsw (Haswell):   AVX2/BMI2 without ADX -- the non-ADX dispatch branch.
#  - bdw (Broadwell): ADX+AVX2+BMI2 without AVX-512 -- the fast paths that
#                     OPENSSL_SMALL must keep (#3355).
#  - icl (Ice Lake):  AVX-512-capable -- proves runtime dispatch never calls
#                     the AVX-512 code that OPENSSL_SMALL compiles out.
SDE_SMALL_CPUS="hsw,bdw,icl"

function build_and_test_small_with_sde {
  run_build "$@"
  run_cmake_custom_target 'all_tests'
  cd "$SRC_ROOT"
  go run util/all_tests.go -build-dir "$BUILD_ROOT" -sde=true \
    -sde-path="$SDEROOT/sde" -sde-cpus="$SDE_SMALL_CPUS"
}

echo "Testing AWS-LC with OPENSSL_SMALL in release mode under Intel's SDE."
build_and_test_small_with_sde -DCMAKE_BUILD_TYPE=Release -DOPENSSL_SMALL=ON

echo "Testing AWS-LC with OPENSSL_SMALL and MY_ASSEMBLER_IS_TOO_OLD_FOR_ADX_AVX2 in release mode under Intel's SDE."
build_and_test_small_with_sde -DCMAKE_BUILD_TYPE=Release -DOPENSSL_SMALL=ON \
  -DMY_ASSEMBLER_IS_TOO_OLD_FOR_ADX_AVX2=ON
