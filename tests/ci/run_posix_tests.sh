#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

source tests/ci/common_posix_setup.sh

echo "Testing AWS-LC in debug mode."
build_and_test -DENABLE_DILITHIUM=ON

echo "Testing AWS-LC in release mode."
build_and_test -DCMAKE_BUILD_TYPE=Release -DENABLE_DILITHIUM=ON

echo "Testing AWS-LC with Dilithium3 disabled."
build_and_test -DENABLE_DILITHIUM=OFF

echo "Testing AWS-LC small compilation."
build_and_test -DOPENSSL_SMALL=1 -DCMAKE_BUILD_TYPE=Release -DENABLE_DILITHIUM=ON

echo "Testing AWS-LC with libssl off."
build_and_test -DBUILD_LIBSSL=OFF -DCMAKE_BUILD_TYPE=Release -DENABLE_DILITHIUM=ON

echo "Testing AWS-LC in no asm mode."
build_and_test -DOPENSSL_NO_ASM=1 -DCMAKE_BUILD_TYPE=Release -DENABLE_DILITHIUM=ON

echo "Testing building shared lib."
build_and_test -DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=Release -DENABLE_DILITHIUM=ON

echo "Testing with a SysGenId."
TEST_SYSGENID_PATH=$(mktemp)
dd if=/dev/zero of="${TEST_SYSGENID_PATH}" bs=1 count=4096
build_and_test -DTEST_SYSGENID_PATH="${TEST_SYSGENID_PATH}" -DENABLE_DILITHIUM=ON

echo "Testing with pre-generated assembly code."
build_and_test -DDISABLE_PERL=ON -DENABLE_DILITHIUM=ON

echo "Testing building with AArch64 Data-Independent Timing (DIT) on."
build_and_test -DENABLE_DATA_INDEPENDENT_TIMING=ON -DCMAKE_BUILD_TYPE=Release -DENABLE_DILITHIUM=ON

if [[ "${AWSLC_C99_TEST}" == "1" ]]; then
    echo "Testing the C99 compatability of AWS-LC headers."
    ./tests/coding_guidelines/c99_gcc_test.sh
fi

if [[ "${AWSLC_CODING_GUIDELINES_TEST}" == "1" ]]; then
  echo "Testing that AWS-LC is compliant with the coding guidelines."
  source ./tests/coding_guidelines/coding_guidelines_test.sh
fi

# Lightly verify that uncommon build options does not break the build. Fist
# define a list of typical build options to verify the special build option with
build_options_to_test=("" "-DBUILD_SHARED_LIBS=1" "-DCMAKE_BUILD_TYPE=Release" "-DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=Release" "-DDISABLE_PERL=ON -DDISABLE_GO=ON")

## Build option: MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX
for build_option in "${build_options_to_test[@]}"; do
  run_build ${build_option} -DMY_ASSEMBLER_IS_TOO_OLD_FOR_AVX=ON -DENABLE_DILITHIUM=ON
done

## Build option: MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX
for build_option in "${build_options_to_test[@]}"; do
  run_build ${build_option} -DMY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX=ON -DENABLE_DILITHIUM=ON
done