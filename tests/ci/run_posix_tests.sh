#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

source tests/ci/common_posix_setup.sh

echo "Testing AWS-LC in debug mode."
build_and_test

echo "Testing c_rehash script executes."
test_c_rehash

echo "Testing AWS-LC in release mode."
build_and_test -DCMAKE_BUILD_TYPE=Release

echo "Testing AWS-LC small compilation."
build_and_test -DOPENSSL_SMALL=1 -DCMAKE_BUILD_TYPE=Release

echo "Testing AWS-LC with libssl off."
build_and_test -DBUILD_LIBSSL=OFF -DCMAKE_BUILD_TYPE=Release

echo "Testing AWS-LC in no asm mode."
build_and_test -DOPENSSL_NO_ASM=1 -DCMAKE_BUILD_TYPE=Release

echo "Testing building shared lib."
build_and_test -DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=Release

echo "Testing with a SysGenId."
TEST_SYSGENID_PATH=$(mktemp)
dd if=/dev/zero of="${TEST_SYSGENID_PATH}" bs=1 count=4096
build_and_test -DTEST_SYSGENID_PATH="${TEST_SYSGENID_PATH}"

echo "Testing with pre-generated assembly code."
build_and_test -DDISABLE_PERL=ON

echo "Testing building with AArch64 Data-Independent Timing (DIT) on."
build_and_test -DENABLE_DATA_INDEPENDENT_TIMING=ON -DCMAKE_BUILD_TYPE=Release

# Lightly verify that uncommon build options does not break the build. Fist
# define a list of typical build options to verify the special build option with
build_options_to_test=("" "-DBUILD_SHARED_LIBS=1" "-DCMAKE_BUILD_TYPE=Release" "-DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=Release" "-DDISABLE_PERL=ON -DDISABLE_GO=ON")

## Build option: MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX
for build_option in "${build_options_to_test[@]}"; do
  run_build ${build_option} -DMY_ASSEMBLER_IS_TOO_OLD_FOR_AVX=ON
done

## Build option: MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX
for build_option in "${build_options_to_test[@]}"; do
  run_build ${build_option} -DMY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX=ON
done