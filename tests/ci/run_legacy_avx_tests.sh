#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

source tests/ci/common_posix_setup.sh

echo "Testing AWS-LC in release mode."
build_and_test -DCMAKE_BUILD_TYPE=Release

# Lightly verify that uncommon build options does not break the build. Fist
# define a list of typical build options to verify the special build option with
build_options_to_test=("" "-DBUILD_SHARED_LIBS=1" "-DCMAKE_BUILD_TYPE=Release" "-DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=Release" "-DDISABLE_PERL=ON -DDISABLE_GO=ON" "-DENABLE_PRE_SONAME_BUILD=0")

## Build option: MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX
for build_option in "${build_options_to_test[@]}"; do
  build_and_test ${build_option} -DMY_ASSEMBLER_IS_TOO_OLD_FOR_AVX=ON
done

## Build option: MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX
for build_option in "${build_options_to_test[@]}"; do
  build_and_test ${build_option} -DMY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX=ON
done
