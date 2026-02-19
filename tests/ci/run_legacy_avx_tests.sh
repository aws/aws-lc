#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

source tests/ci/common_posix_setup.sh

AVX_FLAG="${1}"

# Validate AVX_FLAG is provided
if [[ -z "${AVX_FLAG}" ]]; then
  echo "Usage: $0 <AVX_FLAG>"
  echo "Valid values: MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX, MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX"
  exit 1
fi

# Lightly verify that uncommon build options does not break the build. First
# define a list of typical build options to verify the special build option with
build_options_to_test=("" "-DBUILD_SHARED_LIBS=1" "-DCMAKE_BUILD_TYPE=Release" "-DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=Release" "-DENABLE_PRE_SONAME_BUILD=0")

for build_option in "${build_options_to_test[@]}"; do
  build_and_test ${build_option} -D${AVX_FLAG}=ON
done

# When Go is disabled, a different test target is produced
build_and_run_minimal_test -DDISABLE_PERL=ON -DDISABLE_GO=ON -D${AVX_FLAG}=ON
