#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

source tests/ci/common_posix_setup.sh

echo "Testing a prefix build of AWS-LC in debug mode."
build_prefix_and_test

build_options_to_test=("" "-DOPENSSL_SMALL=1" "-DOPENSSL_NO_ASM=1" "-DENABLE_PRE_SONAME_BUILD=0")

for build_option in "${build_options_to_test[@]}"; do
  echo "Testing a prefix build of AWS-LC in release mode with additional build option: ${build_option}"
  build_prefix_and_test ${build_option} -DCMAKE_BUILD_TYPE=Release
done
