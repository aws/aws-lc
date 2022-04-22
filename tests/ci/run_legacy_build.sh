#!/bin/bash
set -exo pipefail
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

# Go is disabled because go tries to fetch from the server when building,
# but the certificates on the ancient ubuntu are expired and the ancient 
# tools are insufficient to update the certificates.
# The build flags used are the same as our ancient internal build.
echo "Testing gcc 4.1.2 support."
run_build  -DBUILD_TESTING="OFF" -DBUILD_LIBSSL="OFF" -DCMAKE_BUILD_TYPE="Debug" -DMY_ASSEMBLER_IS_TOO_OLD_FOR_AVX=ON -std=gnu99 -fgnu89-inline
