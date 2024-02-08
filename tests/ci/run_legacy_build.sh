#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

source tests/ci/common_posix_setup.sh

# gcc 4.1.3 is used in our CI because ubuntu 7.10's `gcc4.1.3` and
# `GNU assembler 2.18` resembles rhel5's binutils the most. SSE4
# assembly instructions are not supported in ubuntu 7.04, while rhel5
# and ubuntu 7.10 do.
echo "Testing gcc 4.1.2 / 4.1.3 support."

# Go is disabled because go tries to fetch from the server when building,
# but the certificates on the ancient ubuntu are expired and the ancient 
# tools are insufficient to update the certificates.
# The build flags used are the same as our ancient internal build.
run_build  -DDISABLE_GO=ON -DBUILD_TESTING=OFF -DBUILD_LIBSSL=OFF -DCMAKE_BUILD_TYPE=Debug -DMY_ASSEMBLER_IS_TOO_OLD_FOR_AVX=ON -std=gnu99 -fgnu89-inline
