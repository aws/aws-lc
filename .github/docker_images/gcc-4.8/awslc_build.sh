#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex -o pipefail

echo "Building with GCC Version: $(gcc --version)"

BUILD_DIR=$(mktemp -d)
SRC_DIR="${SRC_DIR:-/awslc}"

pushd "${BUILD_DIR}"

cmake "${SRC_DIR}" "-DDISABLE_PERL=ON" "-DMY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX=1"
cmake --build "${BUILD_DIR}" --target run_tests

popd # ${BUILD_DIR}
