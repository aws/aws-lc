#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex -o pipefail

echo "Building with CMake Version: $(cmake --version)"

BUILD_DIR=$(mktemp -d)
SRC_DIR="${SRC_DIR:-/awslc}"
CMAKE_CONFIGURE_ARGS=("${argv[@]}")

pushd "${BUILD_DIR}"

cmake "${SRC_DIR}" "${CMAKE_CONFIGURE_ARGS[@]}"
cmake --build .

"${BUILD_DIR}/crypto/crypto_test"

if [[ -a "${BUILD_DIR}/ssl/ssl_test"  ]]; then
    "${BUILD_DIR}/ssl/ssl_test"
fi

popd # ${BUILD_DIR}
