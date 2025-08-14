#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

source tests/ci/common_posix_setup.sh

TMP_BUILD_DIR=$(mktemp -d)

echo "Running CMake configure step"
${CMAKE_COMMAND} -B "${TMP_BUILD_DIR}" -S . -GNinja

rm -rf "${TMP_BUILD_DIR:?}"

echo "Adding all changed files to the git tree"
git add -A

echo "Checking for any changes"
git diff --exit-code HEAD
