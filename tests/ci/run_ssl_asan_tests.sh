#!/bin/bash
set -exo pipefail
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# BoringSSL has 7k+ ssl runner tests, and the total number of the runner tests keep increasing.
# When ASAN enabled, the tests take more than 1 hour to finish. The cause relates to https://github.com/google/sanitizers/issues/1331
# To reduce the total time, these tests will be executed in diff CodeBuild dimensions.
# Env var |AWS_LC_RUNNER_START_INDEX| and |AWS_LC_RUNNER_END_INDEX| will be used with this script to split runner tests.
source tests/ci/common_posix_setup.sh

build_type=Release
cflags=("-DCMAKE_BUILD_TYPE=${build_type}")

if [ $(dpkg --print-architecture) == "arm64" ]; then
  echo "Testing AWS-LC in ${build_type} mode with address sanitizer."
  build_and_test -DASAN=1 -DUSE_CUSTOM_LIBCXX=1 "${cflags[@]}"
fi
