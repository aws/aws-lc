#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

source tests/ci/common_posix_setup.sh

echo "Testing distro TLS policy support in libssl."
run_build -DENABLE_DISTRIBUTION_TLS_POLICY=ON -DCMAKE_BUILD_TYPE=Release

"${BUILD_ROOT}/ssl/ssl_test" --gtest_filter=SSLSystemPolicyTest.*
