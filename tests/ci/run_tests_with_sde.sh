#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

echo "Testing AWS-LC in debug mode under Intel's SDE."
build_and_test_with_sde

echo "Testing AWS-LC in release mode under Intel's SDE."
build_and_test_with_sde -DCMAKE_BUILD_TYPE=Release
