#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

# build AWS-LC without Go.
echo "Testing AWS-LC without Go in debug mode."
build_and_run_minimal_test

echo "Testing AWS-LC without Go in release mode."
build_and_run_minimal_test -DCMAKE_BUILD_TYPE=Release

echo "Testing shared lib AWS-LC without Go in release mode."
build_and_run_minimal_test -DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=Release
