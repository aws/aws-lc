#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

source tests/ci/common_posix_setup.sh

echo "Testing AWS-LC shared library in release mode."
build_and_test -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=1

if [ "$PLATFORM" != "amd64" ] && [ "$PLATFORM" != "x86_64" ]; then
    # ARM64 platforms are tested via emulation, so the test durations exceed our 1 hour expectation
    echo "Skipping further testing for $KERNEL_NAME $PLATFORM"
    exit 0
fi

echo "Testing AWS-LC static library in release mode."
build_and_test -DCMAKE_BUILD_TYPE=Release

echo "Testing AWS-LC shared library in FIPS Release mode."
fips_build_and_test -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=1

echo "Testing AWS-LC static library in FIPS Release mode."
fips_build_and_test -DCMAKE_BUILD_TYPE=Release
