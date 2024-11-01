#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

source tests/ci/common_posix_setup.sh

echo "Testing AWS-LC shared library in release mode."
build_and_test -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=1

echo "Testing AWS-LC static library in release mode."
build_and_test -DCMAKE_BUILD_TYPE=Release

echo "Testing AWS-LC shared library in FIPS Release mode."
fips_build_and_test -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=1

echo "Testing AWS-LC static library in FIPS Release mode."
fips_build_and_test -DCMAKE_BUILD_TYPE=Release
