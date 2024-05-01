#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

source tests/ci/common_posix_setup.sh

echo "Testing AWS-LC without Go in debug mode."
build_and_run_minimal_test -DDISABLE_GO=ON

echo "Testing AWS-LC without Go in release mode."
build_and_run_minimal_test -DDISABLE_GO=ON -DCMAKE_BUILD_TYPE=Release

echo "Testing shared lib AWS-LC without Go in release mode."
build_and_run_minimal_test -DDISABLE_GO=ON -DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=Release

# build AWS-LC without Perl/Go.
echo "Testing AWS-LC without Perl/Go in debug mode."
build_and_run_minimal_test -DDISABLE_GO=ON -DDISABLE_PERL=ON

echo "Testing AWS-LC without Perl/Go in release mode."
build_and_run_minimal_test -DDISABLE_GO=ON -DDISABLE_PERL=ON -DCMAKE_BUILD_TYPE=Release

echo "Testing shared lib AWS-LC without Perl/Go in release mode."
build_and_run_minimal_test -DDISABLE_GO=ON -DDISABLE_PERL=ON -DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=Release
