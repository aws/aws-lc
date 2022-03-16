#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

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

# Special build options

## build option: MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX
echo "Testing static lib AWS-LC with MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX build option in release mode."
build_and_run_minimal_test -DCMAKE_BUILD_TYPE=Release -DMY_ASSEMBLER_IS_TOO_OLD_FOR_AVX=ON

echo "Testing shared lib AWS-LC with MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX build option in release mode."
build_and_run_minimal_test -DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=Release -DMY_ASSEMBLER_IS_TOO_OLD_FOR_AVX=ON

echo "Testing static lib AWS-LC with MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX build option in debug mode."
build_and_run_minimal_test -DMY_ASSEMBLER_IS_TOO_OLD_FOR_AVX=ON

echo "Testing shared lib AWS-LC with MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX build option in debug mode."
build_and_run_minimal_test -DBUILD_SHARED_LIBS=1 -DMY_ASSEMBLER_IS_TOO_OLD_FOR_AVX=ON

echo "Testing shared lib AWS-LC with MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX build option in [FIPS, release] mode."
build_and_run_minimal_test -DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=Release -DMY_ASSEMBLER_IS_TOO_OLD_FOR_AVX=ON -DFIPS=1
