#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

source tests/ci/common_posix_setup.sh

echo "Testing a prefix build of AWS-LC in debug mode."
build_prefix_and_test

echo "Testing a prefix build of AWS-LC in release mode."
build_prefix_and_test -DCMAKE_BUILD_TYPE=Release

echo "Testing a prefix build of AWS-LC small compilation."
build_prefix_and_test -DOPENSSL_SMALL=1 -DCMAKE_BUILD_TYPE=Release

echo "Testing a prefix build of AWS-LC in no asm mode."
build_prefix_and_test -DOPENSSL_NO_ASM=1 -DCMAKE_BUILD_TYPE=Release
