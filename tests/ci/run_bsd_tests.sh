#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

source tests/ci/common_posix_setup.sh

if [ "$PLATFORM" != "amd64" ] && [ "$PLATFORM" != "x86_64" ]; then
    # ARM64 platforms are tested via emulation.
    # We narrow testing to libcrypto to avoid exceeding 1 hour duration
    SCRIPT_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
    SCRIPT_DIR="$(readlink -f "${SCRIPT_DIR}")"
    source "${SCRIPT_DIR}/gtest_util.sh"

    run_build all

    shard_gtest "${BUILD_ROOT}/crypto/crypto_test --gtest_also_run_disabled_tests"
    shard_gtest ${BUILD_ROOT}/crypto/urandom_test
    shard_gtest ${BUILD_ROOT}/crypto/mem_test
    shard_gtest ${BUILD_ROOT}/crypto/mem_set_test
    shard_gtest ${BUILD_ROOT}/crypto/rwlock_static_init

    shard_gtest ${BUILD_ROOT}/ssl/ssl_test
    shard_gtest ${BUILD_ROOT}/ssl/integration_test

    # Due to its special linkage, this does not use GoogleTest
    ${BUILD_ROOT}/crypto/dynamic_loading_test

    echo "Skipping further testing for $KERNEL_NAME $PLATFORM"
    exit 0
fi

echo "Testing AWS-LC shared library in release mode."
build_and_test -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=1

echo "Testing AWS-LC static library in release mode."
build_and_test -DCMAKE_BUILD_TYPE=Release

echo "Testing AWS-LC shared library in FIPS Release mode."
fips_build_and_test -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=1

echo "Testing AWS-LC static library in FIPS Release mode."
fips_build_and_test -DCMAKE_BUILD_TYPE=Release
