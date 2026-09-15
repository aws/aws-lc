#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

source tests/ci/common_posix_setup.sh

echo "Testing AWS-LC in debug mode."
build_and_test
echo "Testing c_rehash script executes."
test_c_rehash

echo "Testing AWS-LC in release mode."
build_and_test -DCMAKE_BUILD_TYPE=Release

echo "Testing AWS-LC small compilation."
build_and_test -DOPENSSL_SMALL=1 -DCMAKE_BUILD_TYPE=Release

echo "Testing AWS-LC with libssl off."
build_and_test -DBUILD_LIBSSL=OFF -DCMAKE_BUILD_TYPE=Release

echo "Testing AWS-LC in no asm mode."
build_and_test -DOPENSSL_NO_ASM=1 -DCMAKE_BUILD_TYPE=Release

echo "Testing building shared lib."
build_and_test -DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=Release

# VM UBE (Uniqueness Breaking Event) detection has two backends: vmclock
# (preferred) and SysGenID (fallback). They are tested in separate builds
# because vmclock is preferred at runtime -- enabling both in one build would
# never exercise the SysGenID path. Each build points the backend under test at
# a regular file standing in for its /dev node.
#
# The value round-trip and seqlock tests are DISABLED_ by default: they mutate
# the shared stand-in file that every RAND_bytes call in the suite reads, so
# they cannot run interleaved with other tests. We run them explicitly in a
# dedicated, single-process invocation (nothing else calling RAND_bytes
# concurrently) via --gtest_also_run_disabled_tests.

echo "Testing with VM UBE detection (vmclock backend)."
TEST_VMCLOCK_PATH=$(mktemp)
dd if=/dev/zero of="${TEST_VMCLOCK_PATH}" bs=1 count=4096
build_and_test -DTEST_VMCLOCK_PATH="${TEST_VMCLOCK_PATH}"
echo "Running device-mutating vmclock tests in isolation."
"${BUILD_ROOT}/crypto/crypto_test" \
  --gtest_also_run_disabled_tests \
  --gtest_filter='VmUbeGenerationTest.DISABLED_Vmclock*'

echo "Testing with VM UBE detection (SysGenId backend / vmclock fallback)."
TEST_SYSGENID_PATH=$(mktemp)
dd if=/dev/zero of="${TEST_SYSGENID_PATH}" bs=1 count=4096
build_and_test -DTEST_SYSGENID_PATH="${TEST_SYSGENID_PATH}"
echo "Running device-mutating SysGenId tests in isolation."
"${BUILD_ROOT}/crypto/crypto_test" \
  --gtest_also_run_disabled_tests \
  --gtest_filter='VmUbeGenerationTest.DISABLED_SysGenID*'

echo "Testing with pre-generated assembly code."
build_and_test -DDISABLE_PERL=ON

echo "Testing building with AArch64 Data-Independent Timing (DIT) on."
build_and_test -DENABLE_DATA_INDEPENDENT_TIMING=ON -DCMAKE_BUILD_TYPE=Release

echo "Testing building with opt-out CPU Jitter Entropy."
build_and_test -DDISABLE_CPU_JITTER_ENTROPY=ON
