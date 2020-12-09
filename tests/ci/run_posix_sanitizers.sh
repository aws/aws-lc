#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

build_type=Release
cflags=("-DCMAKE_BUILD_TYPE=${build_type}")

if [ $(dpkg --print-architecture) == "arm64" ]; then
  # BoringSSL provides two sets tests: the C/C++ tests and the blackbox tests.
  # Details: https://github.com/google/boringssl/blob/master/BUILDING.md
  # The blackbox tests (run `go test` under `ssl/test/runner`) take 30 minutes to complete on ARM when ASAN clang flag enabled.
  # But the blackbox tests take less than 2 minutes to complete on other test dimensions -- X86 ASAN and ARM (when ASAN disabled).
  # Instead of running the two sets tests, only the former test is executed here.
  # TODO: Open a GitHub issue on https://github.com/google/sanitizers/issues, and then link the issue here.
  echo "Building AWS-LC in ${build_type} mode with address sanitizer, and running only non ssl test."
  run_build -DASAN=1 -DUSE_CUSTOM_LIBCXX=1 "${cflags[@]}"
  go run util/all_tests.go -build-dir test_build_dir
else
  echo "Testing AWS-LC in ${build_type} mode with address sanitizer."
  build_and_test -DASAN=1 -DUSE_CUSTOM_LIBCXX=1 "${cflags[@]}"
fi

echo "Testing AWS-LC in ${build_type} mode with control flow integrity sanitizer."
build_and_test -DCFI=1 -DUSE_CUSTOM_LIBCXX=1 "${cflags[@]}"

echo "Testing AWS-LC in ${build_type} mode with undefined behavior sanitizer."
build_and_test -DUBSAN=1 "${cflags[@]}"

if [ $(dpkg --print-architecture) == "arm64" ]; then
  # ARM MSAN runs get stuck on PoolTest.Threads for over an hour https://github.com/awslabs/aws-lc/issues/13
  echo "Building AWS-LC in ${build_type} mode with memory sanitizer."
  run_build -DMSAN=1 -DUSE_CUSTOM_LIBCXX=1 "${cflags[@]}"
else
  echo "Testing AWS-LC in ${build_type} mode with memory sanitizer."
  build_and_test -DMSAN=1 -DUSE_CUSTOM_LIBCXX=1 "${cflags[@]}"
fi

if [ $(dpkg --print-architecture) == "amd64" ]; then
  # x86 TSAN runs get stuck on PoolTest.Threads for over an hour https://github.com/awslabs/aws-lc/issues/13
  echo "Building AWS-LC in ${build_type} mode with thread sanitizer."
  run_build -DTSAN=1 -DUSE_CUSTOM_LIBCXX=1 "${cflags[@]}"
else
  echo "Testing AWS-LC in ${build_type} mode with thread sanitizer."
  build_and_test -DTSAN=1 -DUSE_CUSTOM_LIBCXX=1 "${cflags[@]}"
fi
