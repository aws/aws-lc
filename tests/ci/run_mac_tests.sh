#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

# Only run a subset of the tests due to limited Travis resources
echo "Testing AWS-LC in debug mode."
run_build
./test_build_dir/third_party/boringssl/crypto/crypto_test

echo "Testing AWS-LC in release mode."
run_build -DCMAKE_BUILD_TYPE=Release
./test_build_dir/third_party/boringssl/crypto/crypto_test

echo "Testing AWS-LC small compilation."
run_build -DOPENSSL_SMALL=1 -DCMAKE_BUILD_TYPE=Release
./test_build_dir/third_party/boringssl/crypto/crypto_test

echo "Testing AWS-LC in no asm mode."
run_build -DOPENSSL_NO_ASM=1 -DCMAKE_BUILD_TYPE=Release
./test_build_dir/third_party/boringssl/crypto/crypto_test

echo "Testing building shared lib."
run_build -DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=Release
