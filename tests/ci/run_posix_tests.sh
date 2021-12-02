#!/bin/bash
set -exo pipefail
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

export CC=clang-10
export CXX=clang++-10

source tests/ci/common_posix_setup.sh

# echo "Testing AWS-LC in debug mode."
build_and_test
# ./test_build_dir/ssl/ssl_test 
# ./test_build_dir/ssl/ssl_test --gtest_filter=WithVersion/SSLVersionTest.OneSidedShutdown/TLS1_2_SSL_TRANSFER
# gdb --args ./test_build_dir/ssl/ssl_test --gtest_filter=WithVersion/SSLVersionTest.GetServerName/TLS1_2_SSL_TRANSFER

# echo "Testing AWS-LC in release mode."
# build_and_test -DCMAKE_BUILD_TYPE=Release

# echo "Testing AWS-LC small compilation."
# build_and_test -DOPENSSL_SMALL=1 -DCMAKE_BUILD_TYPE=Release

# echo "Testing AWS-LC in no asm mode."
# build_and_test -DOPENSSL_NO_ASM=1 -DCMAKE_BUILD_TYPE=Release

# echo "Testing building shared lib."
# run_build -DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=Release

# if [[ "${AWSLC_FIPS}" == "1" ]]; then
#   echo "Testing AWS-LC in FIPS release mode."
#   build_and_test -DFIPS=1 -DCMAKE_BUILD_TYPE=Release
#   "${BUILD_ROOT}/util/fipstools/cavp/test_fips"
# fi

# if [[ "${AWSLC_C99_TEST}" == "1" ]]; then
#     echo "Testing the C99 compatability of AWS-LC headers."
#     ./tests/coding_guidelines/c99_gcc_test.sh
# fi

# if [[ "${AWSLC_CODING_GUIDELINES_TEST}" == "1" ]]; then
#   echo "Testing that AWS-LC is compliant with the coding guidelines."
#   source ./tests/coding_guidelines/coding_guidelines_test.sh
# fi

# if [[ "${AWSLC_FUZZ}" == "1" ]]; then
#   echo "Testing building fuzz tests."
#   run_build -DFUZZ=1
# fi
