#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

echo "Testing AWS-LC in release mode."
run_build -DCMAKE_BUILD_TYPE=Release

SSL_TEST_COUNT=0

until [ $SSL_TEST_COUNT -gt 1000 ]
do
  echo "SSL_TEST_COUNT is: $SSL_TEST_COUNT"
  SSL_TEST_COUNT=$((SSL_TEST_COUNT+1))
  ./test_build_dir/ssl/ssl_test
done
