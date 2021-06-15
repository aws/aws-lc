#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

echo "Testing AWS-LC in FIPS debug mode."
fips_build_and_test

echo "Testing AWS-LC in FIPS release mode."
fips_build_and_test -DCMAKE_BUILD_TYPE=Release

echo "Testing shared AWS-LC in FIPS debug mode."
fips_build_and_test -DBUILD_SHARED_LIBS=1

# Passive entropy collection is currently only used on Android. Enable this mode
# manually to verify the mechanism works. This test can be removed if passive
# entropy collection becomes AWS-LC global.
echo "Testing AWS-LC in FIPS mode with passive entropy collection enabled."
fips_build_and_test -DTEST_PASSIVE_ENTROPY=1

# FIPS build in release mode is disabled for GCC due to some build issues relating to '-O3'.
if [[ "${CC}" == 'clang'*  ]]; then
  echo "Testing shared AWS-LC in FIPS release mode."
  fips_build_and_test -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=1
fi

if [[  "${AWSLC_NO_ASM_FIPS}" == "1" ]]; then
  # This dimension corresponds to boringssl CI 'linux_fips_noasm_asan'.
  # https://logs.chromium.org/logs/boringssl/buildbucket/cr-buildbucket.appspot.com/8852496158370398336/+/steps/cmake/0/logs/execution_details/0
  echo "Testing AWS-LC in FIPS OPENSSL_NO_ASM release mode."
  fips_build_and_test -DASAN=1 -DOPENSSL_NO_ASM=1 -DCMAKE_BUILD_TYPE=Release
fi
