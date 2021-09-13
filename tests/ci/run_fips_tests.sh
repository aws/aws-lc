#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

echo "Testing AWS-LC in FIPS Debug mode."
fips_build_and_test

# TODO(shang): investigate delocate transform errors when building static awslc with gcc fips release on aarch.
if [[ ("${CC}" == 'clang'*) || ("$(uname -p)" == 'x86_64'*) ]]; then
  echo "Testing AWS-LC in FIPS Release mode."
  fips_build_and_test -DCMAKE_BUILD_TYPE=Release

  echo "Testing AWS-LC in FIPS RelWithDebInfo mode."
  fips_build_and_test -DCMAKE_BUILD_TYPE=RelWithDebInfo
fi

echo "Testing shared AWS-LC in FIPS Debug mode."
fips_build_and_test -DBUILD_SHARED_LIBS=1

echo "Testing shared AWS-LC in FIPS Release mode."
fips_build_and_test -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=1

echo "Testing shared AWS-LC in FIPS RelWithDebInfo mode."
fips_build_and_test -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1

if [[  "${AWSLC_NO_ASM_FIPS}" == "1" ]]; then
  # This dimension corresponds to boringssl CI 'linux_fips_noasm_asan'.
  # https://logs.chromium.org/logs/boringssl/buildbucket/cr-buildbucket.appspot.com/8852496158370398336/+/steps/cmake/0/logs/execution_details/0
  echo "Testing AWS-LC in FIPS OPENSSL_NO_ASM Release mode."
  fips_build_and_test -DASAN=1 -DOPENSSL_NO_ASM=1 -DCMAKE_BUILD_TYPE=Release
  # TODO(shang): add ASAN build with RelWithDebInfo if final FIPS build uses the option.
fi
