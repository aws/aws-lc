#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

echo "Testing AWS-LC in FIPS Release mode."
fips_build_and_test -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=1

# The AL2 version of Clang does not have all of the required artifacts for address sanitizer, see P45594051
if [[ "${AWSLC_NO_ASM_FIPS}" == "1" ]]; then
  echo "Building with Clang and testing AWS-LC in FIPS RelWithDebInfo mode with address sanitizer."
  fips_build_and_test -DASAN=1 -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1
else
  echo "Not building with Clang and testing AWS-LC in FIPS RelWithDebInfo mode."
  fips_build_and_test -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1
fi

if [[ ("$(uname -p)" == 'x86_64'*) ]]; then
  echo "Testing AWS-LC in FIPS RelWithDebInfo and DISABLE_GETAUXVAL mode."
  fips_build_and_test -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1 -DDISABLE_GETAUXVAL=1
fi

echo "Testing shared AWS-LC in FIPS Debug mode in a different folder."
BUILD_ROOT=$(realpath "${SRC_ROOT}/../aws-lc-external_build")
fips_build_and_test -DCMAKE_BUILD_TYPE=Debug -DBUILD_SHARED_LIBS=1