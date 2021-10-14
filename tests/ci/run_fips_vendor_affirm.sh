#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

if [[ -z "${ABS_PATH_TO_BCM_O+x}" || -z "${ABS_PATH_TO_BCM_O}" ]]; then
  echo "ABS_PATH_TO_BCM_O is not defined or empty."
  exit 1
fi

fips_build_and_test -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=1 -DFIPS_VENDOR_AFFIRM_BCM_O_PATH=${ABS_PATH_TO_BCM_O}
