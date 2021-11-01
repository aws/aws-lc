#!/bin/bash -x
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

# bcm.o should be prebuilt and moved to |SRC_ROOT|.
if [[ -z "${BCM_O_UNDER_SRC_ROOT+x}" || -z "${BCM_O_UNDER_SRC_ROOT}" ]]; then
  echo "BCM_O_UNDER_SRC_ROOT is not defined or empty."
  exit 1
fi
ensure_file ${BCM_O_UNDER_SRC_ROOT}

fips_build_and_test -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=1 -DFIPS_VENDOR_AFFIRM_BCM_O_PATH=${BCM_O_UNDER_SRC_ROOT}
