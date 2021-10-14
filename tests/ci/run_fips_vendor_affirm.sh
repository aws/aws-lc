#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

DIR_OF_BCM_DIGEST="$(pwd)/crypto/fipsmodule/bcm_o/AL2_x86_64/gcc-7/shared"
# Check bcm.o digest. If this check fails, we may need to follow README.md under |DIR_OF_BCM_DIGEST| to update bcm.o.
check_bcm_o_digest

fips_build_and_test -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=1 -DFIPS_VENDOR_AFFIRM_BCM_O_PATH=${ABS_PATH_TO_BCM_O}
