#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex -o pipefail

CHECK_FIPS="$1"
if [[ "${CHECK_FIPS}" == "0" ]]; then
    echo "Testing AWS-LC Non-FIPS"
    /tests/ci/run_posix_tests.sh
elif [[ "${CHECK_FIPS}" == "1" ]]; then
    echo "Testing AWS-LC FIPS"
    /tests/ci/run_fips_tests.sh
else
    exit 1
fi
