#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

SCRIPT_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
SCRIPT_DIR="$(readlink -f "${SCRIPT_DIR}")"

"${SCRIPT_DIR}/run_cross_tests.sh" ppc64le powerpc64le-unknown-linux-gnu "-DCMAKE_BUILD_TYPE=Release" "-DCMAKE_BUILD_TYPE=Release -DFIPS=1 -DBUILD_SHARED_LIBS=1"
