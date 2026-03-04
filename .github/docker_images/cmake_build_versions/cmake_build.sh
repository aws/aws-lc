#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex -o pipefail

echo "Building CMake Version: ${CMAKE_VERSION:-unknown}"

NUM_CPU_THREADS=$(grep -c ^processor /proc/cpuinfo)

# CMake versions before 4.0 have compatibility issues with newer system curl libraries.
# The curl headers define CURL_NETRC_* as long int values, but older CMake code expects
# them to be CURL_NETRC_OPTION enum values, causing compilation errors.
# For older versions, we use CMake's bundled curl instead of the system curl.
CONFIGURE_OPTS="--prefix=/opt/cmake --system-libarchive"

if [[ "${CMAKE_VERSION}" =~ ^[0-3]\. ]]; then
    # CMake versions 3.x and earlier: use bundled curl to avoid compatibility issues
    echo "Using bundled curl for CMake ${CMAKE_VERSION}"
fi

./configure ${CONFIGURE_OPTS}
make -j"${NUM_CPU_THREADS}"
make install
