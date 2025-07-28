#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex -o pipefail

echo "Building CMake Version: ${CMAKE_VERSION:-unknown}"

NUM_CPU_THREADS=$(grep -c ^processor /proc/cpuinfo)

# At the moment this works fine for all versions, in the future build logic can be modified to
# look at it ${CMAKE_VERSION}.
./configure --prefix=/opt/cmake --system-curl --system-libarchive
make -j"${NUM_CPU_THREADS}"
make install
