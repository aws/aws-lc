#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -e

PATCH=$(realpath ./patch)
mkdir -p build_src/x86
cd build_src/x86
export CC=clang
export CXX=clang++
(cd ../../../src; patch -p1 -r - --forward <"$PATCH"/nomuxrsp.patch || true)
cmake -DCMAKE_BUILD_TYPE=Rel ../../../src
NUM_CPU_THREADS=$(grep -c ^processor /proc/cpuinfo)
make -j $NUM_CPU_THREADS
