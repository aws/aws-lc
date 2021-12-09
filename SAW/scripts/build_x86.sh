#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

BUILD_TYPE=$1

mkdir -p build_src/x86
cd build_src/x86
export CC=clang
export CXX=clang++
cmake -DCMAKE_BUILD_TYPE=$BUILD_TYPE -DBUILD_LIBSSL=OFF ../../../src
NUM_CPU_THREADS=$(grep -c ^processor /proc/cpuinfo)
make -j $NUM_CPU_THREADS
