#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

BUILD_TYPE=$1

mkdir -p build_src/llvm
cd build_src/llvm
export LLVM_COMPILER=clang
export CC=wllvm
export CXX=clang++
# The extern function __breakpoint__inv used in proof of ec_GFp_nistp384_point_mul_public is not defined
# Option -DCMAKE_CXX_LINK_FLAGS="-Wl,--unresolved-symbols=ignore-in-object-files" allows it
cmake -DCMAKE_BUILD_TYPE=$BUILD_TYPE -DBUILD_LIBSSL=OFF -DCMAKE_CXX_LINK_FLAGS="-Wl,--unresolved-symbols=ignore-in-object-files" ../../../src
NUM_CPU_THREADS=$(grep -c ^processor /proc/cpuinfo)
make -j $NUM_CPU_THREADS
