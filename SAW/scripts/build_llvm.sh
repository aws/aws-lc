#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0



set -e

mkdir -p build_src/llvm
cd build_src/llvm
export LLVM_COMPILER=clang
export CC=wllvm
export CXX=clang++
cmake -DCMAKE_BUILD_TYPE=Rel ../../../src
NUM_CPU_THREADS=$(grep -c ^processor /proc/cpuinfo)
make -j $NUM_CPU_THREADS
