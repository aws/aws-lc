#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

BUILD_TYPE=$1
TARGET="aarch64-unknown-linux-gnu"

mkdir -p build_src/llvm_aarch64
cd build_src/llvm_aarch64
export LDFLAGS="-fuse-ld=lld"

export LLVM_COMPILER=clang
export BINUTILS_TARGET_PREFIX=aarch64-linux-gnu

cmake -DCMAKE_BUILD_TYPE=$BUILD_TYPE \
      -DCMAKE_CXX_FLAGS="-ggdb" \
      -DCMAKE_C_FLAGS="-ggdb" \
      -DBUILD_LIBSSL=OFF \
      -DCMAKE_TOOLCHAIN_FILE=../../scripts/aarch64/build_llvm.cmake \
      -DCMAKE_C_FLAGS="--target=${TARGET} -I/usr/aarch64-linux-gnu/include -I/usr/aarch64-linux-gnu/include/c++/9/aarch64-linux-gnu" \
      -DCMAKE_CXX_FLAGS="--target=${TARGET} -I/usr/aarch64-linux-gnu/include -I/usr/aarch64-linux-gnu/include/c++/9/aarch64-linux-gnu" \
      -DCMAKE_ASM_FLAGS="--target=${TARGET} -I/usr/aarch64-linux-gnu/include -I/usr/aarch64-linux-gnu/include/c++/9/aarch64-linux-gnu" \
      -DCMAKE_CXX_LINK_FLAGS="-Wl,--unresolved-symbols=ignore-in-object-files -I/usr/aarch64-linux-gnu/include -I/usr/aarch64-linux-gnu/include/c++/9/aarch64-linux-gnu"  \
      ../../../src

NUM_CPU_THREADS=$(grep -c ^processor /proc/cpuinfo)
make -j $NUM_CPU_THREADS
