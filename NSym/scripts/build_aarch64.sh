#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

BUILD_TYPE=$1
MICRO_ARCH=$2
TARGET="aarch64-unknown-linux-gnu"

mkdir -p build_src/aarch64
cd build_src/aarch64
export LDFLAGS="-fuse-ld=lld"
cmake -DCMAKE_BUILD_TYPE=$BUILD_TYPE \
      -DBUILD_LIBSSL=OFF \
      -DKEEP_ASM_LOCAL_SYMBOLS=1 \
      -DCMAKE_TOOLCHAIN_FILE=../../scripts/build_aarch64.cmake \
      -DCMAKE_C_FLAGS="-mcpu=${MICRO_ARCH}" \
      -DCMAKE_CXX_FLAGS="-mcpu=${MICRO_ARCH}" \
      -DCMAKE_ASM_FLAGS="-mcpu=${MICRO_ARCH}" \
      -DCMAKE_C_COMPILER_TARGET=$TARGET \
      -DCMAKE_CXX_COMPILER_TARGET=$TARGET \
      -DCMAKE_ASM_COMPILER_TARGET=$TARGET \
      ../../../src

NUM_CPU_THREADS=$(grep -c ^processor /proc/cpuinfo)
make -j $NUM_CPU_THREADS
