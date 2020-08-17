#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -e

mkdir -p build_src/x86
cd build_src/x86
export CC=clang
export CXX=clang++
cmake ../../../src
make
