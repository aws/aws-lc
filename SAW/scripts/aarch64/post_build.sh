#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0


set -ex

export BINUTILS_TARGET_PREFIX=aarch64-linux-gnu

mkdir -p build/llvm_aarch64/crypto
cp build_src/llvm_aarch64/crypto/crypto_test build/llvm_aarch64/crypto/crypto_test
# Warning produced seems to be about DWARF5 format for debugging
# It should be benign
# https://www.spinics.net/lists/kernel/msg4496916.html
extract-bc build/llvm_aarch64/crypto/crypto_test
