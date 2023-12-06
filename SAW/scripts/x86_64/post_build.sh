#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0


set -ex

mkdir -p build/llvm_x86/crypto build/x86/crypto
cp build_src/llvm_x86/crypto/crypto_test build/llvm_x86/crypto/crypto_test
cp build_src/x86/crypto/crypto_test build/x86/crypto/crypto_test
extract-bc build/llvm_x86/crypto/crypto_test
