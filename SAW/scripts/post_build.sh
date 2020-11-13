#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0


set -e

mkdir -p build/llvm/crypto build/x86/crypto
cp build_src/llvm/crypto/crypto_test build/llvm/crypto/crypto_test
cp build_src/x86/crypto/crypto_test build/x86/crypto/crypto_test
extract-bc build/llvm/crypto/crypto_test
