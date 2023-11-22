#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0


set -ex

export BINUTILS_TARGET_PREFIX=aarch64-linux-gnu

mkdir -p build/aarch64/crypto
cp build_src/aarch64/crypto/crypto_test build/aarch64/crypto/crypto_test
