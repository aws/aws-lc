#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -e

PATH=/lc/bin:/go/bin:$PATH

# TODO: Remove this patch
PATCH=$(realpath ./patch)
(cd ../src; patch -p1 -r - --forward < "$PATCH"/rsa-encrypt.patch || true)

./scripts/build_x86.sh
./scripts/build_llvm.sh
./scripts/post_build.sh
./scripts/run_checks.sh
