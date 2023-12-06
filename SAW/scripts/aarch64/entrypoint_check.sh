#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

PATH=/lc/bin:/go/bin:$PATH

go env -w GOPROXY=direct

# The following warning seems like a bug in wllvm and are benign
# WARNING:Did not recognize the compiler flag "--target=aarch64-unknown-linux-gnu"
./scripts/aarch64/build_llvm.sh "Release"
./scripts/aarch64/post_build.sh
./scripts/aarch64/run_checks.sh
