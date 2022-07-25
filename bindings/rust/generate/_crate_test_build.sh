#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -e -x

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)
TMP_DIR="${AWS_LC_DIR}"/bindings/rust/tmp
CRATE_DIR="${TMP_DIR}"/aws-lc-sys

pushd "${CRATE_DIR}"

export GOPROXY=direct

cargo clean
cargo clippy --fix --allow-no-vcs
cargo fmt
cargo build
cargo test
cargo test --release
cargo publish --dry-run --allow-dirty
cargo clean

popd
