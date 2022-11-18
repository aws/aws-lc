#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -e -x

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)
GEN_DIR="${AWS_LC_DIR}"/bindings/rust/generate
TMP_DIR="${AWS_LC_DIR}"/bindings/rust/tmp

pushd "${GEN_DIR}"

cargo clean
cargo run "${TMP_DIR}"/aws-lc-sys
cargo clean

popd
