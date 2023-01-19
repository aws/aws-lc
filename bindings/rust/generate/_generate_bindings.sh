#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -e -x

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)
TMP_DIR="${AWS_LC_DIR}"/bindings/rust/tmp
CRATE_DIR="${TMP_DIR}/$@"

pushd "${CRATE_DIR}"

export GOPROXY=direct

cargo clean
# internal_generate pre-generates the bindings for a specific platform. This feature 
# is only intended for internal use and is removed prior to crate publishing.
cargo build --features internal_generate
cargo clean

popd
