#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -e -x

PUBLISH=0

while getopts "p" option; do
  case ${option} in
  p )
    PUBLISH=1
    ;;
  * )
    echo Invalid argument: -"${?}"
    usage
    exit 1
    ;;
  esac
done

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)
TMP_DIR="${AWS_LC_DIR}"/bindings/rust/tmp
CRATE_DIR="${TMP_DIR}"/aws-lc-sys
COMPLETION_MARKER="${CRATE_DIR}"/.generation_complete

if [[ ! -f "${COMPLETION_MARKER}" ]]; then
  echo The crate generation script must exit successfully before publishing.
  exit 1
fi

pushd "${CRATE_DIR}"
cargo clean
cargo test # sanity check
cargo clean
cargo clippy --fix --allow-no-vcs
cargo fmt
cargo publish --dry-run --allow-dirty --no-verify

if [[ ${PUBLISH} -eq 1 ]]; then
  # The --no-verify is needed because we create `src/bindings.rs` during the build process.
  cargo publish --allow-dirty --no-verify
else
  echo Not published. Use -p to publish.
fi

popd
