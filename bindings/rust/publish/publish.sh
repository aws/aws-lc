#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# You will need to have cargo-public-api installed:
# cargo install public-api

set -e -x

PUBLISH=0
PREV_VERSION=0
SKIP_DIFF=0
FIPS=0

while getopts "d:spf" option; do
  case ${option} in
  d )
    # For example:
    # ./publish.sh -d 0.1.1
    PREV_VERSION="$OPTARG"
    ;;
  # The public API diff should only be skipped if releasing a new major version
  # (or a new minor version when the major version number is 0).
  s )
    SKIP_DIFF=1
    ;;
  p )
    PUBLISH=1
    ;;
  f )
    FIPS=1
    ;;
  * )
    echo Invalid argument: -"${?}"
    usage
    exit 1
    ;;
  esac
done

# Remove the internal_generation feature for bindings pre-generation before publishing.
function remove_internal_feature {
  if [[ "$(uname)" == "Darwin" ]]; then
    find ./ -type f  -name "Cargo.toml" | xargs sed -i '' -e "s|${INTERNAL_FEATURE_STRING}||g"
  else
    find ./ -type f  -name "Cargo.toml" | xargs sed -i -e "s|${INTERNAL_FEATURE_STRING}||g"
  fi
}

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)
TMP_DIR="${AWS_LC_DIR}"/bindings/rust/tmp
if [[ ${FIPS} -eq 1 ]]; then
  CRATE_NAME=aws-lc-fips-sys
else
  CRATE_NAME=aws-lc-sys
fi
CRATE_DIR="${TMP_DIR}/${CRATE_NAME}"
COMPLETION_MARKER="${CRATE_DIR}"/.generation_complete
INTERNAL_FEATURE_STRING="^internal_generate .*"

if [[ ! -f "${COMPLETION_MARKER}" ]]; then
  echo
  echo The crate generation script must exit successfully before publishing.
  echo
  exit 1
fi

pushd "${CRATE_DIR}"
remove_internal_feature
cargo clean
cargo clippy --fix --allow-no-vcs
cargo fmt
cargo test # sanity check
cargo clean
if [[ "${SKIP_DIFF}" -eq 0 ]]; then
  if [[ "${PREV_VERSION}" == "0" ]]; then
    echo Aborting. Must specify previous crate version for API diff.
    exit 1;
  fi
  cargo public-api --deny changed --deny removed --diff-published "${CRATE_NAME}@${PREV_VERSION}"
fi
cargo publish --dry-run --allow-dirty --no-verify

if [[ ${PUBLISH} -eq 1 ]]; then
  # The --no-verify is needed because we create `src/bindings.rs` during the build process.
  # The maximum crate size allowed by crates-io is 10MB.
  cargo publish --allow-dirty --no-verify
else
  echo Not published. Use -p to publish.
fi

popd
