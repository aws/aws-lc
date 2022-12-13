#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -e -x

PUBLISH=0
PREV_VERSION=0
SKIP_DIFF=0

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)
TMP_DIR="${AWS_LC_DIR}"/bindings/rust/tmp
CRATE_NAME=aws-lc-fips-sys
CRATE_DIR="${TMP_DIR}/${CRATE_NAME}"
COMPLETION_MARKER="${CRATE_DIR}"/.generation_complete
INTERNAL_FEATURE_STRING="^internal_generate .*"

source ${SCRIPT_DIR}/_publish_tools.sh

publish_options "$@"
find_completion_marker ${COMPLETION_MARKER}

pushd "${CRATE_DIR}"
remove_internal_feature
run_prepublish_checks_linux "${CRATE_NAME}"
publish_crate "${CRATE_NAME}"
popd
