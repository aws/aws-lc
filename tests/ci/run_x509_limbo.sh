#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -euxo pipefail

source tests/ci/common_posix_setup.sh

# For now we will just verify that the patch applies and our reporting to builds and tests successfully
# Subsequent follow-up PRs will wire this up into a new CodeBuild project and handle producing and tracking
# the reports.

SCRATCH_DIR="${SRC_ROOT}/scratch"
X509_CI_DIR="${SRC_ROOT}/tests/ci/x509"
X509_LIMBO_SRC="${SCRATCH_DIR}/x509-limbo"

function build_reporting_tool() {
    pushd "${X509_CI_DIR}/limbo-report"
    make
    mv ./limbo-report "${SCRATCH_DIR}/"
    popd # "${X509_CI_DIR}/limbo-report"
}

function clone_and_patch_x509_limbo() {
    git clone https://github.com/C2SP/x509-limbo.git "${X509_LIMBO_SRC}"
    pushd "${X509_LIMBO_SRC}"
    patch -p1 -i "${X509_CI_DIR}/x509-limbo.patch"
    popd # "${X509_LIMBO_SRC}"
}

function run_aws_lc_harness() {
    pushd "${X509_LIMBO_SRC}"
    AWS_LC_SRC_DIR="${SRC_ROOT}" make test-aws-lc
    popd # "${X509_LIMBO_SRC}"
}

mkdir -p "${SCRATCH_DIR}"
rm -rf "${SCRATCH_DIR:?}"/*
pushd "${SCRATCH_DIR}"

build_reporting_tool
clone_and_patch_x509_limbo
run_aws_lc_harness

popd # "${SCRATCH_DIR}"
# rm -rf "${SCRATCH_DIR:?}"
