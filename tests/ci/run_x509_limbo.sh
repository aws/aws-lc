#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -euxo pipefail

source tests/ci/common_posix_setup.sh

# For now we will just verify that the patch applies and our reporting to builds and tests successfully
# Subsequent follow-up PRs will wire this up into a new CodeBuild project and handle producing and tracking
# the reports.

SCRATCH_DIR="${SYS_ROOT}/scratch"
X509_CI_DIR="${SRC_ROOT}/tests/ci/x509"
X509_LIMBO_SRC="${X509_LIMBO_SRC:-/x509-limbo}" # Should be by the docker image
BASE_COMMIT_SRC="${SYS_ROOT}/base-src"

# If BASE_REF is set in the environment we will use that, this provides a mechanism for a user to manually kick off
# a job via the CodeBuild console (otherwise CodeBuild won't let your override variables prefixed with CODEBUILD_).
# Otherwise if CODEBUILD_WEBHOOK_BASE_REF is set we use (this would be in the case of pull requests).
# Lastly if that isn't set then we fallback to CODEBUILD_WEBHOOK_PREV_COMMIT which will be set for a push event.
# If none of those are set the script will fail here.
BASE_REF="${BASE_REF:-${CODEBUILD_WEBHOOK_BASE_REF:-${CODEBUILD_WEBHOOK_PREV_COMMIT:?}}}"

function build_reporting_tool() {
    pushd "${X509_CI_DIR}/limbo-report" 2>&1 >/dev/null
    make
    mv ./limbo-report "${SCRATCH_DIR}/"
    popd 2>&1 >/dev/null # "${X509_CI_DIR}/limbo-report"
}

function setup_x509_limbo() {
    pushd "${X509_LIMBO_SRC}" 2>&1 >/dev/null
    patch -p1 -i "${X509_CI_DIR}/x509-limbo.patch"
    popd 2>&1 >/dev/null # "${X509_LIMBO_SRC}"
}

function build_aws_lc() {
    local BUILD_DIR
    BUILD_DIR=$(mktemp -d)
    cmake -B "${BUILD_DIR}" -S "${1}" -GNinja \
        -DBUILD_SHARED_LIBS=1 \
        -DCMAKE_BUILD_TYPE=Debug \
        -DCMAKE_INSTALL_PREFIX="${2}"
    cmake --build "${BUILD_DIR}"
    cmake --install "${BUILD_DIR}"
    rm -rf "${BUILD_DIR}"
}

function build_aws_lc_harness() {
    local HARNESS_SRC
    HARNESS_SRC="${X509_LIMBO_SRC}/harness/aws-lc"
    local PKG_CONFIG_PATH
    PKG_CONFIG_PATH="${1}/lib64/pkgconfig"

    pushd "${HARNESS_SRC}" 2>&1 >/dev/null
    PKG_CONFIG_PATH="${PKG_CONFIG_PATH}" make 2>&1 >/dev/null

    local HARNESS 
    HARNESS="$(mktemp harnessXXX)"

    mv main "${HARNESS}"

    popd 2>&1 >/dev/null # "${HARNESS_SRC}"

    echo "${HARNESS_SRC}/${HARNESS}"
}

function run_aws_lc_harness() {
    pushd "${X509_LIMBO_SRC}" 2>&1 >/dev/null
    set +e
    make run ARGS="harness --output ./results/aws-lc.json -- ${1}"
    if [ ! -f "${X509_LIMBO_SRC}/results/aws-lc.json" ]; then
        echo "Failed to run x509-limbo harness: ${1}"
        exit 1
    fi
    set -e
    popd 2>&1 >/dev/null # "${X509_LIMBO_SRC}"
}

git worktree add "${BASE_COMMIT_SRC}" "${BASE_REF:?}"

mkdir -p "${SCRATCH_DIR}"
rm -rf "${SCRATCH_DIR:?}"/*
pushd "${SCRATCH_DIR}"

build_reporting_tool
setup_x509_limbo

REPORTS_DIR="${SRC_ROOT}/x509-limbo-reports"
mkdir -p "${REPORTS_DIR}"

# Build run x509-limbo on current src of event
build_aws_lc "${SRC_ROOT}" "/opt/aws-lc-after"
AFTER_HARNESS="$(build_aws_lc_harness "/opt/aws-lc-after")"
run_aws_lc_harness "${AFTER_HARNESS}"
"${SCRATCH_DIR}/limbo-report" annotate "${X509_LIMBO_SRC}/limbo.json" "${X509_LIMBO_SRC}/results/aws-lc.json" > "${REPORTS_DIR}/base.json"
"${SCRATCH_DIR}/limbo-report" annotate -csv "${X509_LIMBO_SRC}/limbo.json" "${X509_LIMBO_SRC}/results/aws-lc.json" > "${REPORTS_DIR}/base.csv"

# Build run x509-limbo on the base src for event
build_aws_lc "${BASE_COMMIT_SRC}" "/opt/aws-lc-before"
BEFORE_HARNESS="$(build_aws_lc_harness "/opt/aws-lc-before")"
run_aws_lc_harness "${BEFORE_HARNESS}"
"${SCRATCH_DIR}/limbo-report" annotate "${X509_LIMBO_SRC}/limbo.json" "${X509_LIMBO_SRC}/results/aws-lc.json" > "${REPORTS_DIR}/changes.json"
"${SCRATCH_DIR}/limbo-report" annotate -csv "${X509_LIMBO_SRC}/limbo.json" "${X509_LIMBO_SRC}/results/aws-lc.json" > "${REPORTS_DIR}/changes.csv"

# Produce diff report
set +e
"${SCRATCH_DIR}/limbo-report" diff "${REPORTS_DIR}/base.json" "${REPORTS_DIR}/changes.json" | tee "${REPORTS_DIR}/summary.txt"
DIFF_RET_STATUS=${PIPESTATUS[0]}

set -e
popd # "${SCRATCH_DIR}"
rm -rf "${SCRATCH_DIR:?}"

if [ $DIFF_RET_STATUS -eq 0 ]; then
    exit 0
else
    exit 1
fi
