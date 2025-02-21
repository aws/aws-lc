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
X509_LIMBO_SRC="${SCRATCH_DIR}/x509-limbo"
BASE_COMMIT_SRC="${SYS_ROOT}/base-src"

# If BASE_REF is set in the environment we will use that, this provides a mechanism for a user to manually kick off
# a job via the CodeBuild console (otherwise CodeBuild won't let your override variables prefixed with CODEBUILD_).
# Otherwise if CODEBUILD_WEBHOOK_BASE_REF is set we use (this would be in the case of pull requests).
# Lastly if that isn't set then we fallback to CODEBUILD_WEBHOOK_PREV_COMMIT which will be set for a push event.
# If none of those are set the script will fail here.
BASE_REF="${BASE_REF:-${CODEBUILD_WEBHOOK_BASE_REF:-${CODEBUILD_WEBHOOK_PREV_COMMIT:?}}}"

function build_reporting_tool() {
    pushd "${X509_CI_DIR}/limbo-report"
    make
    mv ./limbo-report "${SCRATCH_DIR}/"
    popd # "${X509_CI_DIR}/limbo-report"
}

function setup_x509_limbo() {
    git clone https://github.com/C2SP/x509-limbo.git "${X509_LIMBO_SRC}"
    pushd "${X509_LIMBO_SRC}"
    patch -p1 -i "${X509_CI_DIR}/x509-limbo.patch"
    python3 -m venv .venv
    source .venv/bin/activate
    pip install -e .
    popd # "${X509_LIMBO_SRC}"
}

function run_aws_lc_harness() {
    pushd "${X509_LIMBO_SRC}"
    set +e
    AWS_LC_SRC_DIR="${1}" make test-aws-lc
    if [ ! -f "${X509_LIMBO_SRC}/results/aws-lc.json" ]; then
        echo "Failed to run x509-limbo harness for AWS_LC_SRC_DIR=${1}"
        exit 1
    fi
    set -e
    popd # "${X509_LIMBO_SRC}"
}

# Log Docker hub limit https://docs.docker.com/docker-hub/download-rate-limit/#how-can-i-check-my-current-rate
TOKEN=$(curl "https://auth.docker.io/token?service=registry.docker.io&scope=repository:ratelimitpreview/test:pull" | jq -r .token)
curl --head -H "Authorization: Bearer $TOKEN" https://registry-1.docker.io/v2/ratelimitpreview/test/manifests/latest

git worktree add "${BASE_COMMIT_SRC}" "${BASE_REF:?}"

mkdir -p "${SCRATCH_DIR}"
rm -rf "${SCRATCH_DIR:?}"/*
pushd "${SCRATCH_DIR}"

build_reporting_tool
setup_x509_limbo

REPORTS_DIR="${SRC_ROOT}/x509-limbo-reports"
mkdir -p "${REPORTS_DIR}"

# Build run x509-limbo on current src of event
run_aws_lc_harness "${SRC_ROOT}"
"${SCRATCH_DIR}/limbo-report" annotate "${X509_LIMBO_SRC}/limbo.json" "${X509_LIMBO_SRC}/results/aws-lc.json" > "${REPORTS_DIR}/base.json"
"${SCRATCH_DIR}/limbo-report" annotate -csv "${X509_LIMBO_SRC}/limbo.json" "${X509_LIMBO_SRC}/results/aws-lc.json" > "${REPORTS_DIR}/base.csv"

# Build run x509-limbo on the base src for event
run_aws_lc_harness "${BASE_COMMIT_SRC}"
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
