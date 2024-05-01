#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -x

# set default value of directory name
if [ -z "${PR_FOLDER_NAME}" ]; then export PR_FOLDER_NAME=aws-lc; fi

# Get AWS_ACCOUNT_ID
if [ -z "${AWS_ACCOUNT_ID}" ]; then AWS_ACCOUNT_ID=$(aws sts get-caller-identity --query Account --output text); fi

AWSLC_PR_ROOT=$(pwd)

cd ..

# run this from the bm_framework root directory!
AWSLC_PR_ROOT=$(pwd)/"${PR_FOLDER_NAME}"
AWSLC_PROD_ROOT=$(pwd)/aws-lc-prod

source ${AWSLC_PR_ROOT}/tests/ci/common_posix_setup.sh

# clone the various repositories we need (we already have aws-lc-pr since we need it to run this script)
git clone https://github.com/aws/aws-lc.git aws-lc-prod

# build AWSLC pr
mkdir -p "${PR_FOLDER_NAME}"/build
${CMAKE_COMMAND} -B"${PR_FOLDER_NAME}"/build -H"${PR_FOLDER_NAME}" -GNinja -DCMAKE_BUILD_TYPE=Release \
  -DBUILD_TESTING=OFF
ninja -C "${PR_FOLDER_NAME}"/build

# build FIPS compliant version of AWSLC pr
mkdir -p "${PR_FOLDER_NAME}"/fips_build
${CMAKE_COMMAND} -B"${PR_FOLDER_NAME}"/fips_build -H"${PR_FOLDER_NAME}" -GNinja -DFIPS=1 -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=TRUE
ninja -C "${PR_FOLDER_NAME}"/fips_build

# build AWSLC prod
mkdir -p aws-lc-prod/build
${CMAKE_COMMAND} -Baws-lc-prod/build -Haws-lc-prod -GNinja -DCMAKE_BUILD_TYPE=Release -DBUILD_TESTING=OFF
ninja -C aws-lc-prod/build

#build FIPS compliant version of AWSLC prod
mkdir -p aws-lc-prod/fips_build
${CMAKE_COMMAND} -Baws-lc-prod/fips_build -Haws-lc-prod -GNinja -DFIPS=1 -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=TRUE
ninja -C aws-lc-prod/fips_build

./"${PR_FOLDER_NAME}"/build/tool/bssl speed -timeout 1 -json > aws-lc-pr_bm.json
./"${PR_FOLDER_NAME}"/fips_build/tool/bssl speed -timeout 1 -json > aws-lc-pr_fips_bm.json

./aws-lc-prod/build/tool/bssl speed -timeout 1 -json > aws-lc-prod_bm.json
./aws-lc-prod/fips_build/tool/bssl speed -timeout 1 -json > aws-lc-prod_fips_bm.json


./"${PR_FOLDER_NAME}"/build/tool/bssl speed -filter trusttoken -timeout 1 -json > aws-lc-pr_tt_bm.json
./"${PR_FOLDER_NAME}"/fips_build/tool/bssl speed -filter trusttoken -timeout 1 -json > aws-lc-pr_tt_fips_bm.json
./aws-lc-prod/build/tool/bssl speed -filter trusttoken -timeout 1 -json > aws-lc-prod_tt_bm.json
./aws-lc-prod/fips_build/tool/bssl speed -filter trusttoken -timeout 1 -json > aws-lc-prod_tt_fips_bm.json

# convert results from .json to .csv
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-pr_bm.json
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-pr_fips_bm.json
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-prod_bm.json
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-prod_fips_bm.json

python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-pr_tt_bm.json
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-pr_tt_fips_bm.json
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-prod_tt_bm.json
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-prod_tt_fips_bm.json

# once we have csvs, we want to update the main benchmark results files with the sequential trusttoken results
# files will be updated in place
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/update_results.py aws-lc-pr_bm.csv aws-lc-pr_tt_bm.csv python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/update_results.py aws-lc-pr_fips_bm.csv aws-lc-pr_tt_fips_bm.csv python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/update_results.py aws-lc-prod_bm.csv aws-lc-prod_tt_bm.csv python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/update_results.py aws-lc-prod_fips_bm.csv aws-lc-prod_tt_fips_bm.csv

# check for regressions!
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/compare_results.py aws-lc-prod_bm.csv aws-lc-pr_bm.csv prod_vs_pr.csv
prod_vs_pr_code="$?"
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/compare_results.py aws-lc-prod_fips_bm.csv aws-lc-pr_fips_bm.csv prod_vs_pr_fips.csv
prod_vs_pr_fips_code="$?"

# upload results to s3
aws s3 cp aws-lc-pr_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/${CODEBUILD_SOURCE_VERSION}/aws-lc-pr_bm.csv"
aws s3 cp aws-lc-pr_fips_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/${CODEBUILD_SOURCE_VERSION}/aws-lc-pr_fips_bm.csv"
aws s3 cp aws-lc-prod_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-prod-bucket/${CODEBUILD_SOURCE_VERSION}/aws-lc-prod_bm.csv"
aws s3 cp aws-lc-prod_fips_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-prod-bucket/${CODEBUILD_SOURCE_VERSION}/aws-lc-prod_fips_bm.csv"

# upload results to lastest folders in s3
aws s3 mv aws-lc-pr_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/latest-${CODEBUILD_WEBHOOK_TRIGGER}/aws-lc-pr_bm.csv"
aws s3 mv aws-lc-pr_fips_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/latest-${CODEBUILD_WEBHOOK_TRIGGER}/aws-lc-pr_fips_bm.csv"
aws s3 mv aws-lc-prod_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-prod-bucket/latest/aws-lc-prod_bm.csv"
aws s3 mv aws-lc-prod_fips_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-prod-bucket/latest/aws-lc-prod_fips_bm.csv"

# if any of the results gave an exit code of 5, there's a performance regression
# we only want to actually fail the vote if we've detected a regression in the pr version of aws-lc and tip of main of aws-lc (for fips and non-fips)
exit_fail=false
if [ "${prod_vs_pr_code}" != 0 ]; then
  aws s3 cp prod_vs_pr.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/${CODEBUILD_SOURCE_VERSION}/prod_vs_pr.csv"
  aws s3 mv prod_vs_pr.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/latest-${CODEBUILD_WEBHOOK_TRIGGER}/prod_vs_pr.csv"
  exit_fail=true
fi
if [ "${prod_vs_pr_fips_code}" != 0 ]; then
  aws s3 cp prod_vs_pr_fips.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/${CODEBUILD_SOURCE_VERSION}/prod_vs_pr_fips.csv"
  aws s3 mv prod_vs_pr_fips.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/latest-${CODEBUILD_WEBHOOK_TRIGGER}/prod_vs_pr_fips.csv"
  exit_fail=true
fi

if [ "${exit_fail}" = true ]; then
  exit 1
fi
