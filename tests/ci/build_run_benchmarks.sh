#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# run this from the bm_framework root directory!
AWSLC_PR_ROOT=$(pwd)/aws-lc-pr
AWSLC_PROD_ROOT=$(pwd)/aws-lc-prod

# build AWSLC pr
mkdir aws-lc-pr/build
cmake -Baws-lc-pr/build -Haws-lc-pr -GNinja -DCMAKE_BUILD_TYPE=Release -DAWSLC_INSTALL_DIR="${AWSLC_PR_ROOT}"
ninja -C aws-lc-pr/build

# build FIPS compliant version of AWSLC pr
mkdir aws-lc-pr/fips_build
cmake -Baws-lc-pr/fips_build -Haws-lc-pr -GNinja -DFIPS=1 -DCMAKE_BUILD_TYPE=Release -DAWSLC_INSTALL_DIR="${AWSLC_PR_ROOT}"
ninja -C aws-lc-pr/fips_build

# build AWSLC prod
mkdir aws-lc-prod/build
cmake -Baws-lc-prod/build -Haws-lc-pr -GNinja -DCMAKE_BUILD_TYPE=Release -DAWSLC_INSTALL_DIR="${AWSLC_PROD_ROOT}"
ninja -C aws-lc-prod/build

#build FIPS compliant version of AWSLC prod
mkdir aws-lc-prod/fips_build
cmake -Baws-lc-prod/fips_build -Haws-lc-prod -GNinja -DFIPS=1 -DCMAKE_BUILD_TYPE=Release -DAWSLC_INSTALL_DIR="${AWSLC_PROD_ROOT}"
ninja -C aws-lc-prod/fips_build

# run the generated benchmarks and wait for them to finish
taskset -c 0 ./aws-lc-pr/build/tool/awslc_bm -timeout 3 -json > aws-lc-pr_bm.json &
pr_pid=$!
taskset -c 1 ./aws-lc-pr/fips_build/tool/awslc_bm -timeout 3 -json > aws-lc-pr_fips_bm.json &
pr_fips_pid=$!

taskset -c 2 ./aws-lc-prod/build/tool/awslc_bm -timeout 3 -json > aws-lc-prod_bm.json &
prod_pid=$!
taskset -c 3 ./aws-lc-prod/fips_build/tool/awslc_bm -timeout 3 -json > aws-lc-prod_fips_bm.json &
prod_fips_pid=$!

# wait for benchmarks to finish
wait "${pr_pid}"
wait "${pr_fips_pid}"
wait "${prod_pid}"
wait "${prod_fips_pid}"

# upload results to s3
aws s3 mv aws-lc-pr_bm.json s3://"${AWS_ACCOUNT_ID}"-aws-lc-bm-framework-pr-bucket/"${COMMIT_ID}"/aws-lc-pr_bm.json
aws s3 mv aws-lc-pr_fips_bm.json s3://"${AWS_ACCOUNT_ID}"-aws-lc-bm-framework-pr-bucket/"${COMMIT_ID}"/aws-lc-pr_fips_bm.json
aws s3 mv aws-lc-prod_bm.json s3://"${AWS_ACCOUNT_ID}"-aws-lc-bm-framework-prod-bucket/"${COMMIT_ID}"/aws-lc-prod_bm.json
aws s3 mv aws-lc-prod_fips_bm.json s3://"${AWS_ACCOUNT_ID}"-aws-lc-bm-framework-prod-bucket/"${COMMIT_ID}"/aws-lc-prod_fips_bm.json
