#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# run this from the AWSLC root directory!

AWSLC_ROOT=$(pwd)

# build AWSLC
mkdir build
cmake -Bbuild -H. -GNinja -DCMAKE_BUILD_TYPE=Release -DAWSLC_INSTALL_DIR="${AWSLC_ROOT}"
ninja -C build

# build FIPS compliant version of AWSLC
mkdir fips_build
cmake -Bfips_build -H. -GNinja -DFIPS=1 -DCMAKE_BUILD_TYPE=Release -DAWSLC_INSTALL_DIR="${AWSLC_ROOT}"
ninja -C fips_build

# run the generated benchmarks and wait for them to finish
taskset -c 0 ./build/tool/awslc_bm -timeout 3 -json > aws-lc_prod_bm.json &
prod_pid=$!
taskset -c 1 ./fips_build/tool/awslc_bm -timeout 3 -json > aws-lc_prod_fips_bm.json &
prod_fips_pid=$!

# wait for benchmarks to
wait "${prod_pid}"
wait "${prod_fips_pid}"

# upload results to s3
aws s3 mv aws-lc_prod_bm.json s3://"${AWS_ACCOUNT_ID}"-aws-lc-bm-framework-pr-bucket/"${COMMIT_ID}"/aws-lc_prod_bm.json
aws s3 mv aws-lc_prod_fips_bm.json s3://"${AWS_ACCOUNT_ID}"-aws-lc-bm-framework-pr-bucket/"${COMMIT_ID}"/aws-lc_prod_fips_bm.json
