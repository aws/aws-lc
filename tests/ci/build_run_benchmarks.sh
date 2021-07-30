#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# run this from the bm_framework root directory!
OPENSSL_ROOT=$(pwd)/openssl
BORINGSSL_ROOT=$(pwd)/boringssl
AWSLC_PR_ROOT=$(pwd)/aws-lc-pr
AWSLC_PROD_ROOT=$(pwd)/aws-lc-prod

# build OpenSSL
mkdir openssl/build
(cd openssl && ./config --prefix="${OPENSSL_ROOT}"/build --openssldir="${OPENSSL_ROOT}"/build)
make -C openssl
make install -C openssl

# build BoringSSL
mkdir boringssl/build
cmake -Bboringssl/build -Hboringssl -GNinja -DCMAKE_BUILD_TYPE=Release
ninja -C boringssl/build

# build AWSLC pr
mkdir aws-lc-pr/build
cmake -Baws-lc-pr/build -Haws-lc-pr -GNinja -DCMAKE_BUILD_TYPE=Release \
  -DAWSLC_INSTALL_DIR="${AWSLC_PR_ROOT}" \
  -DBORINGSSL_INSTALL_DIR="${BORINGSSL_ROOT}" \
  -DOPENSSL_INSTALL_DIR="${OPENSSL_ROOT}"
ninja -C aws-lc-pr/build

# build FIPS compliant version of AWSLC pr
mkdir aws-lc-pr/fips_build
cmake -Baws-lc-pr/fips_build -Haws-lc-pr -GNinja -DFIPS=1 -DCMAKE_BUILD_TYPE=Release -DAWSLC_INSTALL_DIR="${AWSLC_PR_ROOT}"
ninja -C aws-lc-pr/fips_build

# build AWSLC prod
mkdir aws-lc-prod/build
cmake -Baws-lc-prod/build -Haws-lc-prod -GNinja -DCMAKE_BUILD_TYPE=Release -DAWSLC_INSTALL_DIR="${AWSLC_PROD_ROOT}"
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

taskset -c 4 ./aws-lc-pr/build/tool/ossl_bm -timeout 3 -json > ossl_bm.json &
ossl_pid=$!
taskset -c 5 ./aws-lc-pr/build/tool/bssl_bm -timeout 3 -json > bssl_bm.json &
bssl_pid=$!

# wait for benchmarks to finish
wait "${pr_pid}"
wait "${pr_fips_pid}"
wait "${prod_pid}"
wait "${prod_fips_pid}"
wait "${ossl_pid}"
wait "${bssl_pid}"

# convert results from .json to .csv
python3 aws-lc-pr/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-pr_bm.json
python3 aws-lc-pr/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-pr_fips_bm.json
python3 aws-lc-pr/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-prod_bm.json
python3 aws-lc-pr/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-prod_fips_bm.json
python3 aws-lc-pr/tests/ci/benchmark_framework/convert_json_to_csv.py ossl_bm.json
python3 aws-lc-pr/tests/ci/benchmark_framework/convert_json_to_csv.py bssl_bm.json

# check for regressions!
python3 aws-lc-pr/tests/ci/benchmark_framework/compare_results.py aws-lc-prod_bm.csv aws-lc-pr_bm.csv prod_vs_pr.csv
prod_vs_pr_code="$?"
python3 aws-lc-pr/tests/ci/benchmark_framework/compare_results.py aws-lc-prod_bm.csv aws-lc-pr_fips_bm.csv aws-lc-prod_fips_bm.csv prod_vs_pr_fips.csv
prod_vs_pr_fips_code="$?"
python3 aws-lc-pr/tests/ci/benchmark_framework/compare_results.py ossl_bm.csv aws-lc-pr_bm.csv ossl_vs_pr.csv
ossl_vs_pr_code="$?"
python3 aws-lc-pr/tests/ci/benchmark_framework/compare_results.py bssl_bm.csv aws-lc-pr_bm.csv bssl_vs_pr.csv
bssl_vs_pr_code="$?"

# upload results to s3
aws s3 cp aws-lc-pr_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-pr-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-aws-lc-pr_bm.csv"
aws s3 cp aws-lc-pr_fips_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-pr-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-aws-lc-pr_fips_bm.csv"
aws s3 cp aws-lc-prod_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-prod-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-aws-lc-prod_bm.csv"
aws s3 cp aws-lc-prod_fips_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-prod-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-aws-lc-prod_fips_bm.csv"
aws s3 cp ossl_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-prod-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-ossl_bm.csv"
aws s3 cp bssl_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-prod-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-bssl_bm.csv"

# upload results to lastest folders in s3
aws s3 mv aws-lc-pr_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-pr-bucket/latest/${CPU_TYPE}${NOHW_TYPE}-aws-lc-pr_bm.csv"
aws s3 mv aws-lc-pr_fips_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-pr-bucket/latest/${CPU_TYPE}${NOHW_TYPE}-aws-lc-pr_fips_bm.csv"
aws s3 mv aws-lc-prod_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-prod-bucket/latest/${CPU_TYPE}${NOHW_TYPE}-aws-lc-prod_bm.csv"
aws s3 mv aws-lc-prod_fips_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-prod-bucket/latest/${CPU_TYPE}${NOHW_TYPE}-aws-lc-prod_fips_bm.csv"
aws s3 mv ossl_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-prod-bucket/latest/${CPU_TYPE}${NOHW_TYPE}-ossl_bm.csv"
aws s3 mv bssl_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-prod-bucket/latest/${CPU_TYPE}${NOHW_TYPE}-bssl_bm.csv"

# if any of the results gave an exit code of 5, there's a performance regression
exit_fail=false
if [ "${prod_vs_pr_code}" = 5 ]; then
  aws s3 cp prod_vs_pr.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-pr-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-prod_vs_pr.csv"
  aws s3 mv prod_vs_pr.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-pr-bucket/latest/${CPU_TYPE}${NOHW_TYPE}-prod_vs_pr.csv"
  exit_fail=true
fi
if [ "${prod_vs_pr_fips_code}" = 5 ]; then
  aws s3 cp prod_vs_pr_fips.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-pr-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-prod_vs_pr_fips.csv"
  aws s3 mv prod_vs_pr_fips.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-pr-bucket/latest/${CPU_TYPE}${NOHW_TYPE}-prod_vs_pr_fips.csv"
  exit_fail=true
fi
if [ "${ossl_vs_pr_code}" = 5 ]; then
  aws s3 cp ossl_vs_pr.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-pr-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-ossl_vs_pr.csv"
  aws s3 mv ossl_vs_pr.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-pr-bucket/latest/${CPU_TYPE}${NOHW_TYPE}-ossl_vs_pr.csv"
  exit_fail=true
fi
if [ "${bssl_vs_pr_code}" = 5 ]; then
  aws s3 cp bssl_vs_pr.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-pr-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-bssl_vs_pr.csv"
  aws s3 mv bssl_vs_pr.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-bm-framework-pr-bucket/latest/${CPU_TYPE}${NOHW_TYPE}-bssl_vs_pr.csv"
  exit_fail=true
fi

if [ "${exit_fail}" = true ]; then
  exit 1
fi
