#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -x

# set default value of directory name
if [ -z "${PR_FOLDER_NAME}" ]; then export PR_FOLDER_NAME=aws-lc; fi

# run this from the bm_framework root directory!
OPENSSL_ROOT=$(pwd)/openssl
BORINGSSL_ROOT=$(pwd)/boringssl
AWSLC_PR_ROOT=$(pwd)/"${PR_FOLDER_NAME}"
AWSLC_PROD_ROOT=$(pwd)/aws-lc-prod

# clone the various repositories we need (we already have aws-lc-pr since we need it to run this script)
git clone https://github.com/awslabs/aws-lc.git aws-lc-prod
git clone https://boringssl.googlesource.com/boringssl
git clone --branch OpenSSL_1_1_1-stable https://github.com/openssl/openssl.git

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
mkdir "${PR_FOLDER_NAME}"/build
cmake -B"${PR_FOLDER_NAME}"/build -H"${PR_FOLDER_NAME}" -GNinja -DCMAKE_BUILD_TYPE=Release \
  -DAWSLC_INSTALL_DIR="${AWSLC_PR_ROOT}" \
  -DBORINGSSL_INSTALL_DIR="${BORINGSSL_ROOT}" \
  -DOPENSSL_INSTALL_DIR="${OPENSSL_ROOT}"
ninja -C "${PR_FOLDER_NAME}"/build

# build FIPS compliant version of AWSLC pr
mkdir "${PR_FOLDER_NAME}"/fips_build
cmake -B"${PR_FOLDER_NAME}"/fips_build -H"${PR_FOLDER_NAME}" -GNinja -DFIPS=1 -DCMAKE_BUILD_TYPE=Release -DAWSLC_INSTALL_DIR="${AWSLC_PR_ROOT}"
ninja -C "${PR_FOLDER_NAME}"/fips_build

# build AWSLC prod
mkdir aws-lc-prod/build
cmake -Baws-lc-prod/build -Haws-lc-prod -GNinja -DCMAKE_BUILD_TYPE=Release -DAWSLC_INSTALL_DIR="${AWSLC_PROD_ROOT}"
ninja -C aws-lc-prod/build

#build FIPS compliant version of AWSLC prod
mkdir aws-lc-prod/fips_build
cmake -Baws-lc-prod/fips_build -Haws-lc-prod -GNinja -DFIPS=1 -DCMAKE_BUILD_TYPE=Release -DAWSLC_INSTALL_DIR="${AWSLC_PROD_ROOT}"
ninja -C aws-lc-prod/fips_build

# avoid cpus 0-3 since there are a lot of other things running on them
# we have a lot of cpus to spare so we can just go from cpu 4 onwards until a better solution is found
# run the generated benchmarks and wait for them to finish
taskset -c 4 ./"${PR_FOLDER_NAME}"/build/tool/awslc_bm -timeout 3 -json > aws-lc-pr_bm.json &
pr_pid=$!
taskset -c 5 ./"${PR_FOLDER_NAME}"/fips_build/tool/awslc_bm -timeout 3 -json > aws-lc-pr_fips_bm.json &
pr_fips_pid=$!

taskset -c 6 ./aws-lc-prod/build/tool/awslc_bm -timeout 3 -json > aws-lc-prod_bm.json &
prod_pid=$!
taskset -c 7 ./aws-lc-prod/fips_build/tool/awslc_bm -timeout 3 -json > aws-lc-prod_fips_bm.json &
prod_fips_pid=$!

taskset -c 8 ./"${PR_FOLDER_NAME}"/build/tool/ossl_bm -timeout 3 -json > ossl_bm.json &
ossl_pid=$!
taskset -c 9 ./"${PR_FOLDER_NAME}"/build/tool/bssl_bm -timeout 3 -json > bssl_bm.json &
bssl_pid=$!

# wait for benchmarks to finish
wait "${pr_pid}"
wait "${pr_fips_pid}"
wait "${prod_pid}"
wait "${prod_fips_pid}"
wait "${ossl_pid}"
wait "${bssl_pid}"

# once all those are done, we want to run the trusttoken benchmarks sequentially
# (running them in parallel caused severe bias problems)
taskset -c 4 ./"${PR_FOLDER_NAME}"/build/tool/awslc_bm -filter trusttoken -timeout 3 -json > aws-lc-pr_tt_bm.json
taskset -c 5 ./"${PR_FOLDER_NAME}"/fips_build/tool/awslc_bm -filter trusttoken -timeout 3 -json > aws-lc-pr_tt_fips_bm.json
taskset -c 6 ./aws-lc-prod/build/tool/awslc_bm -filter trusttoken -timeout 3 -json > aws-lc-prod_tt_bm.json
taskset -c 7 ./aws-lc-prod/fips_build/tool/awslc_bm -filter trusttoken -timeout 3 -json > aws-lc-prod_tt_fips_bm.json
taskset -c 8 ./"${PR_FOLDER_NAME}"/build/tool/ossl_bm -filter trusttoken -timeout 3 -json > ossl_tt_bm.json
taskset -c 9 ./"${PR_FOLDER_NAME}"/build/tool/bssl_bm -filter trusttoken -timeout 3 -json > bssl_tt_bm.json

# convert results from .json to .csv
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-pr_bm.json
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-pr_fips_bm.json
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-prod_bm.json
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-prod_fips_bm.json
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py ossl_bm.json
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py bssl_bm.json

python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-pr_tt_bm.json
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-pr_tt_fips_bm.json
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-prod_tt_bm.json
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py aws-lc-prod_tt_fips_bm.json
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py ossl_tt_bm.json
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/convert_json_to_csv.py bssl_tt_bm.json

# once we have csvs, we want to update the main benchmark results files with the sequential trusttoken results
# files will be updated in place
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/update_results.py aws-lc-pr_bm.csv aws-lc-pr_tt_bm.csv
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/update_results.py aws-lc-pr_fips_bm.csv aws-lc-pr_tt_fips_bm.csv
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/update_results.py aws-lc-prod_bm.csv aws-lc-prod_tt_bm.csv
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/update_results.py aws-lc-prod_fips_bm.csv aws-lc-prod_tt_fips_bm.csv
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/update_results.py ossl_bm.csv ossl_tt_bm.csv
python3 "${PR_FOLDER_NAME}"/tests/ci/benchmark_framework/update_results.py bssl_bm.csv bssl_tt_bm.csv

# check for regressions!
python3 aws-lc-pr/tests/ci/benchmark_framework/compare_results.py aws-lc-prod_bm.csv aws-lc-pr_bm.csv prod_vs_pr.csv
prod_vs_pr_code="$?"
python3 aws-lc-pr/tests/ci/benchmark_framework/compare_results.py aws-lc-prod_fips_bm.csv aws-lc-pr_fips_bm.csv prod_vs_pr_fips.csv
prod_vs_pr_fips_code="$?"
python3 aws-lc-pr/tests/ci/benchmark_framework/compare_results.py ossl_bm.csv aws-lc-pr_bm.csv ossl_vs_pr.csv
ossl_vs_pr_code="$?"
python3 aws-lc-pr/tests/ci/benchmark_framework/compare_results.py bssl_bm.csv aws-lc-pr_bm.csv bssl_vs_pr.csv
bssl_vs_pr_code="$?"

# upload results to s3
aws s3 cp aws-lc-pr_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-aws-lc-pr_bm.csv"
aws s3 cp aws-lc-pr_fips_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-aws-lc-pr_fips_bm.csv"
aws s3 cp aws-lc-prod_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-prod-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-aws-lc-prod_bm.csv"
aws s3 cp aws-lc-prod_fips_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-prod-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-aws-lc-prod_fips_bm.csv"
aws s3 cp ossl_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-prod-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-ossl_bm.csv"
aws s3 cp bssl_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-prod-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-bssl_bm.csv"

# upload results to lastest folders in s3
aws s3 mv aws-lc-pr_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/latest-${PR_NUM}/${CPU_TYPE}${NOHW_TYPE}-aws-lc-pr_bm.csv"
aws s3 mv aws-lc-pr_fips_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/latest-${PR_NUM}/${CPU_TYPE}${NOHW_TYPE}-aws-lc-pr_fips_bm.csv"
aws s3 mv aws-lc-prod_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-prod-bucket/latest/${CPU_TYPE}${NOHW_TYPE}-aws-lc-prod_bm.csv"
aws s3 mv aws-lc-prod_fips_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-prod-bucket/latest/${CPU_TYPE}${NOHW_TYPE}-aws-lc-prod_fips_bm.csv"
aws s3 mv ossl_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-prod-bucket/latest/${CPU_TYPE}${NOHW_TYPE}-ossl_bm.csv"
aws s3 mv bssl_bm.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-prod-bucket/latest/${CPU_TYPE}${NOHW_TYPE}-bssl_bm.csv"

# if any of the results gave an exit code of 5, there's a performance regression
# we only want to actually fail the vote if we've detected a regression in the pr version of aws-lc and tip of main of aws-lc (for fips and non-fips)
exit_fail=false
if [ "${prod_vs_pr_code}" != 0 ]; then
  aws s3 cp prod_vs_pr.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-prod_vs_pr.csv"
  aws s3 mv prod_vs_pr.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/latest-${PR_NUM}/${CPU_TYPE}${NOHW_TYPE}-prod_vs_pr.csv"
  exit_fail=true
fi
if [ "${prod_vs_pr_fips_code}" != 0 ]; then
  aws s3 cp prod_vs_pr_fips.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-prod_vs_pr_fips.csv"
  aws s3 mv prod_vs_pr_fips.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/latest-${PR_NUM}/${CPU_TYPE}${NOHW_TYPE}-prod_vs_pr_fips.csv"
  exit_fail=true
fi
if [ "${ossl_vs_pr_code}" != 0 ]; then
  aws s3 cp ossl_vs_pr.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-ossl_vs_pr.csv"
  aws s3 mv ossl_vs_pr.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/latest-${PR_NUM}/${CPU_TYPE}${NOHW_TYPE}-ossl_vs_pr.csv"
fi
if [ "${bssl_vs_pr_code}" != 0 ]; then
  aws s3 cp bssl_vs_pr.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/${COMMIT_ID}/${CPU_TYPE}${NOHW_TYPE}-bssl_vs_pr.csv"
  aws s3 mv bssl_vs_pr.csv s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/latest-${PR_NUM}/${CPU_TYPE}${NOHW_TYPE}-bssl_vs_pr.csv"
fi

if [ "${exit_fail}" = true ]; then
  exit 1
fi
