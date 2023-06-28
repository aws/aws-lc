#!/bin/bash -exu
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

trap dump_log EXIT

MYSQL_VERSION_TAG="mysql-8.0.33"
# This directory is specific to the docker image used. Use -DDOWNLOAD_BOOST=1 -DWITH_BOOST=<directory>
# with mySQL to download a compatible boost version locally.
BOOST_INSTALL_FOLDER=/home/dependencies/boost

# Set up environment.

# SYS_ROOT
#  |
#  - SRC_ROOT(aws-lc)
#  |
#  - SCRATCH_FOLDER
#    |
#    - mysql
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER
#    - MYSQL_BUILD_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SYS_ROOT}/"MYSQL_BUILD_ROOT"
MYSQL_SRC_FOLDER="${SCRATCH_FOLDER}/mysql-server"
MYSQL_BUILD_FOLDER="${SCRATCH_FOLDER}/mysql-aws-lc"
MYSQL_PATCH_FOLDER=${SRC_ROOT}/"tests/ci/integration/mysql_patch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${MYSQL_SRC_FOLDER}/aws-lc-install"


mkdir -p ${SCRATCH_FOLDER}
rm -rf ${SCRATCH_FOLDER}/*
cd ${SCRATCH_FOLDER}

function mysql_patch_reminder() {
  LATEST_MYSQL_VERSION_TAG=mysql-`curl https://api.github.com/repos/mysql/mysql-server/tags | jq '.[].name' |grep '\-8.0' |sed -e 's/"mysql-cluster-\(.*\)"/\1/' |sort | tail -n 1`
  if [[ "${LATEST_MYSQL_VERSION_TAG}" != "${MYSQL_VERSION_TAG}" ]]; then
    aws cloudwatch put-metric-data --namespace AWS-LC --metric-name MySQLVersionMismatch --value 1
  else
    aws cloudwatch put-metric-data --namespace AWS-LC --metric-name MySQLVersionMismatch --value 0
  fi
}

function mysql_build() {
  cmake ${MYSQL_SRC_FOLDER} -GNinja -DENABLED_PROFILING=OFF -DWITH_NDB_JAVA=OFF  -DWITH_BOOST=${BOOST_INSTALL_FOLDER} -DWITH_SSL=${AWS_LC_INSTALL_FOLDER} "-B${MYSQL_BUILD_FOLDER}"
  ninja -C ${MYSQL_BUILD_FOLDER}
  ls -R ${MYSQL_BUILD_FOLDER}
}

function mysql_run_tests() {
  pushd ${MYSQL_BUILD_FOLDER}
  ninja test
  popd
}

# Used to access debugging logs.
function dump_log() {
  ls ${MYSQL_BUILD_FOLDER}/Testing/Temporary/LastTest.log
  for logfile in $(find -L "${MYSQL_BUILD_FOLDER}/Testing/Temporary" -type f -name '*.log'); do
    echo "Dumping out logs to observe:"
    cat $logfile
  done
}

# MySQL tests expect the OpenSSL style of error messages. We patch this to expect AWS-LC's style.
# TODO: Remove this when we make an upstream contribution.
function mysql_patch_error_strings() {
  MYSQL_TEST_FILES=("test_routing_splicer.cc" "test_http_server.cc")
  MYSQL_ERROR_STRING=("certificate verify failed" "no start line" "ee key too small")
  AWS_LC_EXPECTED_ERROR_STRING=("CERTIFICATE_VERIFY_FAILED" "NO_START_LINE" "key-size too small")
  for file in "${MYSQL_TEST_FILES[@]}"; do
    for i in "${!MYSQL_ERROR_STRING[@]}"; do
      find ./ -type f -name "$file" | xargs sed -i -e "s|${MYSQL_ERROR_STRING[$i]}|${AWS_LC_EXPECTED_ERROR_STRING[$i]}|g"
    done
  done
}

# MySQL relies on some behaviour that AWS-LC intentionally does not provide support for. Some of these known gaps are listed below:
# * DH cipher suites in libssl
# * Stateful session resumption
function mysql_patch_tests() {
  for patchfile in $(find -L "${MYSQL_PATCH_FOLDER}" -type f -name '*.patch'); do
    echo "Apply patch $patchfile..."
    patch -p1 --quiet -i "$patchfile"
  done
}

# Get latest MySQL version. MySQL often updates with large changes depending on OpenSSL all at once, so we pin to a specific version.
#mysql_patch_reminder
git clone https://github.com/mysql/mysql-server.git ${MYSQL_SRC_FOLDER} -b ${MYSQL_VERSION_TAG} --depth 1
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${MYSQL_BUILD_FOLDER}
ls

aws_lc_build ${SRC_ROOT} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
pushd ${MYSQL_SRC_FOLDER}
mysql_patch_tests
mysql_patch_error_strings
mysql_build
mysql_run_tests
popd
