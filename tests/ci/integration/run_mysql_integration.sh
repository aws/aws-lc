#!/bin/bash -exu
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

MYSQL_VERSION_TAG="mysql-8.0.33"
# This directory is specific to the docker image used. Use -DDOWNLOAD_BOOST=1 -DWITH_BOOST=<directory>
# with mySQL to download a compatible boost version locally.
BOOST_INSTALL_FOLDER=/home/dependencies/boost

# Set up environment.

# ROOT
#  |
#  - AWS_LC_DIR
#    |
#    - aws-lc
#  |
#  - SCRATCH_FOLDER
#    |
#    - mysql
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER
#    - MYSQL_BUILD_FOLDER

# Assumes script is executed from the root of aws-lc directory
AWS_LC_DIR=$(pwd)
cd ../
ROOT=$(pwd)

SCRATCH_FOLDER=${ROOT}/"MYSQL_BUILD_ROOT"
MYSQL_SRC_FOLDER="${SCRATCH_FOLDER}/mysql-server"
MYSQL_BUILD_FOLDER="${SCRATCH_FOLDER}/server/mysql-aws-lc"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${MYSQL_SRC_FOLDER}/aws-lc-install"

mkdir -p ${SCRATCH_FOLDER}
rm -rf ${SCRATCH_FOLDER}/*
cd ${SCRATCH_FOLDER}

function aws_lc_build() {
  ${CMAKE_COMMAND} "${AWS_LC_DIR}" -GNinja "-B${AWS_LC_BUILD_FOLDER}" "-DCMAKE_INSTALL_PREFIX=${AWS_LC_INSTALL_FOLDER}" "$@"
  ninja -C "${AWS_LC_BUILD_FOLDER}" install
  ls -R "${AWS_LC_INSTALL_FOLDER}"
  rm -rf "${AWS_LC_BUILD_FOLDER:?}"/*
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

# Get latest MySQL version. MySQL often updates with large changes depending on OpenSSL all at once, so we pin to a specific version.
git clone https://github.com/mysql/mysql-server.git ${MYSQL_SRC_FOLDER} -b ${MYSQL_VERSION_TAG} --depth 1
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${MYSQL_BUILD_FOLDER}
ls

aws_lc_build
pushd ${MYSQL_SRC_FOLDER}
mysql_build
# TODO: There are still pending test failures that need to be resolved. Turn this on once we resolve them.
# mysql_run_tests
popd
