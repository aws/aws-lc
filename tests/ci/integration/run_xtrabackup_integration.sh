#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

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
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER
#    - XTRABACKUP_BUILD_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SYS_ROOT}/"XTRABACKUP_BUILD_ROOT"
XTRABACKUP_SRC_FOLDER="${SCRATCH_FOLDER}/percona-xtrabackup"
XTRABACKUP_BUILD_FOLDER="${SCRATCH_FOLDER}/xtrabackup-aws-lc"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${XTRABACKUP_SRC_FOLDER}/aws-lc-install"

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

function xtrabackup_build() {
  cmake ${XTRABACKUP_SRC_FOLDER} -GNinja -DWITH_SSL=system -DCMAKE_PREFIX_PATH=${AWS_LC_INSTALL_FOLDER} "-B${XTRABACKUP_BUILD_FOLDER}" -DCMAKE_BUILD_TYPE=RelWithDebInfo
  time ninja -C ${XTRABACKUP_BUILD_FOLDER}
  ls -R ${XTRABACKUP_BUILD_FOLDER}
}

git clone --recurse-submodules https://github.com/percona/percona-xtrabackup.git ${XTRABACKUP_SRC_FOLDER} --depth 1
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${XTRABACKUP_BUILD_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1

pushd ${XTRABACKUP_SRC_FOLDER}
xtrabackup_build
popd

ldd "${XTRABACKUP_BUILD_FOLDER}/bin/xtrabackup" | grep "${AWS_LC_INSTALL_FOLDER}/lib/libcrypto.so" || exit 1
ldd "${XTRABACKUP_BUILD_FOLDER}/bin/xtrabackup" | grep "${AWS_LC_INSTALL_FOLDER}/lib/libssl.so" || exit 1
