#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

trap dump_log EXIT

# Set up environment.

# SYS_ROOT
#  |
#  - SRC_ROOT(aws-lc)
#  |
#  - SCRATCH_FOLDER
#    |
#    - mariadb
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER
#    - MARIADB_BUILD_FOLDER

# The CFlags, skipped test list, and patches were taken from the internal CI pipeline of our customer.

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SYS_ROOT}/"MARIADB_BUILD_ROOT"
MARIADB_SRC_FOLDER="${SCRATCH_FOLDER}/server"
MARIADB_BUILD_FOLDER="${SCRATCH_FOLDER}/server/mariadb-aws-lc"
MARIADB_PATCH_FOLDER=${SRC_ROOT}/"tests/ci/integration/mariadb_patch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${MARIADB_SRC_FOLDER}/aws-lc-install"

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

function mariadb_build() {
  cmake ${MARIADB_SRC_FOLDER} -GNinja -DWITH_SSL=system -DOPENSSL_ROOT_DIR=${AWS_LC_INSTALL_FOLDER} "-B${MARIADB_BUILD_FOLDER}" -DPLUGIN_COLUMNSTORE=NO -DPLUGIN_ROCKSDB=NO -DPLUGIN_S3=NO -DPLUGIN_MROONGA=NO -DPLUGIN_CONNECT=NO -DPLUGIN_SPHINX=NO -DPLUGIN_SPIDER=NO -DPLUGIN_TOKUDB=NO -DWITH_WSREP=OFF
  ninja -C ${MARIADB_BUILD_FOLDER}
  ls -R ${MARIADB_BUILD_FOLDER}
}

# Used to access debugging logs.
function dump_log() {
  ls ${MARIADB_BUILD_FOLDER}/mysql-test/var/log
  for logfile in $(find -L "${MARIADB_BUILD_FOLDER}/mysql-test/var/log" -type f -name '*.log'); do
    echo "Dumping out logs to observe:"
    cat $logfile
  done
}

function mariadb_run_tests() {
  pushd ${MARIADB_BUILD_FOLDER}/mysql-test
  # More complicated integration tests. mtr expects to be launched in-place and with write access to it's own directories
  #
  # main.plugin_load passes, but is skipped over since it generates a warning when we run the script in Codebuild. Warnings will cause
  # a failure in MariaDB's test runs, unless --nowarnings is turned on. The warning is not reproducible in Gitlab's CI or any local
  # container runs. This test isn't relevant to AWS-LC integration so we skip over the Codebuild specific issue for now.
  echo "main.mysqldump : Field separator argument is not what is expected; check the manual when executing 'SELECT INTO OUTFILE'
main.flush_logs_not_windows : query 'flush logs' succeeded - should have failed with error ER_CANT_CREATE_FILE (1004)
main.mysql_upgrade_noengine : upgrade output order does not match the expected
main.plugin_load : This test generates a warning in Codebuild. Skip over since this isn't relevant to AWS-LC.
main.desc_index_min_max : This test is flaky and unrelated to aws-lc.
"> skiplist
  ./mtr --suite=main --force --parallel=auto --skip-test-list=${MARIADB_BUILD_FOLDER}/mysql-test/skiplist --retry-failure=2
  popd
}

# TODO: Remove this when we make an upstream contribution.
function mariadb_patch() {
  for patchfile in $(find -L "${MARIADB_PATCH_FOLDER}" -type f -name '*.patch'); do
    echo "Apply patch $patchfile..."
    patch -p1 --quiet -i "$patchfile"
  done
}

# Get latest mariadb version, we can pin to a specific version if MariaDB's code changes break us too often.
git clone https://github.com/MariaDB/server.git ${MARIADB_SRC_FOLDER} --depth 1
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${MARIADB_BUILD_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=0
pushd ${MARIADB_SRC_FOLDER}
mariadb_patch
mariadb_build
mariadb_run_tests
popd

