#!/bin/bash -exu
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

# Set up environment.

# ROOT
#  |
#  - AWS_LC_DIR
#    |
#    - aws-lc
#  |
#  - SCRATCH_FOLDER
#    |
#    - mariadb
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER
#    - MARIADB_BUILD_FOLDER

# The CFlags, skipped test list, and patches were taken from the internal CI pipeline of our customer.

# Assumes script is executed from the root of aws-lc directory
AWS_LC_DIR=$(pwd)
cd ../
ROOT=$(pwd)

SCRATCH_FOLDER=${ROOT}/"MARIADB_BUILD_ROOT"
MARIADB_SRC_FOLDER="${SCRATCH_FOLDER}/server"
MARIADB_BUILD_FOLDER="${SCRATCH_FOLDER}/server/mariadb-aws-lc"
MARIADB_PATCH_FOLDER=${AWS_LC_DIR}/"tests/ci/integration/mariadb_patch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${MARIADB_SRC_FOLDER}/aws-lc-install"

mkdir -p ${SCRATCH_FOLDER}
rm -rf ${SCRATCH_FOLDER}/*
cd ${SCRATCH_FOLDER}

function mariadb_build() {
  cmake ${MARIADB_SRC_FOLDER} -GNinja -DWITH_SSL=${AWS_LC_INSTALL_FOLDER} "-B${MARIADB_BUILD_FOLDER}" -DPLUGIN_COLUMNSTORE=NO -DPLUGIN_ROCKSDB=NO -DPLUGIN_S3=NO -DPLUGIN_MROONGA=NO -DPLUGIN_CONNECT=NO -DPLUGIN_SPHINX=NO -DPLUGIN_SPIDER=NO -DPLUGIN_TOKUDB=NO -DPLUGIN_PERFSCHEMA=NO -DWITH_WSREP=OFF
  ninja -C ${MARIADB_BUILD_FOLDER}
  ls -R ${MARIADB_BUILD_FOLDER}
}

function mariadb_run_tests() {
  pushd ${MARIADB_BUILD_FOLDER}
  # More complicated integration tests. mtr expects to be launched in-place and with write access to it's own directories
  pushd mysql-test
  echo "main.mysqldump : Field separator argument is not what is expected; check the manual when executing 'SELECT INTO OUTFILE'
main.flush_logs_not_windows : query 'flush logs' succeeded - should have failed with error ER_CANT_CREATE_FILE (1004)
main.mysql_upgrade_noengine : upgrade output order does not match the expected" > skiplist
  ./mtr --suite=main --force --parallel=auto --skip-test-list=${MARIADB_BUILD_FOLDER}/mysql-test/skiplist --force-restart
  cat var/log
  popd
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

aws_lc_build ${AWS_LC_DIR} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
pushd ${MARIADB_SRC_FOLDER}
mariadb_patch
mariadb_build
mariadb_run_tests
popd

