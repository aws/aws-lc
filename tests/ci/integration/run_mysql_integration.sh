#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

MYSQL_VERSION_TAG="mysql-cluster-9.3.0"
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
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

function mysql_patch_reminder() {
  # Check latest MySQL version. MySQL often updates with large changes depending on OpenSSL all at once, so we pin to a specific version.
  LATEST_MYSQL_VERSION_TAG=`git tag --sort=-taggerdate | tail -1`
  if [[ "${LATEST_MYSQL_VERSION_TAG}" != "${MYSQL_VERSION_TAG}" ]]; then
    aws cloudwatch put-metric-data --namespace AWS-LC --metric-name MySQLVersionMismatch --value 1
  else
    aws cloudwatch put-metric-data --namespace AWS-LC --metric-name MySQLVersionMismatch --value 0
  fi
}

function mysql_build() {
  cmake ${MYSQL_SRC_FOLDER} -GNinja -DWITH_SSL=system -DCMAKE_PREFIX_PATH=${AWS_LC_INSTALL_FOLDER} "-B${MYSQL_BUILD_FOLDER}" -DCMAKE_BUILD_TYPE=RelWithDebInfo
  time ninja -C ${MYSQL_BUILD_FOLDER}
  ls -R ${MYSQL_BUILD_FOLDER}
}

function mysql_run_tests() {
  pushd ${MYSQL_BUILD_FOLDER}/mysql-test
  # More complicated integration tests. mtr expects to be launched in-place and with write access to it's own directories.
  #
  # Tests marked with Bug#0000 are tests that have are known to fail in containerized environments. These tests aren't exactly relevant
  # to testing AWS-LC functionality.
  # Tests marked with Bug#0001 use stateful session resumption, otherwise known as session caching. It is known that AWS-LC does not
  # currently support this with TLS 1.3.
  echo "main.restart_server : Bug#0000 mysqld is not managed by supervisor process
main.udf_bug35242734 : Bug#0000 mysqld is not managed by supervisor process
main.file_contents : Bug#0000 Cannot open 'INFO_SRC' in ''
main.resource_group_thr_prio_unsupported : Bug#0000 Invalid thread priority value -5
main.mysqld_daemon : Bug#0000 failed, error: 256, status: 1, errno: 2.
main.mysqld_safe : Bug#0000 nonexistent: No such file or directory
main.grant_user_lock : Bug#0000 Access denied for user root at localhost
main.persisted_variables_bugs_fast : Bug#0000 Unsure
main.mysqldump : Bug#0000 contains nonaggregated column
main.func_math : Bug#0000 should have failed with errno 1690
main.derived_condition_pushdown : Bug#0000 Fails with OpenSSL as well. Not relevant to AWS-LC.
main.client_ssl_data_print  : Bug#0001 AWS-LC does not support Stateful session resumption (Session Caching).
main.ssl_cache : Bug#0001 AWS-LC does not support Stateful session resumption (Session Caching).
main.ssl_cache_tls13 : Bug#0001 AWS-LC does not support Stateful session resumption (Session Caching).
main.mysql_client_test : Bug#0002 test_wl13075:No TLS 1.3 resumption with AWS-LC SSL_get_session(CryptoAlg-2773)
"> skiplist
  ./mtr --suite=main --force --parallel=auto --skip-test-list=${MYSQL_BUILD_FOLDER}/mysql-test/skiplist --retry-failure=5 --retry=5 --report-unstable-tests --max-test-fail=30
  popd
}

# MySQL tests expect the OpenSSL style of error messages. We patch this to expect AWS-LC's style.
# These are checked as part of mySQL's unit tests, but we don't actually run them in our CI. They are known to be flaky
# within docker containers. The mtr tests are much more robust and run full server test suites that actually do TLS
# connections end-to-end.
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

git clone https://github.com/mysql/mysql-server.git ${MYSQL_SRC_FOLDER} --depth 1  --no-single-branch
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${MYSQL_BUILD_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1

pushd ${MYSQL_SRC_FOLDER}

mysql_patch_reminder
git checkout ${MYSQL_VERSION_TAG}

mysql_patch_tests
mysql_patch_error_strings

mysql_build
if [ $(uname -p) != "aarch64" ]; then
  # MySQL's tests use extensive resources. They are slow on ARM and flaky race conditions occur.
  # TODO: Enable ARM testing when Codebuild releases a larger ARM type (Current Type: 16vCPU, 32GB).
  mysql_run_tests
fi

popd

ldd "${MYSQL_BUILD_FOLDER}/lib/libmysqlclient.so" | grep "${AWS_LC_INSTALL_FOLDER}/lib/libcrypto.so" || exit 1
ldd "${MYSQL_BUILD_FOLDER}/lib/libmysqlclient.so" | grep "${AWS_LC_INSTALL_FOLDER}/lib/libssl.so" || exit 1
ldd "${MYSQL_BUILD_FOLDER}/lib/libmysqlharness_tls.so" | grep "${AWS_LC_INSTALL_FOLDER}/lib/libcrypto.so" || exit 1
ldd "${MYSQL_BUILD_FOLDER}/lib/libmysqlharness_tls.so" | grep "${AWS_LC_INSTALL_FOLDER}/lib/libssl.so" || exit 1
ldd "${MYSQL_BUILD_FOLDER}/lib/libmysqlrouter_routing.so" | grep "${AWS_LC_INSTALL_FOLDER}/lib/libcrypto.so" || exit 1
ldd "${MYSQL_BUILD_FOLDER}/lib/libmysqlrouter_routing.so" | grep "${AWS_LC_INSTALL_FOLDER}/lib/libssl.so" || exit 1
ldd "${MYSQL_BUILD_FOLDER}/lib/libmysqlrouter_http.so" | grep "${AWS_LC_INSTALL_FOLDER}/lib/libcrypto.so" || exit 1
