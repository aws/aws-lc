#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  |
#  - SRC_ROOT(aws-lc)
#  |
#  - SCRATCH_FOLDER
#    |
#    - httpd
#    - httpd-install
#    - aws-lc-build
#    - aws-lc-install

# Assumes script is executed from the root of aws-lc directory
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
HTTPD_PATCH_FOLDER="${SCRIPT_DIR}/httpd_patch"

SCRATCH_FOLDER=${SYS_ROOT}/"SCRATCH-httpd-integ"
HTTPD_SRC_FOLDER="${SCRATCH_FOLDER}/httpd"
HTTPD_INSTALL_FOLDER="${SCRATCH_FOLDER}/httpd-install"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

if [ $# -eq 0 ]; then
  # Use tag "2.4.65" if none specified
  HTTPD_TAGS=("2.4.65")
else
  HTTPD_TAGS=("$@")
fi

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

# Dependencies: Ubuntu
if [ "$(id -u)" -eq 0 ]; then
  apt update
  apt install -y libpcre2-dev libnghttp2-dev nghttp2-client zlib1g-dev libtool-bin libxml2-dev pebble python3-venv
fi

function run_httpd_test() {
  local HTTPD_TAG=$1
  echo "Running httpd integration test for tag: ${HTTPD_TAG}"

  # Clean up previous build
  rm -rf "${HTTPD_SRC_FOLDER:?}" "${HTTPD_INSTALL_FOLDER:?}"
  mkdir -p "${HTTPD_INSTALL_FOLDER}"

  # Clone httpd and APR
  git clone https://github.com/apache/httpd.git "${HTTPD_SRC_FOLDER}" --depth 1
  cd "${HTTPD_SRC_FOLDER}"
  git fetch --tags origin
  git checkout -b branch-for-${HTTPD_TAG} ${HTTPD_TAG}
  git clone https://github.com/apache/apr.git srclib/apr --depth 1

  # Build httpd from source
  pushd "${HTTPD_SRC_FOLDER}"
  httpd_patch
  httpd_build

  # Ensure httpd is linked to AWS-LC
  nm --defined-only "${HTTPD_INSTALL_FOLDER}/bin/httpd" | grep -q awslc_version_string

  # Setup Python environment and run tests
  setup_python_env
  httpd_run_tests
  popd

  cd ${SCRATCH_FOLDER}
}

function httpd_patch() {
  # if the directory exists
  if [ -d "${HTTPD_PATCH_FOLDER}/${HTTPD_TAG}" ]; then
    patch -p1 --quiet -i "${HTTPD_PATCH_FOLDER}/${HTTPD_TAG}"/*
  else
    echo "No patches found for httpd tag: '${HTTPD_TAG}'"
  fi
}

function httpd_build() {
  ./buildconf
  ./configure \
    "CFLAGS=-I/usr/include/libxml2" \
    --prefix="${HTTPD_INSTALL_FOLDER}" \
    --with-included-apr \
    --with-ssl="${AWS_LC_INSTALL_FOLDER}" \
    --enable-mpms-shared="all" \
    --enable-mods-shared="most" \
    --with-libxml2=/usr \
    --enable-mods-static="access_compat actions alias asis authn_core authz_core autoindex cgi deflate dir env expires filter headers include log_config mime negotiation proxy proxy_http proxy_http2 remoteip rewrite setenvif slotmem_shm ssl status unixd version"
  make -j "$NUM_CPU_THREADS"
  make install
}

function setup_python_env() {
  python3 -m venv venv
  source venv/bin/activate
  python3 -m pip install --upgrade pip
  python3 -m pip install pyopenssl websockets "pytest<7.0" filelock python-multipart
}

function httpd_run_tests() {
  source venv/bin/activate
  # Disabled tests:
  # * Tests relating to TLS renegotiation -- This feature is disabled by default in AWS-LC.
  # * Tests relating to mod_md -- not built
  # * "test_h2_106_02" had intermittent failures
  #    -- The test ignores exit status 55 (CURL_SEND_ERROR), but fails when it's 56 (CURL_RECV_ERROR). It should ignore both.
  #       There seems to be a subtle behavioral difference here between OpenSSL and AWS-LC.
  python3 -m pytest test -k "not TestSslRenegotiation and not test_md_ and not test_h2_106_02"
}

# Static build for AWS-LC
aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=0

# Run tests for each tag
for HTTPD_TAG in "${HTTPD_TAGS[@]}"; do
  run_httpd_test "$HTTPD_TAG"
done
