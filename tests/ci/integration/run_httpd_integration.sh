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
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
HTTPD_PATCH_FOLDER="${SCRIPT_DIR}/httpd_patch"
SCRATCH_FOLDER=${SYS_ROOT}/"HTTPD_BUILD_ROOT"
HTTPD_SRC_FOLDER="${SCRATCH_FOLDER}/httpd"
HTTPD_INSTALL_FOLDER="${SCRATCH_FOLDER}/httpd-install"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${HTTPD_SRC_FOLDER}/aws-lc-install"

HTTPD_TAG="2.4.65"

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

# Dependencies: Ubuntu
if [ "$(id -u)" -eq 0 ]; then
  apt update
  apt install -y libpcre2-dev libnghttp2-dev nghttp2-client zlib1g-dev libtool-bin libxml2-dev pebble python3-venv
fi

function httpd_patch() {
  patch -p1 --quiet -i ${HTTPD_PATCH_FOLDER}/${HTTPD_TAG}/*
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
  python3 -m pip install pyopenssl websockets pytest filelock python-multipart
}

function httpd_run_tests() {
  export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"
  source venv/bin/activate
  python3 -m pytest test -k "not TestSslRenegotiation and not test_md_"
}


# Clone httpd and APR
git clone https://github.com/apache/httpd.git ${HTTPD_SRC_FOLDER} --depth 1
cd ${HTTPD_SRC_FOLDER}
git fetch --tags origin
git checkout -b branch-for-${HTTPD_TAG} ${HTTPD_TAG}
git clone https://github.com/apache/apr.git srclib/apr --depth 1

mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${HTTPD_INSTALL_FOLDER}

# Build AWS-LC
aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=0

# Build httpd from source
pushd ${HTTPD_SRC_FOLDER}
httpd_patch
httpd_build
popd

# Ensure it linked to AWS-LC
nm --defined-only ${HTTPD_INSTALL_FOLDER}/bin/httpd | grep -q awslc_version_string

# Setup Python environment and run tests
pushd ${HTTPD_SRC_FOLDER}
setup_python_env
httpd_run_tests
popd
