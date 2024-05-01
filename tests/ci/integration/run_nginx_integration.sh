#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#    - SCRATCH_FOLDER
#      - nginx
#      - AWS_LC_BUILD_FOLDER
#      - AWS_LC_INSTALL_FOLDER
#      - NGINX_BUILD_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SRC_ROOT}/NGINX_BUILD_ROOT"
NGINX_SRC_FOLDER="${SCRATCH_FOLDER}/nginx"
NGINX_TEST_FOLDER="${SCRATCH_FOLDER}/nginx-tests"
NGINX_BUILD_FOLDER="${SCRATCH_FOLDER}/nginx-aws-lc"
NGINX_PATCH_BUILD_FOLDER="${SRC_ROOT}/tests/ci/integration/nginx_patch"
NGINX_PATCH_TEST_FOLDER="${SRC_ROOT}/tests/ci/integration/nginx_tests_patch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${NGINX_SRC_FOLDER}/aws-lc-install"


mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

function nginx_build() {
  ./auto/configure --prefix="${NGINX_BUILD_FOLDER}" \
    --with-http_ssl_module \
    --with-http_v2_module \
    --with-http_v3_module \
    --with-stream \
    --with-stream_realip_module \
    --with-stream_ssl_module \
    --with-stream_ssl_preread_module \
    --with-mail \
    --with-mail_ssl_module \
    --with-cc-opt="-I${AWS_LC_INSTALL_FOLDER}/include" \
    --with-ld-opt="-L${AWS_LC_INSTALL_FOLDER}/lib"
  make -j "$NUM_CPU_THREADS" install
  ls -R ${NGINX_BUILD_FOLDER}
}

function nginx_run_tests() {
  TEST_NGINX_BINARY="${NGINX_BUILD_FOLDER}/sbin/nginx" prove .
}

# TODO: Remove this when we make an upstream contribution.
function nginx_patch_build() {
  for patchfile in $(find -L "${NGINX_PATCH_BUILD_FOLDER}" -type f -name '*.patch'); do
    echo "Apply patch $patchfile..."
    patch -p1 --quiet -i "$patchfile"
  done
}

# There are some features in nginx that we don't currently support. The known gaps are:
# * SSL_Conf Command
# * Stateful session resumption (Session Caches)
function nginx_patch_tests() {
  for patchfile in $(find -L "${NGINX_PATCH_TEST_FOLDER}" -type f -name '*.patch'); do
    echo "Apply patch $patchfile..."
    patch -p1 --quiet -i "$patchfile"
  done
  # http_listen.t tries to open port 8182, but this port isn't available within the
  # docker container from CI configurations. This isn't related to ssl functionality, so
  # we skip/remove it.
  rm http_listen.t
}

git clone https://github.com/nginx/nginx.git ${NGINX_SRC_FOLDER} --depth 1
git clone https://github.com/nginx/nginx-tests.git ${NGINX_TEST_FOLDER} --depth 1
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${NGINX_BUILD_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=0

# Build nginx from source.
pushd ${NGINX_SRC_FOLDER}
nginx_patch_build
nginx_build
popd

# Run against nginx unit tests.
pushd ${NGINX_TEST_FOLDER}
nginx_patch_tests
nginx_run_tests
popd
