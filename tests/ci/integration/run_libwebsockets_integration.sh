#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#    - SCRATCH_FOLDER
#      - SOCKET_SRC_FOLDER
#      - AWS_LC_BUILD_FOLDER
#      - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SRC_ROOT}/SOCKETS_BUILD_ROOT"

SOCKET_TEST_PATCH_FOLDER="${SRC_ROOT}/tests/ci/integration/libwebsockets_patch"
SOCKET_SRC_FOLDER="${SCRATCH_FOLDER}/libwebsockets"
SOCKET_DEST_DIR="${SOCKET_SRC_FOLDER}/destdir"
SOCKET_BUILD_DIR="${SOCKET_SRC_FOLDER}/build"

AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

function libwebsockets_patch() {
  patchfile="${SOCKET_TEST_PATCH_FOLDER}/libwebsocket_master.patch"
  echo "Apply patch $patchfile..."
  patch -p1 --quiet -i "$patchfile"
}

function libwebsockets_build() {
  mkdir $SOCKET_BUILD_DIR $SOCKET_DEST_DIR
  export LD_LIBRARY_PATH="${SOCKET_DEST_DIR}/usr/local/share/libwebsockets-test-server/plugins:${SOCKET_DEST_DIR}/usr/local/lib:${AWS_LC_INSTALL_FOLDER}/lib"

  pushd $SOCKET_BUILD_DIR
  cmake .. -DLWS_WITH_AWSLC=1 -DLWS_WITH_SS_TESTS_HTTP_ONLY=0 -DLWS_OPENSSL_INCLUDE_DIRS="${AWS_LC_INSTALL_FOLDER}/include" -DLWS_OPENSSL_LIBRARIES="${AWS_LC_INSTALL_FOLDER}/lib/libssl.so;${AWS_LC_INSTALL_FOLDER}/lib/libcrypto.so" -DLWS_WITH_MINIMAL_EXAMPLES=1
  make -j && make -j DESTDIR=${SOCKET_DEST_DIR} install

  local socket_lib="${SOCKET_DEST_DIR}/usr/local/lib/libwebsockets.so"
  ${AWS_LC_BUILD_FOLDER}/check-linkage.sh ${socket_lib} crypto || exit 1
}

function libwebsockets_test() {
  pushd $SOCKET_BUILD_DIR
  ctest -j --output-on-failure
}

git clone https://github.com/warmcat/libwebsockets.git ${SOCKET_SRC_FOLDER}
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DCMAKE_INSTALL_LIBDIR=lib -DBUILD_TESTING=OFF -DCMAKE_BUILD_TYPE=Debug -DBUILD_SHARED_LIBS=1

# Build latest tag from source.
pushd ${SOCKET_SRC_FOLDER}
LATEST_TAG=$(git tag -l | grep -E "^v[0-9]+\.[0-9]+\.[0-9]+$" | sort -V | tail -n 1)
git checkout $LATEST_TAG
echo "Using libwebsockets version: ${LATEST_TAG}"

libwebsockets_patch
libwebsockets_build
libwebsockets_test

popd
