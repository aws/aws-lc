#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#    - SCRATCH_FOLDER
#      - XMLSEC_SRC_FOLDER
#      - AWS_LC_BUILD_FOLDER
#      - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SRC_ROOT}/XMLSEC_BUILD_ROOT"
XMLSEC_SRC_FOLDER="${SCRATCH_FOLDER}/xmlsec"
XMLSEC_SRC_FOLDER_BUILD_PREFIX="${XMLSEC_SRC_FOLDER}/build/install"
XMLSEC_SRC_FOLDER_BUILD_EPREFIX="${XMLSEC_SRC_FOLDER}/build/exec-install"
XMLSEC_PATCH_FOLDER="${SRC_ROOT}/tests/ci/integration/xmlsec_patch"

AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

function xmlsec_build() {

  export OPENSSL_CFLAGS="-I${AWS_LC_INSTALL_FOLDER}/include"
  export OPENSSL_LIBS="-L${AWS_LC_INSTALL_FOLDER}/lib -lssl -lcrypto"
  export LD_FLAGS="-Wl,-rpath=${AWS_LC_INSTALL_FOLDER}/lib"

  ./autogen.sh --prefix="$XMLSEC_SRC_FOLDER_BUILD_PREFIX" \
              --exec-prefix="$XMLSEC_SRC_FOLDER_BUILD_EPREFIX"

  make -j install

  local xmlsec_executable="${XMLSEC_SRC_FOLDER}/build/exec-install/lib/libxmlsec1-openssl.so"
  ldd ${xmlsec_executable} \
    | grep "${AWS_LC_INSTALL_FOLDER}/lib/libcrypto.so" || exit 1
}

function xmlsec_patch() {
  patchfile="${XMLSEC_PATCH_FOLDER}/xmlsec_master.patch"
  echo "Apply patch $patchfile..."
  patch -p1 --quiet -i "$patchfile"
}

function xmlsec_run_tests() {
  make check
}

git clone https://github.com/lsh123/xmlsec.git ${XMLSEC_SRC_FOLDER}
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=Debug -DBUILD_SHARED_LIBS=1

# Build xmlsec from source.
pushd ${XMLSEC_SRC_FOLDER}
xmlsec_patch
xmlsec_build
xmlsec_run_tests
