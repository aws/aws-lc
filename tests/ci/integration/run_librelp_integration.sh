#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#    - SCRATCH_FOLDER
#      - librelp
#      - AWS_LC_BUILD_FOLDER
#      - AWS_LC_INSTALL_FOLDER
#      - LIBRELP_BUILD_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SRC_ROOT}/LIBRELP_BUILD_ROOT"
LIBRELP_SRC_FOLDER="${SCRATCH_FOLDER}/librelp"
LIBRELP_BUILD_FOLDER="${SCRATCH_FOLDER}/librelp-aws-lc"
LIBRELP_PATCH_BUILD_FOLDER="${SRC_ROOT}/tests/ci/integration/librelp_patch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

function librelp_build() {
  autoreconf -fi  
  PKG_CONFIG_PATH="${AWS_LC_INSTALL_FOLDER}/lib/pkgconfig" ./configure --enable-tls-openssl
  make -j ${NUM_CPU_THREADS}
}

function librelp_run_tests() {
  export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"
  make -j "$NUM_CPU_THREADS" check
}

# TODO: Remove this when we make an upstream contribution.
function librelp_patch_build() {
  for patchfile in $(find -L "${LIBRELP_PATCH_BUILD_FOLDER}" -type f -name '*.patch'); do
    echo "Apply patch $patchfile..."
    patch -p1 --quiet -i "$patchfile"
  done
}

mkdir -p ${SCRATCH_FOLDER}
rm -rf ${SCRATCH_FOLDER}/*
cd ${SCRATCH_FOLDER}

git clone https://github.com/rsyslog/librelp.git ${LIBRELP_SRC_FOLDER} --depth 1
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${LIBRELP_BUILD_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1

# Build librelp from source.
pushd ${LIBRELP_SRC_FOLDER}

librelp_patch_build
librelp_build
librelp_run_tests

popd

${AWS_LC_BUILD_FOLDER}/check-linkage.sh "${LIBRELP_SRC_FOLDER}/src/.libs/librelp.so" crypto || exit 1
${AWS_LC_BUILD_FOLDER}/check-linkage.sh "${LIBRELP_SRC_FOLDER}/src/.libs/librelp.so" ssl || exit 1
