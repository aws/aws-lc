#!/bin/bash -exu
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#    - SCRATCH_FOLDER
#      - bind9
#      - AWS_LC_BUILD_FOLDER
#      - AWS_LC_INSTALL_FOLDER
#      - BIND9_BUILD_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SRC_ROOT}/BIND9_BUILD_ROOT"
BIND9_SRC_FOLDER="${SCRATCH_FOLDER}/bind9"
BIND9_BUILD_FOLDER="${SCRATCH_FOLDER}/bind9-aws-lc"
BIND9_PATCH_FOLDER=${SRC_ROOT}/"tests/ci/integration/bind9_patch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

function bind9_build() {
  autoreconf -fi  
  PKG_CONFIG_PATH="${AWS_LC_INSTALL_FOLDER}/lib/pkgconfig" ./configure --with-openssl="${AWS_LC_INSTALL_FOLDER}" --enable-dnstap --enable-dnsrps --with-cmocka --with-libxml2 --enable-leak-detection
  make -j ${NUM_CPU_THREADS} -k all
}

# TODO: Remove this when we make an upstream contribution.
function bind9_patch() {
  for patchfile in $(find -L "${BIND9_PATCH_FOLDER}" -type f -name '*.patch'); do
    echo "Apply patch $patchfile..."
    patch -p1 --quiet -i "$patchfile"
  done
}

function bind9_run_tests() {
  make -j ${NUM_CPU_THREADS} check
}

mkdir -p ${SCRATCH_FOLDER}
rm -rf ${SCRATCH_FOLDER}/*
cd ${SCRATCH_FOLDER}

git clone https://gitlab.isc.org/isc-projects/bind9.git ${BIND9_SRC_FOLDER} --depth 1
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${BIND9_BUILD_FOLDER}
ls

aws_lc_build ${SRC_ROOT} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} -DBUILD_TESTING=OFF

# Build bind9 from source.
pushd ${BIND9_SRC_FOLDER}

bind9_patch
bind9_build
bind9_run_tests
popd

