#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

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
if [ -v CODEBUILD_SRC_DIR ]; then
  SCRATCH_FOLDER="${CODEBUILD_SCRIPT_DIR}/BIND9_BUILD_ROOT" # /codebuild/output/tmp/BIND9_BUILD_ROOT
else
  SCRATCH_FOLDER="${SRC_ROOT}/BIND9_BUILD_ROOT"
fi
BIND9_SRC_FOLDER="${SCRATCH_FOLDER}/bind9"
BIND9_BUILD_FOLDER="${SCRATCH_FOLDER}/bind9-aws-lc"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

function bind9_build() {
  #dnsrps was removed since bind9 9.21.2
  meson setup "$BIND9_BUILD_FOLDER" \
    --pkg-config-path="${AWS_LC_INSTALL_FOLDER}/lib/pkgconfig" \
    --libdir=lib \
    -Ddnstap=enabled \
    -Dcmocka=enabled \
    -Dstats-xml=enabled \
    -Dleak-detection=enabled \
    -Djemalloc=disabled \
    -Dtracing=disabled

  meson compile -C "$BIND9_BUILD_FOLDER"
  "$BIND9_BUILD_FOLDER"/named -V

  ninja -C "$BIND9_BUILD_FOLDER" -j "$NUM_CPU_THREADS" all
}

function bind9_run_tests() {
  # use ninja over meson test for better logging
  ninja -C "$BIND9_BUILD_FOLDER" -j "$NUM_CPU_THREADS" test
}

mkdir -p ${SCRATCH_FOLDER}
rm -rf ${SCRATCH_FOLDER}/*
cd ${SCRATCH_FOLDER}

git clone https://gitlab.isc.org/isc-projects/bind9.git ${BIND9_SRC_FOLDER} --depth 1
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${BIND9_BUILD_FOLDER}
ls

aws_lc_build ${SRC_ROOT} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DBUILD_SHARED_LIBS=1
export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"

# Build bind9 from source.
pushd ${BIND9_SRC_FOLDER}

bind9_build
bind9_run_tests

# Iterate through all of bind's vended artifacts.
for libname in dns ns isc isccc isccfg; do
  ${AWS_LC_BUILD_FOLDER}/check-linkage.sh "${BIND9_BUILD_FOLDER}/lib${libname}.so" crypto || exit 1
  ${AWS_LC_BUILD_FOLDER}/check-linkage.sh "${BIND9_BUILD_FOLDER}/lib${libname}.so" ssl || exit 1
done

popd
