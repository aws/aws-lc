#!/bin/bash -exu
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#    - SCRATCH_FOLDER
#      - monit
#      - AWS_LC_BUILD_FOLDER
#      - AWS_LC_INSTALL_FOLDER
#      - MONIT_BUILD_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SRC_ROOT}/MONIT_BUILD_ROOT"
MONIT_SRC_FOLDER="${SCRATCH_FOLDER}/monit"
MONIT_BUILD_FOLDER="${SCRATCH_FOLDER}/monit-aws-lc"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

function monit_build() {
  ./bootstrap  
  ./configure --with-ssl-static="${AWS_LC_INSTALL_FOLDER}"
  make -j ${NUM_CPU_THREADS}
}

# Monit doesn't run any tests verifying ssl behavior, but it shouldn't hurt to run the brief tests.
function monit_run_tests() {
  pushd libmonit
  # TimeTest will fail on a machine not in CET timezone.
  # https://bitbucket.org/tildeslash/monit/src/def6b462259586358be3c86d76a299c80744df39/libmonit/test/TimeTest.c#lines-24
  sed -i 's/TimeTest && //g' test/test.sh
  make verify
  popd
}

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

git clone https://bitbucket.org/tildeslash/monit.git ${MONIT_SRC_FOLDER} --depth 1
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${MONIT_BUILD_FOLDER}
ls

aws_lc_build ${SRC_ROOT} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} -DBUILD_TESTING=OFF

# Build monit from source.
pushd ${MONIT_SRC_FOLDER}

monit_build
monit_run_tests
popd

