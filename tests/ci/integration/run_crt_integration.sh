#!/usr/bin/env bash
set -exu
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SYS_ROOT}/SCRATCH_AWSLC_CRT_TEST

# Make script execution idempotent.
mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

git clone --recursive https://github.com/awslabs/aws-crt-cpp.git

cd aws-crt-cpp
# The CRT has a submodule for AWS-LC, overwrite that with the local version
rm -rf crt/aws-lc/*
cp -r ${SRC_ROOT}/* crt/aws-lc/

# Don't pre-build AWS-LC, the CRT will build all of it's dependencies how it wants them built
mkdir build && cd build
${CMAKE_COMMAND} -GNinja ../
ninja
ninja test
