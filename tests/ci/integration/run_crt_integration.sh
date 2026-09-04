#!/usr/bin/env bash
set -exu
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SYS_ROOT}/SCRATCH_AWSLC_CRT_TEST
CRT_SRC_FOLDER="${SCRATCH_FOLDER}/aws-crt-cpp"

# Make script execution idempotent.
mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

git clone --recursive https://github.com/awslabs/aws-crt-cpp.git "${CRT_SRC_FOLDER}"
record_repo_commit "${CRT_SRC_FOLDER}"

cd "${CRT_SRC_FOLDER}"
# The CRT has a submodule for AWS-LC, overwrite that with the local version
rm -rf crt/aws-lc/*
cp -r ${SRC_ROOT}/* crt/aws-lc/

# Don't pre-build AWS-LC, the CRT will build all of it's dependencies how it wants them built
mkdir build && cd build
${CMAKE_COMMAND} -GNinja ../
ninja
ninja test
