#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# We expect an executable failure in this test. Hence, don't use -e.
set -xo pipefail

source tests/ci/common_posix_setup.sh

# libseccomp is required to run this tests. Typically this package is named
# either libseccomp-dev or libseccomp-devel.

# Set up environment.

# SYS_ROOT
#  |
#  - SRC_ROOT(aws-lc)
#  |
#  - SCRATCH_FOLDER
#    |
#    - seccomp app binary
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SYS_ROOT}/"SCRATCH_AWSLC_PRESANDBOX_TEST"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"
: "${CC:=gcc}"

# Make script execution idempotent.
mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" \
  -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo \
  -DBUILD_SHARED_LIBS=OFF

# Check which AWS-LC library folder name we must use.
if [ -d ${AWS_LC_INSTALL_FOLDER}/lib64 ]; then
  AWS_LC_LIBRARY_FOLDER="lib64"
else
  AWS_LC_LIBRARY_FOLDER="lib"
fi

function seccomp_build() {
  __CFLAGS=${1}
  ${CC} -I${SRC_ROOT}/include ${__CFLAGS} \
    ${SRC_ROOT}/tests/ci/test_apps/seccomp_app.c -o seccomp_app \
    -lseccomp -L${AWS_LC_INSTALL_FOLDER}/${AWS_LC_LIBRARY_FOLDER} -lcrypto -pthread
}

echo "Test that AWS-LC performs syscalls that will trip the seccomp filter."
seccomp_build ""
./seccomp_app
if [ $? -eq 0 ]; then
  echo "Failure: expected AWS-LC syscalls to trip the seccomp filter."
  exit 1
fi

echo "Test that when AWS-LC is sandbox configured, the seccomp filter does not trip."
seccomp_build "-DUSE_AWS_LC_PRE_SANDBOX"
./seccomp_app
if [ $? -ne 0 ]; then
  echo "Failure: AWS-LC is sandbox configured but something tripped the seccomp filter."
  exit 1
fi

echo "Pre-sandbox test succeeded."
