#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#    - SCRATCH_FOLDER
#      - IBMTPM_SRC_FOLDER
#      - AWS_LC_BUILD_FOLDER
#      - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SRC_ROOT}/IBMTPM_BUILD_ROOT"
IBMTPM_SRC_FOLDER="${SCRATCH_FOLDER}/ibmtpm"
IBMTPM_BUILD_PREFIX="${IBMTPM_SRC_FOLDER}/build/install"

AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

function ibmtpm_build() {
  export CXXFLAGS="-I${AWS_LC_INSTALL_FOLDER}/include $CXXFLAGS"
  export CFLAGS="-I${AWS_LC_INSTALL_FOLDER}/include $CFLAGS"
  export LDFLAGS="-L${AWS_LC_INSTALL_FOLDER}/lib $LDFLAGS"

  pushd src
  make -j
  
  export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"
  local ibmtpm_executable="tpm_server"
  ${AWS_LC_BUILD_FOLDER}/check-linkage.sh ${ibmtpm_executable} crypto || exit 1

  popd
}

git clone https://github.com/kgoldman/ibmswtpm2.git ${IBMTPM_SRC_FOLDER}
cd ${IBMTPM_SRC_FOLDER}
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DCMAKE_INSTALL_LIBDIR=lib -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=Debug -DBUILD_SHARED_LIBS=1

# Build ibmtpm from source.
pushd ${IBMTPM_SRC_FOLDER}
ibmtpm_build
popd
