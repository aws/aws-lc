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
IBMTPM_PATCH_BUILD_FOLDER="${SRC_ROOT}/tests/ci/integration/ibmtpm_patch"

AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

function ibmtpm_build() {
  # Check which AWS-LC library folder name we must use.
  if [ -d ${AWS_LC_INSTALL_FOLDER}/lib64 ]; then
    AWS_LC_LIBRARY_FOLDER="lib64"
  else
    AWS_LC_LIBRARY_FOLDER="lib"
  fi

  export CXXFLAGS="-I${AWS_LC_INSTALL_FOLDER}/include $CXXFLAGS"
  export CFLAGS="-I${AWS_LC_INSTALL_FOLDER}/include $CFLAGS"
  export LDFLAGS="-L${AWS_LC_INSTALL_FOLDER}/${AWS_LC_LIBRARY_FOLDER} $LDFLAGS"

  pushd src
  make -j

  local ibmtpm_executable="tpm_server"
  ldd ${ibmtpm_executable} \
    | grep "${AWS_LC_INSTALL_FOLDER}/${AWS_LC_LIBRARY_FOLDER}/libcrypto.so" || exit 1

  popd
}

function ibmtpm_patch_build() {
  patchfile="${IBMTPM_PATCH_BUILD_FOLDER}/ibmtpm-mainline-awslc.patch"
  echo "Apply patch $patchfile..."
  patch -p1 --quiet -i "$patchfile"
}

git clone https://github.com/kgoldman/ibmswtpm2.git ${IBMTPM_SRC_FOLDER}
cd ${IBMTPM_SRC_FOLDER}
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=Debug -DBUILD_SHARED_LIBS=1

# Build ibmtpm from source.
pushd ${IBMTPM_SRC_FOLDER}
ibmtpm_patch_build
ibmtpm_build
popd
