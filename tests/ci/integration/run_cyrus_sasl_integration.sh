#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#    - SCRATCH_FOLDER
#      - CYRUS_SRC_FOLDER
#      - AWS_LC_BUILD_FOLDER
#      - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SRC_ROOT}/CYRUS_BUILD_ROOT"
CYRUS_SRC_FOLDER="${SCRATCH_FOLDER}/cyrus"
CYRUS_BUILD_PREFIX="${CYRUS_SRC_FOLDER}/build/install"
CYRUS_BUILD_EPREFIX="${CYRUS_SRC_FOLDER}/build/exec-install"

AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

export CFLAGS="-I$AWS_LC_INSTALL_FOLDER/include ${CFLAGS:=}"
export CPPFLAGS="-I$AWS_LC_INSTALL_FOLDER/include ${CXXFLAGS:=}"
export CXXFLAGS="-I$AWS_LC_INSTALL_FOLDER/include ${CXXFLAGS:=}"
export LDFLAGS="-L$AWS_LC_INSTALL_FOLDER/lib ${LDFLAGS:=}"

function cyrus_build() {
  sh ./autogen.sh \
  --prefix="$CYRUS_BUILD_PREFIX" \
  --exec-prefix="$CYRUS_BUILD_EPREFIX" \
  --with-openssl="$AWS_LC_INSTALL_FOLDER"

  make -j install

  # Assert Cyrus-SASL was built with AWS-LC
  local cyrus_executable="${CYRUS_SRC_FOLDER}/build/exec-install/lib/libsasl2.so"
  ${AWS_LC_BUILD_FOLDER}/check-linkage.sh ${cyrus_executable} crypto || exit 1
}

# TO-DO: Setup Kerberos and DB, then use sample client and server programs to test GSSAPI

git clone --depth 1 https://github.com/cyrusimap/cyrus-sasl.git ${CYRUS_SRC_FOLDER}
cd ${CYRUS_SRC_FOLDER}
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=1

export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}

# Build cyrus from source.
pushd ${CYRUS_SRC_FOLDER}
cyrus_build
