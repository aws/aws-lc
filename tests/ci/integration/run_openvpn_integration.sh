#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#    - SCRATCH_FOLDER
#      - OPENVPN_SRC_FOLDER
#      - AWS_LC_BUILD_FOLDER
#      - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SRC_ROOT}/OPENVPN_BUILD_ROOT"
OPENVPN_SRC_FOLDER="${SCRATCH_FOLDER}/openvpn"
OPENVPN_BUILD_PREFIX="${OPENVPN_SRC_FOLDER}/build/install"
OPENVPN_BUILD_EPREFIX="${OPENVPN_SRC_FOLDER}/build/exec-install"
OPENVPN_PATCH_BUILD_FOLDER="${SRC_ROOT}/tests/ci/integration/openvpn_patch"

AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

# Check if branch name is passed as an argument
if [ $# -eq 0 ]; then
  echo "No branch name provided. Usage: $0 <branch_name>"
  exit 1
fi
BRANCH_NAME=$1

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

function openvpn_build() {
  autoreconf -ivf

  OPENSSL_CFLAGS="-I/${AWS_LC_INSTALL_FOLDER}/include" \
  OPENSSL_LIBS="-L/${AWS_LC_INSTALL_FOLDER}/lib -lssl -lcrypto" \
  LDFLAGS="-Wl,-rpath=/${AWS_LC_INSTALL_FOLDER}/lib" \
  ./configure \
    --prefix="$OPENVPN_BUILD_PREFIX" \
    --exec-prefix="$OPENVPN_BUILD_EPREFIX" \
    --with-crypto-library=openssl \
    --with-openssl-engine=no

  make -j install

  local openvpn_executable="${OPENVPN_SRC_FOLDER}/build/exec-install/sbin/openvpn"
  ${AWS_LC_BUILD_FOLDER}/check-linkage.sh ${openvpn_executable} crypto || exit 1
}

function openvpn_patch_build() {
  if [ "$BRANCH_NAME" = "release/2.6" ]; then
    patchfile="${OPENVPN_PATCH_BUILD_FOLDER}/aws-lc-openvpn2-6-x.patch"
    echo "Apply patch $patchfile..."
    patch -p1 --quiet -i "$patchfile"
  fi
}

function openvpn_run_tests() {
  sudo make check
}

git clone https://github.com/OpenVPN/openvpn.git ${OPENVPN_SRC_FOLDER}
cd ${OPENVPN_SRC_FOLDER} && git checkout $BRANCH_NAME
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=Debug -DBUILD_SHARED_LIBS=1

# Build openvpn from source.
pushd ${OPENVPN_SRC_FOLDER}
openvpn_patch_build
openvpn_build
openvpn_run_tests
