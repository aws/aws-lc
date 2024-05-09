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
OPENVPN_PATCH_BUILD_FOLDER="${SRC_ROOT}/tests/ci/integration/openvpn_patch"
OPENVPN_BUILD_PREFIX="${OPENVPN_SRC_FOLDER}/build/install"
OPENVPN_BUILD_EPREFIX="${OPENVPN_SRC_FOLDER}/build/exec-install"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"


mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

function openvpn_build() {
  autoreconf -ivf
  ./configure \
  --prefix $OPENVPN_BUILD_PREFIX \
  --exec-prefix $OPENVPN_BUILD_EPREFIX \
  --with-crypto-library=openssl \
  --with-openssl-engine=no   
  
  make 
  make install
}

# TODO: Remove this when we make an upstream contribution.
function openvpn_patch_build() {
  for patchfile in $(find -L "${OPENVPN_PATCH_BUILD_FOLDER}" -type f -name '*.patch'); do
    echo "Apply patch $patchfile..."
    patch -p1 --quiet -i "$patchfile"
  done
}

git clone https://github.com/OpenVPN/openvpn.git ${OPENVPN_SRC_FOLDER} --depth 1
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1

# Build nginx from source.
pushd ${OPENVPN_SRC_FOLDER}
openvpn_patch_build
export OPENSSL_CFLAGS="-I/${AWS_LC_INSTALL_FOLDER}/include" 
export OPENSSL_LIBS="-L/${AWS_LC_INSTALL_FOLDER}/lib64 -lssl -lcrypto" 
openvpn_build
popd
