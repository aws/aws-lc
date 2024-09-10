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


mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

function openvpn_build() {
  autoreconf -ivf

  OPENSSL_CFLAGS="-I/${AWS_LC_INSTALL_FOLDER}/include" \
  OPENSSL_LIBS="-L/${AWS_LC_INSTALL_FOLDER}/lib -lssl -lcrypto" \
  ./configure \
    --prefix="$OPENVPN_BUILD_PREFIX" \
    --exec-prefix="$OPENVPN_BUILD_EPREFIX" \
    --with-crypto-library=openssl \
    --with-openssl-engine=no

  make -j install

  export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"

  local openvpn_executable="${OPENVPN_SRC_FOLDER}/build/exec-install/sbin/openvpn"
  ldd ${openvpn_executable} \
    | grep "${AWS_LC_INSTALL_FOLDER}/lib/libcrypto.so" || exit 1
}

# TODO: Remove this when we make an upstream contribution.
function openvpn_patch_build() {
  for patchfile in $(find -L "${OPENVPN_PATCH_BUILD_FOLDER}" -type f -name '*.patch'); do
    echo "Apply patch $patchfile..."
    patch -p1 --quiet -i "$patchfile"
  done
}

function openvpn_run_tests() {
  # Explicitly running as sudo and passing in LD_LIBRARY_PATH as some OpenVPN
  # tests run as sudo and LD_LIBRARY_PATH doesn't get inherited.
  sudo LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib" make check
}

git clone https://github.com/OpenVPN/openvpn.git ${OPENVPN_SRC_FOLDER}

# anchoring to tip of minor release 2.6.x for OpenVPN, currently not compatible
# with tip of main
cd ${OPENVPN_SRC_FOLDER} && git checkout release/2.6
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=Debug -DBUILD_SHARED_LIBS=1

# Build openvpn from source.
pushd ${OPENVPN_SRC_FOLDER}
openvpn_patch_build
openvpn_build
openvpn_run_tests
