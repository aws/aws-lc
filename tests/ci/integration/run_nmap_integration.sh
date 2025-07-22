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
SCRATCH_FOLDER="${SRC_ROOT}/NMAP_BUILD_ROOT"
NMAP_SRC_FOLDER="${SCRATCH_FOLDER}/nmap"
NMAP_BUILD_PREFIX="${NMAP_SRC_FOLDER}/build/install"
NMAP_BUILD_EPREFIX="${NMAP_SRC_FOLDER}/build/exec-install"
NMAP_PATCH_FOLDER="${SRC_ROOT}/tests/ci/integration/nmap_patch"

AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

function nmap_build() {
  ./configure \
    --prefix="$NMAP_BUILD_PREFIX" \
    --exec-prefix="$NMAP_BUILD_EPREFIX" \
    --with-openssl="$AWS_LC_INSTALL_FOLDER" \
    --without-zenmap

  make -j install

  local nmap_executable="${NMAP_BUILD_EPREFIX}/bin/nmap"
  ${AWS_LC_BUILD_FOLDER}/check-linkage.sh ${nmap_executable} crypto || exit 1
}

# TODO: Remove this when we make an upstream contribution.
function nmap_patch_build() {
   for patchfile in $(find -L "${NMAP_PATCH_FOLDER}" -type f -name '*.patch'); do
     echo "Apply patch $patchfile..."
     patch -p1 --quiet -i "$patchfile"
   done
}

function nmap_run_tests() {
  # Add nmap executable to path, needed for zenmap tests
  export PATH="${NMAP_BUILD_EPREFIX}/bin/:$PATH"
  make check
}

git clone --depth 1 https://github.com/nmap/nmap.git ${NMAP_SRC_FOLDER} 
cd ${NMAP_SRC_FOLDER}
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=1

export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:+$LD_LIBRARY_PATH:}${AWS_LC_INSTALL_FOLDER}/lib"

# Build nmap from source.
pushd ${NMAP_SRC_FOLDER}
nmap_patch_build
nmap_build
nmap_run_tests
