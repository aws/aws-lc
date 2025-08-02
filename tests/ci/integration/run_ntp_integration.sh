#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  |
#  - SRC_ROOT(aws-lc)
#  |
#  - SCRATCH_FOLDER
#    |
#    - NTP_SRC_FOLDER
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SYS_ROOT}/NTP_BUILD_ROOT"
NTP_WEBSITE_URL="https://downloads.nwtime.org/ntp/"

# - curl fetches the HTML content of the website,
# - the first grep searches for all occurrences of href attributes in anchor tags and outputs only the URLs,
# - sed removes the href=" and trailing " from the URLs,
# - the second grep filters only the links ending with .tar.gz,
# - "head -n 1" gets only the first matching line
# - cut strips "/ntp/" from the link and retains only the tar name.
NTP_TAR=$(curl -s ${NTP_WEBSITE_URL} | grep -o 'href="[^"]*"' | sed 's/href="//;s/"$//' | grep '.tar.gz$' | head -n 1 | cut -d '/' -f3)
NTP_DOWNLOAD_URL="${NTP_WEBSITE_URL}/${NTP_TAR}"
NTP_SRC_FOLDER="${SCRATCH_FOLDER}/ntp-src"
NTP_PATCH_FOLDER="${SRC_ROOT}/tests/ci/integration/ntp_patch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

# TODO: Remove this when we make an upstream contribution.
function ntp_patch() {
  for patchfile in $(find -L "${NTP_PATCH_FOLDER}" -type f -name '*.patch'); do
    echo "Apply patch $patchfile..."
    patch -p1 --quiet -i "$patchfile"
  done
}

function ntp_build() {
  ./configure --with-openssl-incdir="${AWS_LC_INSTALL_FOLDER}/include" --with-openssl-libdir="${AWS_LC_INSTALL_FOLDER}/lib/"
  make -j "$NUM_CPU_THREADS"
}

function ntp_run_tests() {
  export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"
  make -j "$NUM_CPU_THREADS" check
}

mkdir -p "$SCRATCH_FOLDER"
rm -rf "${SCRATCH_FOLDER:?}/*"
cd "$SCRATCH_FOLDER"

wget -q $NTP_DOWNLOAD_URL
mkdir -p "$NTP_SRC_FOLDER"
tar -xzf "$NTP_TAR" -C "$NTP_SRC_FOLDER" --strip-components=1

mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1

# Build ntp from source.
pushd ${NTP_SRC_FOLDER}

ntp_patch
ntp_build
ntp_run_tests

popd

${AWS_LC_BUILD_FOLDER}/check-linkage.sh "${NTP_SRC_FOLDER}/ntpd/ntpd" crypto || exit 1
