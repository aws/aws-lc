#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Dependencies needed for nmap build
if [ "$(id -u)" -eq 0 ]; then
  apt-get update
  apt-get install -y --no-install-recommends liblinear-dev
fi

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#  - SCRATCH_FOLDER
#    - OPENVPN_SRC_FOLDER
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SYS_ROOT}/NMAP_BUILD_ROOT"
NMAP_SRC_FOLDER="${SCRATCH_FOLDER}/nmap"
NMAP_BUILD_PREFIX="${NMAP_SRC_FOLDER}/build/install"
NMAP_BUILD_EPREFIX="${NMAP_SRC_FOLDER}/build/exec-install"
NMAP_PATCH_ROOT="${SRC_ROOT}/tests/ci/integration/nmap_patch"

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

# Map nmap git ref to its patch subdirectory. Each supported ref needs its own
# subdir under nmap_patch/ because patches drift as nmap evolves.
function nmap_patch_folder_for_ref() {
  case "$1" in
    main|master)
      echo "${NMAP_PATCH_ROOT}/master" ;;
    deb076224e9f138ea29fa4823bcce0030301dc54)
      echo "${NMAP_PATCH_ROOT}/v7.99" ;;
    *)
      echo "ERROR: no patch directory configured for nmap ref '$1'" >&2
      echo "Add one under ${NMAP_PATCH_ROOT}/ and update nmap_patch_folder_for_ref." >&2
      return 1 ;;
  esac
}

function nmap_run_tests() {
  # Add nmap executable to path, needed for zenmap tests
  export PATH="${NMAP_BUILD_EPREFIX}/bin/:$PATH"
  make check
}

# Emit a CloudWatch metric when the pinned nmap ref's version (NMAP_MAJOR.NMAP_MINOR
# from nmap.h) drifts from master, so we get reminded to refresh the pin. nmap
# doesn't publish git tags or GitHub releases, so the version macro is the only
# in-repo signal of an upstream release. Only meaningful for pinned refs.
function nmap_version_drift_check() {
  local pinned_version
  pinned_version="$(awk '/^#define NMAP_MAJOR/ {maj=$3} /^#define NMAP_MINOR/ {min=$3} END {print maj"."min}' "${NMAP_SRC_FOLDER}/nmap.h")"
  local latest_version
  latest_version="$(curl -fsSL https://raw.githubusercontent.com/nmap/nmap/master/nmap.h \
    | awk '/^#define NMAP_MAJOR/ {maj=$3} /^#define NMAP_MINOR/ {min=$3} END {print maj"."min}')"
  if [[ -z "${latest_version}" || -z "${pinned_version}" ]]; then
    echo "Could not determine nmap version (pinned='${pinned_version}', latest='${latest_version}'); skipping drift metric." >&2
    return 0
  fi
  if [[ "${pinned_version}" != "${latest_version}" ]]; then
    aws cloudwatch put-metric-data --namespace AWS-LC --metric-name NmapVersionMismatch --value 1
  else
    aws cloudwatch put-metric-data --namespace AWS-LC --metric-name NmapVersionMismatch --value 0
  fi
}

# Required first argument: nmap git ref (commit, tag, or branch).
if [ "$#" -lt 1 ] || [ -z "${1:-}" ]; then
  echo "Usage: $0 <nmap-git-ref>" >&2
  echo "  ref may be a commit SHA, tag, or branch (e.g. 'main')." >&2
  exit 1
fi
NMAP_REF="$1"
NMAP_PATCH_FOLDER="$(nmap_patch_folder_for_ref "${NMAP_REF}")" || exit 1
git init ${NMAP_SRC_FOLDER}
git -C ${NMAP_SRC_FOLDER} fetch --depth 1 https://github.com/nmap/nmap.git ${NMAP_REF}
git -C ${NMAP_SRC_FOLDER} checkout FETCH_HEAD
cd ${NMAP_SRC_FOLDER}
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=1

export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:+$LD_LIBRARY_PATH:}${AWS_LC_INSTALL_FOLDER}/lib"

# Build nmap from source.
pushd ${NMAP_SRC_FOLDER}
# Only emit the drift metric for pinned refs; master is always at tip-of-tree.
case "${NMAP_REF}" in
  main|master) ;;
  *) nmap_version_drift_check ;;
esac
nmap_patch_build
nmap_build
nmap_run_tests
