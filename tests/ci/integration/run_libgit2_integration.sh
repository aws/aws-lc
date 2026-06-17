#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Required first argument: libgit2 git ref (release tag, branch, or commit SHA).
if [ "$#" -lt 1 ] || [ -z "${1:-}" ]; then
  echo "Usage: $0 <libgit2-git-ref>" >&2
  echo "  ref may be a release tag (e.g. 'v1.9.4'), branch (e.g. 'main'), or commit SHA." >&2
  exit 1
fi
LIBGIT2_REF="$1"

# Set up environment.

# SYS_ROOT
#  |
#  - SRC_ROOT(aws-lc)
#  |
#  - SCRATCH_FOLDER
#    |
#    - libgit2
#    - LIBGIT2_BUILD_FOLDER
#    - LIBGIT2_INSTALL_FOLDER
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
SCRATCH_FOLDER=${SYS_ROOT}/"LIBGIT2_SCRATCH"
LIBGIT2_SRC_FOLDER="${SCRATCH_FOLDER}/libgit2"
LIBGIT2_PATCH_FOLDER="${SCRIPT_DIR}"/libgit2_patch
LIBGIT2_BUILD_FOLDER="${SCRATCH_FOLDER}/libgit2-build"
LIBGIT2_INSTALL_FOLDER="${SCRATCH_FOLDER}/libgit2-install"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

mkdir -p "${SCRATCH_FOLDER}"
rm -rf "${SCRATCH_FOLDER:?}"/*

pushd "${SCRATCH_FOLDER}"

function libgit2_patch_build() {
  pushd "${LIBGIT2_SRC_FOLDER}"
  for patchfile in $(find -L "${LIBGIT2_PATCH_FOLDER}" -type f -name '*.patch' | sort); do
    echo "Apply patch $patchfile..."
    patch -p1 --quiet -i "$patchfile"
  done
  popd
}

function libgit2_build_shared() {
  cmake -B "${LIBGIT2_BUILD_FOLDER}" -DBUILD_SHARED_LIBS=ON -DLINK_WITH_STATIC_LIBRARIES=OFF -DBUILD_TESTS=1 -DCMAKE_INSTALL_PREFIX="${LIBGIT2_INSTALL_FOLDER}" -DOPENSSL_ROOT_DIR="${AWS_LC_INSTALL_FOLDER}" -DUSE_SSH=exec -DUSE_HTTPS=OpenSSL -DUSE_SHA1=HTTPS -DUSE_SHA256=HTTPS -DCMAKE_C_STANDARD=99 -DUSE_AUTH_NTLM=builtin
  cmake --build "${LIBGIT2_BUILD_FOLDER}" --target install
  ${SCRATCH_FOLDER}/check-linkage.sh "${LIBGIT2_INSTALL_FOLDER}/bin/git2" crypto || exit 1
}

function libgit2_build_static() {
  cmake -B "${LIBGIT2_BUILD_FOLDER}" -DBUILD_SHARED_LIBS=OFF -DLINK_WITH_STATIC_LIBRARIES=ON -DBUILD_TESTS=1 -DCMAKE_INSTALL_PREFIX="${LIBGIT2_INSTALL_FOLDER}" -DOPENSSL_ROOT_DIR="${AWS_LC_INSTALL_FOLDER}" -DUSE_SSH=exec -DUSE_HTTPS=OpenSSL -DUSE_SHA1=HTTPS -DUSE_SHA256=HTTPS -DCMAKE_C_STANDARD=99 -DUSE_AUTH_NTLM=builtin
  cmake --build "${LIBGIT2_BUILD_FOLDER}" --target install
  nm --defined-only "${LIBGIT2_INSTALL_FOLDER}/bin/git2" | grep awslc_version_string || exit 1
}

function libgit2_run_tests() {
  # Local suites (git plumbing; exercises AWS-LC libcrypto). 'offline' is the
  # full libgit2_tests suite with -xonline.
  ctest --extra-verbose -R 'offline|invasive'

  # Online suite: the only coverage of AWS-LC libssl (TLS via streams/openssl.c).
  # Run libgit2_tests directly so we can exclude:
  #   online::badssl     - *.badssl.com resets before cert validation from our
  #                        networks (server-side, not AWS-LC; cert rejection is
  #                        still covered by online::clone::certificate_invalid).
  #   online::customcert - clones test.libgit2.org with no timeout, and that host
  #                        is unreachable from our CI and dev networks, so it hangs.
  # 'timeout' is a backstop so a future unresponsive endpoint fails fast instead
  # of hanging indefinitely.
  timeout --kill-after=60s 1200s \
    "${LIBGIT2_BUILD_FOLDER}/libgit2_tests" -v -sonline -xonline::customcert -xonline::badssl
}

# Fetch the requested libgit2 ref (tag, branch, or commit).
git init "${LIBGIT2_SRC_FOLDER}"
git -C "${LIBGIT2_SRC_FOLDER}" fetch --depth 1 https://github.com/libgit2/libgit2.git "${LIBGIT2_REF}"
git -C "${LIBGIT2_SRC_FOLDER}" checkout FETCH_HEAD
mkdir -p "${AWS_LC_BUILD_FOLDER}" "${AWS_LC_INSTALL_FOLDER}" "${LIBGIT2_BUILD_FOLDER}" "${LIBGIT2_INSTALL_FOLDER}"
ls

libgit2_patch_build

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1
cp "${AWS_LC_BUILD_FOLDER}/check-linkage.sh" "${SCRATCH_FOLDER}/"
aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=0
export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

pushd "${LIBGIT2_SRC_FOLDER}"
libgit2_build_shared
popd

pushd "${LIBGIT2_BUILD_FOLDER}"
libgit2_run_tests
popd

rm -rf "${LIBGIT2_BUILD_FOLDER:?}"/* "${LIBGIT2_INSTALL_FOLDER:?}"/*

pushd "${LIBGIT2_SRC_FOLDER}"
libgit2_build_static
popd

pushd "${LIBGIT2_BUILD_FOLDER}"
libgit2_run_tests
popd

popd
