#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

KRB5_GIT_REF="${1:?Usage: $0 <krb5-git-ref>}"

# Set up environment.

# SYS_ROOT
#  |
#  - SRC_ROOT(aws-lc)
#  |
#  - SCRATCH_FOLDER
#    |
#    - krb5
#    - KRB5_BUILD_FOLDER
#    - KRB5_INSTALL_FOLDER
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
SCRATCH_FOLDER="${SYS_ROOT}/KRB5_SCRATCH"
KRB5_SRC_FOLDER="${SCRATCH_FOLDER}/krb5"
KRB5_PATCH_FOLDER="${SCRIPT_DIR}/krb5_patch"
KRB5_BUILD_FOLDER="${SCRATCH_FOLDER}/krb5-build"
KRB5_INSTALL_FOLDER="${SCRATCH_FOLDER}/krb5-install"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

mkdir -p "${SCRATCH_FOLDER}"
rm -rf "${SCRATCH_FOLDER:?}"/*

pushd "${SCRATCH_FOLDER}"

echo "Using krb5 git ref: ${KRB5_GIT_REF}"

function krb5_apply_patches() {
  pushd "${KRB5_SRC_FOLDER}"
  for patchfile in $(find -L "${KRB5_PATCH_FOLDER}" -type f -name '*.patch' | sort); do
    echo "Applying patch ${patchfile}..."
    patch -p1 --quiet -i "${patchfile}"
  done
  popd
}

function krb5_build() {
  pushd "${KRB5_SRC_FOLDER}/src"

  autoreconf -fi

  # --with-crypto-impl=openssl selects the OpenSSL-compatible crypto backend,
  # which AWS-LC plugs into. We disable PKINIT and LDAP plugins (which pull in
  # extra dependencies and additional crypto surface area not relevant to this
  # integration), and we point the configure script at our AWS-LC install via
  # CPPFLAGS / LDFLAGS so its OpenSSL probes find AWS-LC's headers and libs.
  CPPFLAGS="-I${AWS_LC_INSTALL_FOLDER}/include ${CPPFLAGS:-}" \
  LDFLAGS="-L${AWS_LC_INSTALL_FOLDER}/lib ${LDFLAGS:-}" \
  PKG_CONFIG_PATH="${AWS_LC_INSTALL_FOLDER}/lib/pkgconfig${PKG_CONFIG_PATH:+:${PKG_CONFIG_PATH}}" \
  ./configure \
    --prefix="${KRB5_INSTALL_FOLDER}" \
    --with-crypto-impl=openssl \
    --without-libedit \
    --without-readline \
    --disable-pkinit \
    --disable-static \
    --enable-shared

  make -j "${NUM_CPU_THREADS}"
  make -j "${NUM_CPU_THREADS}" install

  # Assert krb5 linked against AWS-LC's libcrypto rather than a system OpenSSL.
  local kinit_bin="${KRB5_INSTALL_FOLDER}/bin/kinit"
  "${AWS_LC_BUILD_FOLDER}/check-linkage.sh" "${kinit_bin}" crypto || exit 1

  popd
}

# Run krb5's crypto unit tests. The full `make check` from the top of the tree
# spins up KDCs and exercises end-to-end Kerberos flows, which requires Python
# and additional CI plumbing. We build the test binaries then run the crypto
# test subset, which exercises the AWS-LC backend (AES-CTS, HMAC, SHA-2, PRF,
# key derivation) alongside krb5's built-in primitives (Camellia is served by
# the built-in implementation when building against AWS-LC).
function krb5_run_tests() {
  pushd "${KRB5_SRC_FOLDER}/src/lib/crypto"

  # Symlink AWS-LC's libcrypto into krb5's lib dir so the Makefile's
  # LD_LIBRARY_PATH (which only includes ../../../lib) can find it at
  # test runtime.
  ln -sf "${AWS_LC_INSTALL_FOLDER}/lib/libcrypto.so" "../../lib/libcrypto.so"
  ln -sf "${AWS_LC_INSTALL_FOLDER}/lib/libcrypto.so.1" "../../lib/libcrypto.so.1"

  make -j "${NUM_CPU_THREADS}" check
  popd
}

git clone --depth 1 --branch "${KRB5_GIT_REF}" \
  https://github.com/krb5/krb5.git "${KRB5_SRC_FOLDER}"
mkdir -p "${AWS_LC_BUILD_FOLDER}" "${AWS_LC_INSTALL_FOLDER}" \
         "${KRB5_BUILD_FOLDER}" "${KRB5_INSTALL_FOLDER}"
ls

krb5_apply_patches

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" \
  -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1

export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib${LD_LIBRARY_PATH:+:${LD_LIBRARY_PATH}}"

krb5_build
krb5_run_tests

popd
