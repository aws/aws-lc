#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  - SCRATCH_FOLDER
#     - postgres
#     - AWS_LC_BUILD_FOLDER
#     - AWS_LC_INSTALL_FOLDER
#     - POSTGRES_BUILD_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SRC_ROOT}/"POSTGRES_BUILD_ROOT"
POSTGRES_SRC_FOLDER="${SCRATCH_FOLDER}/postgres"
POSTGRES_BUILD_FOLDER="${SCRATCH_FOLDER}/postgres/build"
POSTGRES_PATCH_FOLDER="${SRC_ROOT}/tests/ci/integration/postgres_patch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${POSTGRES_SRC_FOLDER}/aws-lc-install"

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

function postgres_build() {
  ./configure --with-openssl --enable-tap-tests --with-includes=${AWS_LC_INSTALL_FOLDER}/include --with-libraries=${AWS_LC_INSTALL_FOLDER}/lib --prefix=$(pwd)/build
  make -j "$NUM_CPU_THREADS"
  # Build additional modules for postgres.
  make -j "$NUM_CPU_THREADS" -C contrib all
  ls -R build
}

function postgres_run_tests() {
  make -j "$NUM_CPU_THREADS" check
  # Run additional tests, particularly the "SSL" tests.
  make -j "$NUM_CPU_THREADS" check-world PG_TEST_EXTRA='ssl'
  cd ${SCRATCH_FOLDER}
}

# SSL tests expect the OpenSSL style of error messages. We patch this to expect AWS-LC's style.
# TODO: Remove this when we make an upstream contribution.
function postgres_patch() {
  POSTGRES_ERROR_STRING=("certificate verify failed" "bad decrypt" "ssl\[a\-z0\-9\/\]\* alert certificate revoked" "tlsv1 alert unknown ca")
  AWS_LC_EXPECTED_ERROR_STRING=("CERTIFICATE_VERIFY_FAILED" "BAD_DECRYPT" "SSLV3_ALERT_CERTIFICATE_REVOKED" "TLSV1_ALERT_UNKNOWN_CA")
  for i in "${!POSTGRES_ERROR_STRING[@]}"; do
    find ./ -type f -name "001_ssltests.pl" | xargs sed -i -e "s|${POSTGRES_ERROR_STRING[$i]}|${AWS_LC_EXPECTED_ERROR_STRING[$i]}|g"
  done
  for patchfile in $(find -L "${POSTGRES_PATCH_FOLDER}" -type f -name '*.patch'); do
    echo "Apply patch $patchfile..."
    patch -p1 --quiet -i "$patchfile"
  done
}

# Get latest postgres version.
git clone https://github.com/postgres/postgres.git ${POSTGRES_SRC_FOLDER}
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${POSTGRES_BUILD_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=0
cd ${POSTGRES_SRC_FOLDER}
postgres_patch
postgres_build
postgres_run_tests

