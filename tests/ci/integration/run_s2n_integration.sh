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
#    - s2n-tls
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER
#    - S2N_TLS_BUILD_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SYS_ROOT}/"SCRATCH_AWSLC_S2N_INTERN_TEST"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"
S2N_TLS_BUILD_FOLDER="${SCRATCH_FOLDER}/s2n-tls-build"

# Make script execution idempotent.
mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

# Test helper functions.
# Assumes OS where the Ninja executable is named "ninja". This is not true for
# AL2 for example.

function fail() {
    echo "test failure: $1"
    exit 1
}

function s2n_tls_build() {
	${CMAKE_COMMAND} s2n-tls -GNinja "-B${S2N_TLS_BUILD_FOLDER}" "-DCMAKE_PREFIX_PATH=${AWS_LC_INSTALL_FOLDER}" "$@"
	ninja -C ${S2N_TLS_BUILD_FOLDER}
	ls -R ${S2N_TLS_BUILD_FOLDER}
}

function s2n_tls_run_tests() {
	cd ${S2N_TLS_BUILD_FOLDER}
	ctest -j ${NUM_CPU_THREADS} --output-on-failure
	cd ${SCRATCH_FOLDER}
}

function s2n_tls_prepare_new_build() {
	rm -rf "${S2N_TLS_BUILD_FOLDER:?}"/*
}

# Get latest s2n-tls version.

mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${S2N_TLS_BUILD_FOLDER}
git clone https://github.com/aws/s2n-tls.git
ls

# s2n-tls's FindLibCrypto.cmake expects to find both the static and shared
# libcrypto objects. We can't use existing test helper functions
# (e.g. run_build()) because they make implicit assumptions about e.g. build
# folders.

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=0
aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1

# Build s2n-tls+aws-lc and run s2n-tls tests. First using static aws-lc
# libcrypto and then shared aws-lc libcrypto.

s2n_tls_build
s2n_tls_run_tests
s2n_tls_prepare_new_build

s2n_tls_build -DBUILD_SHARED_LIBS=1
s2n_tls_run_tests
s2n_tls_prepare_new_build

# Test interned s2n-tls+aws-lc against both static and shared aws-lc libcrypto.

s2n_tls_build -DS2N_INTERN_LIBCRYPTO=1
s2n_tls_run_tests
s2n_tls_prepare_new_build

s2n_tls_build -DBUILD_SHARED_LIBS=1 -DS2N_INTERN_LIBCRYPTO=1
# Sanity check that libcrypto does not appear in the .dynamic ELF section.
ldd ${S2N_TLS_BUILD_FOLDER}/lib/libs2n.so | grep -q libcrypto && fail "libs2n.so declares a dynamic dependency on libcrypto which should not happen with interned s2n-tls+aws-lc"
s2n_tls_run_tests
s2n_tls_prepare_new_build
