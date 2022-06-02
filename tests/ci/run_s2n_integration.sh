#!/bin/bash -exu
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# Set up environment

AWS_LC_DIR=${PWD##*/}
cd ../
ROOT=$(pwd)

AWS_LC_BUILD_FOLDER="${ROOT}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${ROOT}/aws-lc-install"
S2N_TLS_BUILD_FOLDER="${ROOT}/s2n-tls-build"

# Test helpers

function fail() {
    echo "test failure: $1"
    exit 1
}

function aws_lc_build() {
	cmake ${AWS_LC_DIR} -GNinja "-B${AWS_LC_BUILD_FOLDER}" "-DCMAKE_INSTALL_PREFIX=${AWS_LC_INSTALL_FOLDER}" "$@"
	ninja -C ${AWS_LC_BUILD_FOLDER} install
	ls -R ${AWS_LC_INSTALL_FOLDER}
	rm -rf ${AWS_LC_BUILD_FOLDER}/*
}

function s2n_tls_build() {
	cmake s2n -GNinja "-B${S2N_TLS_BUILD_FOLDER}" "-DCMAKE_PREFIX_PATH=${AWS_LC_INSTALL_FOLDER}" "$@"
	ninja -C ${S2N_TLS_BUILD_FOLDER}
	ls -R ${S2N_TLS_BUILD_FOLDER}
}

function s2n_tls_run_tests() {
	cd ${S2N_TLS_BUILD_FOLDER}
	ctest -j 8 --output-on-failure
	cd ${ROOT}
}

function s2n_tls_prepare_new_build() {
	rm -rf ${S2N_TLS_BUILD_FOLDER}/*
}

# Get latest s2n-tls version.

mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${S2N_TLS_BUILD_FOLDER}
git clone https://github.com/torben-hansen/s2n.git
cd s2n
git checkout fix_cmake_interning_build
cd ..
ls

# s2n-tls's FindLibCrypto.cmake expects to find both the static and shared
# libcrypto objects. We can't use existing test helper functions
# (e.g. run_build()) because they make implicit assumptions about e.g. build
# folders.

aws_lc_build
aws_lc_build -DBUILD_SHARED_LIBS=1

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
# Sanity check that libcrypto does not appear in .dynamic.
ldd ${S2N_TLS_BUILD_FOLDER}/lib/libs2n.so | grep -q libcrypto && fail "libs2n.so declares a dynamic dependency on libcrypto which should not happen with interned s2n-tls+aws-lc"
s2n_tls_run_tests
s2n_tls_prepare_new_build
