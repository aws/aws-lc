#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

AWS_LC_DIR=${PWD##*/}
cd ../
ROOT=$(pwd)

SCRATCH_FOLDER=${ROOT}/"SCRATCH_AWSLC_S2N_INTERN_TEST"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"
S2N_TLS_BUILD_FOLDER="${SCRATCH_FOLDER}/s2n-tls-build"

# Make script execution idempotent.
mkdir -p ${SCRATCH_FOLDER}
rm -rf ${SCRATCH_FOLDER}/*
cd ${SCRATCH_FOLDER}

# Test helper functions.
# Assumes OS where the Ninja executable is named "ninja". This is not true for
# AL2 for example.

function fail() {
    echo "test failure: $1"
    exit 1
}

function aws_lc_build() {
	${CMAKE_COMMAND} ${AWS_LC_DIR} -GNinja "-B${AWS_LC_BUILD_FOLDER}" "-DCMAKE_INSTALL_PREFIX=${AWS_LC_INSTALL_FOLDER}" "$@"
	ninja -C ${AWS_LC_BUILD_FOLDER} install
	ls -R ${AWS_LC_INSTALL_FOLDER}
	rm -rf ${AWS_LC_BUILD_FOLDER}/*
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
	rm -rf ${S2N_TLS_BUILD_FOLDER}/*
}

# Get latest s2n-tls version.

mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} ${S2N_TLS_BUILD_FOLDER}
git clone https://github.com/aws/s2n-tls.git
# TODO: for new FIPS branch, checkout another code commit of s2n-tls.
# TODO: for new FIPS branch, replace this script content with main branch.
# Checkout commit before https://github.com/aws/s2n-tls/commit/785596b9694d7e12274afea9f42b8216a07102da
(cd s2n-tls && git checkout 36c3dc72ab1359cf721294e1258dfdc2962f3ffc)
ls

# s2n-tls's FindLibCrypto.cmake expects to find both the archieve (.a) and shared object (.so) libcrypto
cmake ${AWS_LC_DIR} -GNinja "-B${ROOT}/aws-lc-build" "-DCMAKE_INSTALL_PREFIX=${ROOT}/aws-lc-install"
ninja -C aws-lc-build install
rm -rf aws-lc-build/*
cmake ${AWS_LC_DIR} -GNinja "-B${ROOT}/aws-lc-build" "-DCMAKE_INSTALL_PREFIX=${ROOT}/aws-lc-install" -DBUILD_SHARED_LIBS=1
ninja -C aws-lc-build install

cmake s2n-tls -GNinja "-B${ROOT}/s2n-tls-build" "-DCMAKE_PREFIX_PATH=${ROOT}/aws-lc-install"
ninja -C s2n-tls-build

cd "${ROOT}/s2n-tls-build"
ctest -j 8 --output-on-failure
