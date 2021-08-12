#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

AWS_LC_DIR=${PWD##*/}
cd ../
ROOT=$(pwd)
mkdir -p aws-lc-build aws-lc-install s2n-tls-build
git clone https://github.com/aws/s2n-tls.git
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
