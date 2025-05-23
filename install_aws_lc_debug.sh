#!/usr/bin/env bash

set -eux

TMP_DIR=`mktemp -d`
echo ${TMP_DIR}
AWS_LC_BUILD=${TMP_DIR}/AWS-LC-BUILD
mkdir -p "${AWS_LC_BUILD}"

AWS_LC_INSTALL=${HOME}/lib/AWS-LC-DEBUG-INSTALL
if [[ -e ${AWS_LC_INSTALL} ]]; then
    rm -rf ${AWS_LC_INSTALL}/*
fi
mkdir -p "${AWS_LC_INSTALL}"

export CFLAGS="-DAWS_LC_INTERNAL_IGNORE_BN_SET_FLAGS=1"

# create static
MY_CMAKE_FLAGS=("-DCMAKE_BUILD_TYPE=Debug" "-GNinja")

# create shared
# shellcheck disable=SC2068
cmake ~/workplace/open-source/aws-lc -B ${AWS_LC_BUILD} -DCMAKE_INSTALL_PREFIX=${AWS_LC_INSTALL} "-DBUILD_SHARED_LIBS=1" "${MY_CMAKE_FLAGS[@]}"
cmake --build ${AWS_LC_BUILD} --target install

cmake ~/workplace/open-source/aws-lc -B ${AWS_LC_BUILD} -DCMAKE_INSTALL_PREFIX=${AWS_LC_INSTALL} "-DBUILD_SHARED_LIBS=0" "${MY_CMAKE_FLAGS[@]}"
cmake --build ${AWS_LC_BUILD} --target install

cmake --build ${AWS_LC_BUILD} --target run_tests

