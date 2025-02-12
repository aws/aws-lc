#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

source tests/ci/common_posix_setup.sh

export CMAKE_BUILD_PARALLEL_LEVEL=1

# Set up environment.

# ROOT
#  |
#  - AWS_LC_DIR
#  |
#  - SCRATCH_FOLDER
#    |
#    - BUILD_DIR
#    - install-shared
#    - install-static
#    - install-both
#    - MYAPP_SRC

# Assumes script is executed from the root of aws-lc directory
AWS_LC_DIR=$(pwd)
ROOT=$(realpath ${AWS_LC_DIR}/..)

SCRATCH_DIR=${ROOT}/SCRATCH_AWSLC_INSTALL_SHARED_AND_STATIC
mkdir -p ${SCRATCH_DIR}
rm -rf "${SCRATCH_DIR:?}"/*
sync

function fail() {
    echo "test failure: $1"
    exit 1
}

function install_aws_lc() {
    local INSTALL_DIR=${SCRATCH_DIR}/$1
    local BUILD_SHARED_LIBS=$2

    local BUILD_DIR=${SCRATCH_DIR}/build
    rm -rf "${BUILD_DIR:?}"
    sync

    ${CMAKE_COMMAND} --fresh -H${AWS_LC_DIR} -B${BUILD_DIR} -GNinja -DCMAKE_INSTALL_PREFIX=${INSTALL_DIR} -DBUILD_TESTING=OFF -D${BUILD_SHARED_LIBS}
    ${CMAKE_COMMAND} --build ${BUILD_DIR} --target install
}

# create installation with shared libssl.so/libcrypto.so
install_aws_lc install-shared BUILD_SHARED_LIBS=ON

# create installation with static libssl.a/libcrypto.a
install_aws_lc install-static BUILD_SHARED_LIBS=OFF

# create installation with both shared libssl.so/libcrypto.so and static libssl.a/libcrypto.a
install_aws_lc install-both BUILD_SHARED_LIBS=OFF
install_aws_lc install-both BUILD_SHARED_LIBS=ON

# write out source of a small cmake project, containing:
# - mylib: a library that uses AWS-LC
# - myapp: executable that uses mylib
MYAPP_SRC_DIR=${SCRATCH_DIR}/myapp-src
rm -rf "${MYAPP_SRC_DIR:?}"
mkdir -p ${MYAPP_SRC_DIR}
sync

cat <<EOF > ${MYAPP_SRC_DIR}/mylib.c
#include <openssl/ssl.h>
void mylib_init(void) {
    OPENSSL_init_ssl(0, NULL);
}
EOF

cat <<EOF > ${MYAPP_SRC_DIR}/myapp.c
extern void mylib_init(void);
int main() {
    mylib_init();
}
EOF

cat <<EOF > ${MYAPP_SRC_DIR}/CMakeLists.txt
cmake_minimum_required (VERSION 3.0)
project (myapp C)
add_library(mylib mylib.c)
find_package(ssl REQUIRED)
target_link_libraries(mylib PRIVATE AWS::ssl)
add_executable(myapp myapp.c)
target_link_libraries(myapp PRIVATE mylib)
EOF

# build myapp and mylib, confirm that expected type of libssl and libcrypto are used
build_myapp() {
    local BUILD_SHARED_LIBS=$1 # ("BUILD_SHARED_LIBS=ON" or "BUILD_SHARED_LIBS=OFF")
    local AWS_LC_INSTALL_DIR=$2 # which install dir should be used
    local EXPECT_USE_LIB_TYPE=$3 # (".so" or ".a") which types of libssl and libcrypto are expected to be used

    echo "Build Parameters:"
    echo "BUILD_SHARED_LIBS: ${BUILD_SHARED_LIBS}"
    echo "AWS_LC_INSTALL_DIR: ${AWS_LC_INSTALL_DIR}"
    echo "EXPECT_USE_LIB_TYPE: ${EXPECT_USE_LIB_TYPE}"

    local BUILD_DIR=${SCRATCH_DIR}/build
    rm -rf "${BUILD_DIR:?}"
    sync

    cmake --fresh -H${MYAPP_SRC_DIR} -B${BUILD_DIR} -GNinja -D${BUILD_SHARED_LIBS} -DCMAKE_PREFIX_PATH=${SCRATCH_DIR}/${AWS_LC_INSTALL_DIR}
    cmake --build ${BUILD_DIR}
    ldd ${BUILD_DIR}/myapp

    test_lib_use ${BUILD_DIR}/myapp libssl ${EXPECT_USE_LIB_TYPE}
    test_lib_use ${BUILD_DIR}/myapp libcrypto ${EXPECT_USE_LIB_TYPE}
}

# test that app is using expected library
test_lib_use() {
    local APP=$1 # app to examine
    local LIB_NAME=$2 # name of lib that app should be using, without file extension
    local EXPECT_USE_LIB_TYPE=$3 # (".so" or ".a") expected type of lib that app should be using

    local LDD_OUTPUT=$(ldd ${APP})
    echo "${LDD_OUTPUT}" | grep "${LIB_NAME}" || echo "No matches found"

    if echo "${LDD_OUTPUT}" | grep -q ${LIB_NAME}.so; then
        local ACTUAL_USE_LIB_TYPE=.so
    else
        local ACTUAL_USE_LIB_TYPE=.a
    fi

    if [ ${ACTUAL_USE_LIB_TYPE} != ${EXPECT_USE_LIB_TYPE} ]; then
        fail "used ${LIB_NAME}${ACTUAL_USE_LIB_TYPE}, but expected to use ${LIB_NAME}${EXPECT_USE_LIB_TYPE}"
    fi
}

# if only shared libssl.so/libcrypto.so are available, that's what should get used
build_myapp BUILD_SHARED_LIBS=ON install-shared .so
build_myapp BUILD_SHARED_LIBS=OFF install-shared .so

# if only static libssl.a/libcrypto.a are available, that's what should get used
build_myapp BUILD_SHARED_LIBS=ON install-static .a
build_myapp BUILD_SHARED_LIBS=OFF install-static .a

# if both shared libssl.so/libcrypto.so and static libssl.a/libcrypto.a are available...
build_myapp BUILD_SHARED_LIBS=ON install-both .so # myapp should use libssl.so/libcrypto.so
build_myapp BUILD_SHARED_LIBS=OFF install-both .a # myapp should use libssl.a/libcrypto.a

# ------------------------------------------------------- #
#           Test for the static library constructor       #
# ------------------------------------------------------- #
rm -rf "${MYAPP_SRC_DIR:?}"
mkdir -p ${MYAPP_SRC_DIR}
sync

cat <<EOF > ${MYAPP_SRC_DIR}/static_constructor_test.c
#include <stdint.h>
#include "openssl/bn.h"
extern uint8_t OPENSSL_cpucap_initialized;
int main() {
  BIGNUM *a = BN_new();
  return (OPENSSL_cpucap_initialized == 1 ? 0 : 1);
}
EOF

# create installation with static libcrypto.a
install_aws_lc install-static BUILD_SHARED_LIBS=OFF

# compile the test app with libcrypto.a
${CC} ${MYAPP_SRC_DIR}/static_constructor_test.c ${SCRATCH_DIR}/install-static/lib/libcrypto.a -pthread -I${SCRATCH_DIR}/install-static/include -o ${MYAPP_SRC_DIR}/static_constructor_test

# verify that the test app returns success
${MYAPP_SRC_DIR}/static_constructor_test || fail "static library constructor has not been executed"
