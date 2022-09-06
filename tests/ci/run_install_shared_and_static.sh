#!/bin/bash
set -exo pipefail
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh
print_system_and_dependency_information

export CMAKE_BUILD_PARALLEL_LEVEL=${NUM_CPU_THREADS}

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
rm -rf ${SCRATCH_DIR}/*

function fail() {
    echo "testf failure: $1"
    exit 1
}

function install_aws_lc() {
    local INSTALL_DIR=${SCRATCH_DIR}/$1
    local BUILD_SHARED_LIBS=$2

    local BUILD_DIR=${SCRATCH_DIR}/build
    rm -rf ${BUILD_DIR}
    ${CMAKE_COMMAND} -H${AWS_LC_DIR} -B${BUILD_DIR} -DCMAKE_INSTALL_PREFIX=${INSTALL_DIR} -DBUILD_TESTING=OFF -D${BUILD_SHARED_LIBS}
    ${CMAKE_COMMAND} --build ${BUILD_DIR} --target install
}

# create installation with libssl.so
install_aws_lc install-shared BUILD_SHARED_LIBS=ON

# create installation with libssl.a
install_aws_lc install-static BUILD_SHARED_LIBS=OFF

# create installation with both libssl.so and libssl.a
install_aws_lc install-both BUILD_SHARED_LIBS=OFF
install_aws_lc install-both BUILD_SHARED_LIBS=ON

# write out source of a small cmake project, containing:
# - mylib: a library that uses AWS-LC
# - myapp: executable that uses mylib
MYAPP_SRC_DIR=${SCRATCH_DIR}/myapp-src
rm -rf ${MYAPP_SRC_DIR}
mkdir -p ${MYAPP_SRC_DIR}

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

    local BUILD_DIR=${SCRATCH_DIR}/build
    rm -rf ${BUILD_DIR}

    cmake -H${MYAPP_SRC_DIR} -B${BUILD_DIR} -D${BUILD_SHARED_LIBS} -DCMAKE_PREFIX_PATH=${SCRATCH_DIR}/${AWS_LC_INSTALL_DIR}
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

    if ldd ${APP} | grep -q ${LIB_NAME}.so; then
        local ACTUAL_USE_LIB_TYPE=.so
    else
        local ACTUAL_USE_LIB_TYPE=.a
    fi

    if [ ${ACTUAL_USE_LIB_TYPE} != ${EXPECT_USE_LIB_TYPE} ]; then
        fail "used ${LIB_NAME}${ACTUAL_USE_LIB_TYPE}, but expected to use ${LIB_NAME}${EXPECT_USE_LIB_TYPE}"
    fi
}

# if only shared libssl.so is available, that's what should get used
build_myapp BUILD_SHARED_LIBS=ON install-shared .so
build_myapp BUILD_SHARED_LIBS=OFF install-shared .so

# # if only static libssl.a is available, that's what should get used
build_myapp BUILD_SHARED_LIBS=ON install-static .a
build_myapp BUILD_SHARED_LIBS=OFF install-static .a

# # if both libssl.so and libssl.a are available...
build_myapp BUILD_SHARED_LIBS=ON install-both .so # myapp should choose libssl.so
build_myapp BUILD_SHARED_LIBS=OFF install-both .a # myapp should choose libssl.a
