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
    cp ${BUILD_DIR}/check-linkage.sh "${SCRATCH_DIR}/${1}-check-linkage.sh"
}

# create installation with shared libssl.so/libcrypto.so
install_aws_lc install-shared BUILD_SHARED_LIBS=ON

# create installation with static libssl.a/libcrypto.a
install_aws_lc install-static BUILD_SHARED_LIBS=OFF

# create installation with both shared libssl.so/libcrypto.so and static libssl.a/libcrypto.a
install_aws_lc install-both BUILD_SHARED_LIBS=OFF
install_aws_lc install-both BUILD_SHARED_LIBS=ON

# Verify the pkg-config files installed by a default (non-dist-pkg) build.
# Default Linux builds enable the OpenSSL shim, so the OpenSSL package names
# (openssl, libcrypto, libssl) must always resolve. Shared builds use -awslc
# suffixed libraries plus OpenSSL-named compat pc files; static builds
# install the OpenSSL names directly.
verify_pkgconfig_files() {
    local INSTALL_DIR=${SCRATCH_DIR}/$1
    local LIB_SUFFIX=$2 # "-awslc" when libraries are suffixed, "" otherwise

    local LIB_DIR=lib
    if [[ -d "${INSTALL_DIR}/lib64" ]]; then
        LIB_DIR=lib64
    fi
    local PC_DIR="${INSTALL_DIR}/${LIB_DIR}/pkgconfig"

    local PC_FILE
    for PC_FILE in aws-lc.pc openssl.pc libcrypto${LIB_SUFFIX}.pc libssl${LIB_SUFFIX}.pc libcrypto.pc libssl.pc; do
        if [[ ! -f "${PC_DIR}/${PC_FILE}" ]]; then
            fail "${PC_FILE} not found in ${PC_DIR}"
        fi
    done

    # The OpenSSL-named files must reference the real library names and the
    # unsuffixed package names.
    grep -q -- "-lcrypto${LIB_SUFFIX}" "${PC_DIR}/libcrypto.pc" || fail "libcrypto.pc does not link -lcrypto${LIB_SUFFIX}"
    grep -q -- "-lssl${LIB_SUFFIX}" "${PC_DIR}/libssl.pc" || fail "libssl.pc does not link -lssl${LIB_SUFFIX}"
    grep -q "Requires: libssl libcrypto" "${PC_DIR}/openssl.pc" || fail "openssl.pc does not require libssl libcrypto"
}

verify_pkgconfig_files install-shared -awslc
verify_pkgconfig_files install-static ""

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

    local LINKAGE_CHECKER="${SCRATCH_DIR}/${2}-check-linkage.sh"

    # The application links libssl explicitly which will find libssl correctly as it embeds rpath.
    # libcrypto is a transient dependency which is picked up, but won't use the rpath.
    # So set LD_LIBRARY_PATH so that the check-linkage.sh script works and the binary can be run.
    local ORIG_LD_LIBRARY_PATH="${LD_LIBRARY_PATH}"

    export LD_LIBRARY_PATH="${SCRATCH_DIR}/${AWS_LC_INSTALL_DIR}/lib${LD_LIBRARY_PATH:+:${LD_LIBRARY_PATH}}"

    test_lib_use "${LINKAGE_CHECKER}" ${BUILD_DIR}/myapp ssl ${EXPECT_USE_LIB_TYPE}
    test_lib_use "${LINKAGE_CHECKER}" ${BUILD_DIR}/myapp crypto ${EXPECT_USE_LIB_TYPE}

    ${BUILD_DIR}/myapp || fail "library constructor has not been executed"

    # Reset LD_LIBRARY_PATH
    export LD_LIBRARY_PATH="${ORIG_LD_LIBRARY_PATH}"
}

# test that app is using expected library
test_lib_use() {
    local LINKAGE_CHECKER=$1
    local APP=$2 # app to examine
    local LIB_NAME=$3 # name of lib that app should be using, without file extension
    local EXPECT_USE_LIB_TYPE=$4 # (".so" or ".a") expected type of lib that app should be using

    if ${LINKAGE_CHECKER} ${APP} ${LIB_NAME}; then
        local ACTUAL_USE_LIB_TYPE=.so
    else
        local ACTUAL_USE_LIB_TYPE=.a
        echo "No matches found"
    fi

    if [ ${ACTUAL_USE_LIB_TYPE} != ${EXPECT_USE_LIB_TYPE} ]; then
        fail "used lib${LIB_NAME}${ACTUAL_USE_LIB_TYPE}, but expected to use lib${LIB_NAME}${EXPECT_USE_LIB_TYPE}"
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
