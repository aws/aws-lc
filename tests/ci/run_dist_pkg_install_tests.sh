#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -euo pipefail

source tests/ci/common_posix_setup.sh

export CMAKE_BUILD_PARALLEL_LEVEL=${NUM_CPU_THREADS}

# Set up environment.
#
# ROOT
#  |
#  - AWS_LC_DIR
#  |
#  - SCRATCH_FOLDER
#    |
#    - BUILD_DIR
#    - install-dist-pkg-shared
#    - install-dist-pkg-shim-shared
#    - install-dist-pkg-static
#    - install-dist-pkg-shim-static
#    - MYAPP_SRC

# Assumes script is executed from the root of aws-lc directory
AWS_LC_DIR=$(pwd)
ROOT=$(realpath ${AWS_LC_DIR}/..)

SCRATCH_DIR=${ROOT}/SCRATCH_AWSLC_DIST_PKG_TESTS
mkdir -p ${SCRATCH_DIR}
rm -rf "${SCRATCH_DIR:?}"/*
sync

function fail() {
    echo "TEST FAILURE: $1"
    exit 1
}

# Detect library directory (lib or lib64)
function get_lib_dir() {
    local INSTALL_DIR=$1
    if [[ -d "${INSTALL_DIR}/lib64" ]]; then
        echo "lib64"
    else
        echo "lib"
    fi
}

function install_aws_lc_dist_pkg() {
    local INSTALL_DIR=${SCRATCH_DIR}/$1
    local BUILD_SHARED_LIBS=$2  # "BUILD_SHARED_LIBS=ON" or "BUILD_SHARED_LIBS=OFF"
    local OPENSSL_SHIM=$3       # "ON" or "OFF"

    local BUILD_DIR=${SCRATCH_DIR}/build
    rm -rf "${BUILD_DIR:?}"
    sync

    local CMAKE_FLAGS=(
        "-H${AWS_LC_DIR}"
        "-B${BUILD_DIR}"
        "-GNinja"
        "-DCMAKE_INSTALL_PREFIX=${INSTALL_DIR}"
        "-DBUILD_TESTING=OFF"
        "-DENABLE_DIST_PKG=ON"
        "-DBUILD_SHARED_LIBS=${BUILD_SHARED_LIBS}"
    )

    if [[ "${OPENSSL_SHIM}" == "ON" ]]; then
        CMAKE_FLAGS+=("-DENABLE_DIST_PKG_OPENSSL_SHIM=ON")
    fi

    ${CMAKE_COMMAND} "${CMAKE_FLAGS[@]}"
    ${CMAKE_COMMAND} --build "${BUILD_DIR}" --target install
}

# Verify installation structure for ENABLE_DIST_PKG
function verify_dist_pkg_structure() {
    local INSTALL_DIR=${SCRATCH_DIR}/$1
    local LIB_EXT=$2  # ".so" or ".a"
    local OPENSSL_SHIM=$3  # "ON" or "OFF"

    # Detect library directory (lib or lib64)
    local LIB_DIR
    LIB_DIR=$(get_lib_dir "${INSTALL_DIR}")

    echo ""
    echo "=============================================="
    echo "Verifying installation structure for: $1"
    echo "Library directory: ${LIB_DIR}"
    echo "Library extension: ${LIB_EXT}"
    echo "OpenSSL Shim: ${OPENSSL_SHIM}"
    echo "=============================================="

    # Check headers are in aws-lc subdirectory (COHABITANT_HEADERS)
    if [[ ! -d "${INSTALL_DIR}/include/aws-lc/openssl" ]]; then
        fail "Headers not installed in include/aws-lc/openssl/ directory"
    fi

    # Check that at least one expected header exists
    if [[ ! -f "${INSTALL_DIR}/include/aws-lc/openssl/ssl.h" ]]; then
        fail "ssl.h not found in include/aws-lc/openssl/"
    fi

    if [[ ! -f "${INSTALL_DIR}/include/aws-lc/openssl/crypto.h" ]]; then
        fail "crypto.h not found in include/aws-lc/openssl/"
    fi

    # Check libraries have -awslc suffix (SET_LIB_SONAME)
    if [[ "${LIB_EXT}" == ".so" ]]; then
        # For shared libraries, check for .so files
        if [[ ! -f "${INSTALL_DIR}/${LIB_DIR}/libcrypto-awslc.so" ]]; then
            fail "libcrypto-awslc.so not found in ${LIB_DIR}/"
        fi
        if [[ ! -f "${INSTALL_DIR}/${LIB_DIR}/libssl-awslc.so" ]]; then
            fail "libssl-awslc.so not found in ${LIB_DIR}/"
        fi
    else
        # For static libraries, check for .a files
        if [[ ! -f "${INSTALL_DIR}/${LIB_DIR}/libcrypto-awslc.a" ]]; then
            fail "libcrypto-awslc.a not found in ${LIB_DIR}/"
        fi
        if [[ ! -f "${INSTALL_DIR}/${LIB_DIR}/libssl-awslc.a" ]]; then
            fail "libssl-awslc.a not found in ${LIB_DIR}/"
        fi
    fi

    # Check pkg-config files
    if [[ ! -f "${INSTALL_DIR}/${LIB_DIR}/pkgconfig/aws-lc.pc" ]]; then
        fail "aws-lc.pc not found in ${LIB_DIR}/pkgconfig/"
    fi
    if [[ ! -f "${INSTALL_DIR}/${LIB_DIR}/pkgconfig/libcrypto-awslc.pc" ]]; then
        fail "libcrypto-awslc.pc not found in ${LIB_DIR}/pkgconfig/"
    fi
    if [[ ! -f "${INSTALL_DIR}/${LIB_DIR}/pkgconfig/libssl-awslc.pc" ]]; then
        fail "libssl-awslc.pc not found in ${LIB_DIR}/pkgconfig/"
    fi

    # Check OpenSSL shim symlinks
    if [[ "${OPENSSL_SHIM}" == "ON" ]]; then
        # Check header symlink
        if [[ ! -L "${INSTALL_DIR}/include/openssl" ]]; then
            fail "include/openssl symlink not found (OpenSSL shim enabled)"
        fi

        # Verify symlink points to aws-lc/openssl
        local SYMLINK_TARGET
        SYMLINK_TARGET=$(readlink "${INSTALL_DIR}/include/openssl")
        if [[ "${SYMLINK_TARGET}" != "aws-lc/openssl" ]]; then
            fail "include/openssl symlink points to '${SYMLINK_TARGET}' instead of 'aws-lc/openssl'"
        fi

        # Check library symlinks
        if [[ "${LIB_EXT}" == ".so" ]]; then
            if [[ ! -L "${INSTALL_DIR}/${LIB_DIR}/libcrypto.so" ]]; then
                fail "libcrypto.so symlink not found in ${LIB_DIR}/ (OpenSSL shim enabled)"
            fi
            if [[ ! -L "${INSTALL_DIR}/${LIB_DIR}/libssl.so" ]]; then
                fail "libssl.so symlink not found in ${LIB_DIR}/ (OpenSSL shim enabled)"
            fi
        else
            if [[ ! -L "${INSTALL_DIR}/${LIB_DIR}/libcrypto.a" ]]; then
                fail "libcrypto.a symlink not found in ${LIB_DIR}/ (OpenSSL shim enabled)"
            fi
            if [[ ! -L "${INSTALL_DIR}/${LIB_DIR}/libssl.a" ]]; then
                fail "libssl.a symlink not found in ${LIB_DIR}/ (OpenSSL shim enabled)"
            fi
        fi

        # Check openssl.pc exists
        if [[ ! -f "${INSTALL_DIR}/${LIB_DIR}/pkgconfig/openssl.pc" ]]; then
            fail "openssl.pc not found in ${LIB_DIR}/pkgconfig/ (OpenSSL shim enabled)"
        fi

        # OpenSSL compat pkg-config files must exist and must not reference
        # the cohabitant include directory.
        local PC_FILE
        for PC_FILE in libcrypto.pc libssl.pc; do
            local PC_PATH="${INSTALL_DIR}/${LIB_DIR}/pkgconfig/${PC_FILE}"
            if [[ ! -f "${PC_PATH}" ]]; then
                fail "${PC_FILE} not found in ${LIB_DIR}/pkgconfig/ (OpenSSL shim enabled)"
            fi
            if grep -q "include/aws-lc" "${PC_PATH}"; then
                fail "${PC_FILE} references the cohabitant include directory"
            fi
        done
    else
        # When OpenSSL shim is disabled, symlinks should NOT exist
        if [[ -e "${INSTALL_DIR}/include/openssl" ]]; then
            fail "include/openssl should not exist when OpenSSL shim is disabled"
        fi

        if [[ "${LIB_EXT}" == ".so" ]]; then
            if [[ -e "${INSTALL_DIR}/${LIB_DIR}/libcrypto.so" ]]; then
                fail "libcrypto.so should not exist in ${LIB_DIR}/ when OpenSSL shim is disabled"
            fi
            if [[ -e "${INSTALL_DIR}/${LIB_DIR}/libssl.so" ]]; then
                fail "libssl.so should not exist in ${LIB_DIR}/ when OpenSSL shim is disabled"
            fi
        else
            if [[ -e "${INSTALL_DIR}/${LIB_DIR}/libcrypto.a" ]]; then
                fail "libcrypto.a should not exist in ${LIB_DIR}/ when OpenSSL shim is disabled"
            fi
            if [[ -e "${INSTALL_DIR}/${LIB_DIR}/libssl.a" ]]; then
                fail "libssl.a should not exist in ${LIB_DIR}/ when OpenSSL shim is disabled"
            fi
        fi

        # OpenSSL compat pkg-config files should NOT exist either
        local PC_FILE
        for PC_FILE in openssl.pc libcrypto.pc libssl.pc; do
            if [[ -e "${INSTALL_DIR}/${LIB_DIR}/pkgconfig/${PC_FILE}" ]]; then
                fail "${PC_FILE} should not exist when OpenSSL shim is disabled"
            fi
        done
    fi

    echo "Installation structure verified successfully!"
}

# Setup test application source
function setup_test_app() {
    local MYAPP_SRC_DIR=${SCRATCH_DIR}/myapp-src
    rm -rf "${MYAPP_SRC_DIR:?}"
    mkdir -p ${MYAPP_SRC_DIR}
    sync

    cat <<EOF > ${MYAPP_SRC_DIR}/mylib.c
#include <openssl/crypto.h>
#include <stdio.h>

void mylib_init(void) {
    printf("AWS-LC version: %s\\n", OpenSSL_version(OPENSSL_VERSION));
}
EOF

    cat <<EOF > ${MYAPP_SRC_DIR}/myapp.c
extern void mylib_init(void);
int main() {
    mylib_init();
    return 0;
}
EOF

    cat <<EOF > ${MYAPP_SRC_DIR}/CMakeLists.txt
cmake_minimum_required(VERSION 3.5)
project(myapp C)

add_library(mylib mylib.c)
find_package(ssl REQUIRED)
target_link_libraries(mylib PRIVATE AWS::ssl AWS::crypto)

add_executable(myapp myapp.c)
target_link_libraries(myapp PRIVATE mylib)
EOF
}

# Build and run test app using CMake find_package
function test_cmake_find_package() {
    local INSTALL_NAME=$1
    local BUILD_SHARED_LIBS=$2
    local INSTALL_DIR=${SCRATCH_DIR}/${INSTALL_NAME}

    # Detect library directory (lib or lib64)
    local LIB_DIR
    LIB_DIR=$(get_lib_dir "${INSTALL_DIR}")

    echo ""
    echo "=============================================="
    echo "Testing CMake find_package for: ${INSTALL_NAME}"
    echo "BUILD_SHARED_LIBS: ${BUILD_SHARED_LIBS}"
    echo "Library directory: ${LIB_DIR}"
    echo "=============================================="

    local BUILD_DIR=${SCRATCH_DIR}/build-myapp
    rm -rf "${BUILD_DIR:?}"
    sync

    ${CMAKE_COMMAND} \
        -H${SCRATCH_DIR}/myapp-src \
        -B${BUILD_DIR} \
        -GNinja \
        -DBUILD_SHARED_LIBS=${BUILD_SHARED_LIBS} \
        -DCMAKE_PREFIX_PATH=${INSTALL_DIR}

    ${CMAKE_COMMAND} --build ${BUILD_DIR}

    # Set library path for running
    local ORIG_LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-}"
    export LD_LIBRARY_PATH="${INSTALL_DIR}/${LIB_DIR}${LD_LIBRARY_PATH:+:${LD_LIBRARY_PATH}}"

    # Run the application
    ${BUILD_DIR}/myapp || fail "Test application failed to run"

    export LD_LIBRARY_PATH="${ORIG_LD_LIBRARY_PATH}"

    echo "CMake find_package test passed!"
}

# Test pkg-config
function test_pkg_config() {
    local INSTALL_NAME=$1
    local PC_NAME=$2  # e.g., "aws-lc" or "openssl"
    local IS_STATIC=$3  # "ON" for static, "OFF" for shared
    local INSTALL_DIR=${SCRATCH_DIR}/${INSTALL_NAME}

    # Detect library directory (lib or lib64)
    local LIB_DIR
    LIB_DIR=$(get_lib_dir "${INSTALL_DIR}")

    # Set pkg-config --static flag for static builds
    local PKG_CONFIG_STATIC_FLAG=""
    if [[ "${IS_STATIC}" == "ON" ]]; then
        PKG_CONFIG_STATIC_FLAG="--static"
    fi

    echo ""
    echo "=============================================="
    echo "Testing pkg-config for: ${INSTALL_NAME}"
    echo "Package name: ${PC_NAME}"
    echo "Library directory: ${LIB_DIR}"
    echo "Static: ${IS_STATIC}"
    echo "=============================================="

    export PKG_CONFIG_PATH="${INSTALL_DIR}/${LIB_DIR}/pkgconfig"

    # Check if package exists
    if ! pkg-config --exists "${PC_NAME}"; then
        fail "pkg-config cannot find package: ${PC_NAME}"
    fi

    # Get and display flags
    local CFLAGS
    CFLAGS=$(pkg-config --cflags "${PC_NAME}")
    local LIBS
    LIBS=$(pkg-config ${PKG_CONFIG_STATIC_FLAG} --libs "${PC_NAME}")

    echo "CFLAGS: ${CFLAGS}"
    echo "LIBS: ${LIBS}"

    # Build a simple test using pkg-config
    local TEST_DIR=${SCRATCH_DIR}/pkgconfig-test
    rm -rf "${TEST_DIR:?}"
    mkdir -p ${TEST_DIR}

    cat <<EOF > ${TEST_DIR}/test.c
#include <openssl/crypto.h>
#include <stdio.h>
int main() {
    OpenSSL_version(OPENSSL_VERSION);
    printf("pkg-config test passed\\n");
    return 0;
}
EOF

    # Compile using pkg-config flags
    ${CC:-cc} ${TEST_DIR}/test.c ${CFLAGS} ${LIBS} -o ${TEST_DIR}/test

    # Run
    local ORIG_LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-}"
    export LD_LIBRARY_PATH="${INSTALL_DIR}/${LIB_DIR}${LD_LIBRARY_PATH:+:${LD_LIBRARY_PATH}}"

    ${TEST_DIR}/test || fail "pkg-config test application failed to run"

    export LD_LIBRARY_PATH="${ORIG_LD_LIBRARY_PATH}"
    unset PKG_CONFIG_PATH

    echo "pkg-config test passed for ${PC_NAME}!"
}

# Verify the OpenSSL compat pkg-config files behave like genuine OpenSSL's:
# all three names resolve, the cohabitant include directory does not leak,
# and a pc file declaring 'Requires.private: libcrypto' (the pattern shipped
# by libssh2 and others) resolves.
function test_openssl_compat_pkg_config() {
    local INSTALL_NAME=$1
    local INSTALL_DIR=${SCRATCH_DIR}/${INSTALL_NAME}

    # Detect library directory (lib or lib64)
    local LIB_DIR
    LIB_DIR=$(get_lib_dir "${INSTALL_DIR}")

    echo ""
    echo "=============================================="
    echo "Testing OpenSSL compat pkg-config files for: ${INSTALL_NAME}"
    echo "=============================================="

    export PKG_CONFIG_PATH="${INSTALL_DIR}/${LIB_DIR}/pkgconfig"

    local PC_NAME
    for PC_NAME in openssl libcrypto libssl; do
        if ! pkg-config --exists "${PC_NAME}"; then
            fail "pkg-config cannot find package: ${PC_NAME}"
        fi
        local CFLAGS
        CFLAGS=$(pkg-config --cflags "${PC_NAME}")
        echo "${PC_NAME} CFLAGS: ${CFLAGS}"
        if [[ "${CFLAGS}" == *"include/aws-lc"* ]]; then
            fail "cohabitant include directory leaked into '${PC_NAME}' Cflags: ${CFLAGS}"
        fi
    done

    # The compat files must still link the suffixed libraries.
    local LIBS
    LIBS=$(pkg-config --libs libcrypto)
    if [[ "${LIBS}" != *"-lcrypto-awslc"* ]]; then
        fail "compat libcrypto.pc does not link libcrypto-awslc: ${LIBS}"
    fi
    LIBS=$(pkg-config --libs libssl)
    if [[ "${LIBS}" != *"-lssl-awslc"* ]]; then
        fail "compat libssl.pc does not link libssl-awslc: ${LIBS}"
    fi

    # Reproduce the third-party consumer pattern: pkg-config resolves
    # Requires.private to compute Cflags, so this fails unless libcrypto.pc
    # exists under that exact filename.
    local CONSUMER_DIR=${SCRATCH_DIR}/pkgconfig-consumer
    rm -rf "${CONSUMER_DIR:?}"
    mkdir -p ${CONSUMER_DIR}
    cat <<EOF > ${CONSUMER_DIR}/shimconsumer.pc
prefix=/nonexistent
Name: shimconsumer
Description: Synthetic consumer of OpenSSL via pkg-config
Version: 1.0
Requires.private: libcrypto
Libs: -L\${prefix}/lib -lshimconsumer
Cflags: -I\${prefix}/include
EOF

    export PKG_CONFIG_PATH="${CONSUMER_DIR}:${PKG_CONFIG_PATH}"
    if ! pkg-config --cflags --libs shimconsumer > /dev/null; then
        fail "pkg-config failed to resolve 'Requires.private: libcrypto' for a consumer package"
    fi

    unset PKG_CONFIG_PATH

    echo "OpenSSL compat pkg-config tests passed!"
}

# Main test execution

echo ""
echo "=============================================="
echo "Setting up test application"
echo "=============================================="
setup_test_app

# Test 1: ENABLE_DIST_PKG only (shared libs)
echo ""
echo "############################################"
echo "# Test 1: ENABLE_DIST_PKG (shared libs)   #"
echo "############################################"
install_aws_lc_dist_pkg install-dist-pkg-shared ON OFF
verify_dist_pkg_structure install-dist-pkg-shared .so OFF
test_cmake_find_package install-dist-pkg-shared ON
test_pkg_config install-dist-pkg-shared aws-lc OFF

# Symbol versioning tests (reuse the shared-lib install from Test 1)
echo ""
echo "############################################"
echo "# Symbol Versioning Tests                  #"
echo "############################################"
"${AWS_LC_DIR}/tests/ci/run_symbol_version_test.sh" "${SCRATCH_DIR}/install-dist-pkg-shared"

# Test 2: ENABLE_DIST_PKG + OPENSSL_SHIM (shared libs)
echo ""
echo "############################################"
echo "# Test 2: ENABLE_DIST_PKG + SHIM (shared) #"
echo "############################################"
install_aws_lc_dist_pkg install-dist-pkg-shim-shared ON ON
verify_dist_pkg_structure install-dist-pkg-shim-shared .so ON
test_cmake_find_package install-dist-pkg-shim-shared ON
test_pkg_config install-dist-pkg-shim-shared aws-lc OFF
test_pkg_config install-dist-pkg-shim-shared openssl OFF
test_pkg_config install-dist-pkg-shim-shared libcrypto OFF
test_openssl_compat_pkg_config install-dist-pkg-shim-shared

# Test 3: ENABLE_DIST_PKG only (static libs)
echo ""
echo "############################################"
echo "# Test 3: ENABLE_DIST_PKG (static libs)   #"
echo "############################################"
install_aws_lc_dist_pkg install-dist-pkg-static OFF OFF
verify_dist_pkg_structure install-dist-pkg-static .a OFF
test_cmake_find_package install-dist-pkg-static OFF
test_pkg_config install-dist-pkg-static aws-lc ON

# Test 4: ENABLE_DIST_PKG + OPENSSL_SHIM (static libs)
echo ""
echo "############################################"
echo "# Test 4: ENABLE_DIST_PKG + SHIM (static) #"
echo "############################################"
install_aws_lc_dist_pkg install-dist-pkg-shim-static OFF ON
verify_dist_pkg_structure install-dist-pkg-shim-static .a ON
test_cmake_find_package install-dist-pkg-shim-static OFF
test_pkg_config install-dist-pkg-shim-static aws-lc ON
test_pkg_config install-dist-pkg-shim-static openssl ON
test_pkg_config install-dist-pkg-shim-static libcrypto ON
test_openssl_compat_pkg_config install-dist-pkg-shim-static

echo ""
echo "############################################"
echo "# All ENABLE_DIST_PKG tests passed!       #"
echo "############################################"
