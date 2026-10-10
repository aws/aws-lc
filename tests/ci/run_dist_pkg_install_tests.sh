#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -euo pipefail

source tests/ci/common_posix_setup.sh
source tests/ci/pkgconfig_test_helpers.sh

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
#    - install-dist-pkg-shim-nossl
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

function install_aws_lc_dist_pkg() {
    local INSTALL_DIR=${SCRATCH_DIR}/$1
    local BUILD_SHARED_LIBS=$2  # "BUILD_SHARED_LIBS=ON" or "BUILD_SHARED_LIBS=OFF"
    local OPENSSL_SHIM=$3       # "ON" or "OFF"
    local BUILD_LIBSSL=${4:-ON} # "ON" or "OFF"

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
        "-DBUILD_LIBSSL=${BUILD_LIBSSL}"
    )

    if [[ "${OPENSSL_SHIM}" == "ON" ]]; then
        CMAKE_FLAGS+=("-DENABLE_DIST_PKG_OPENSSL_SHIM=ON")
    fi

    if [[ "${BUILD_LIBSSL}" == "OFF" ]]; then
        # The bssl tool needs libssl.
        CMAKE_FLAGS+=("-DBUILD_TOOL=OFF")
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

        # Shim pc files must exist and must not name the cohabitant include dir.
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

        # Nor should the shim pc files exist
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

# Setup an isolated consumer that uses CMake's *standard* OpenSSL discovery --
# find_package(OpenSSL) and the OpenSSL::Crypto/OpenSSL::SSL imported targets,
# not AWS-LC's own find_package(ssl)/AWS::crypto package. This is the path that
# exposed the suffixed-Libs bug; see the regression guard below.
function setup_openssl_consumer_app() {
    local SRC_DIR=${SCRATCH_DIR}/openssl-consumer-src
    rm -rf "${SRC_DIR:?}"
    mkdir -p ${SRC_DIR}
    sync

    cat <<EOF > ${SRC_DIR}/main.c
#include <openssl/crypto.h>
#include <stdio.h>
#ifdef CONSUMER_USE_SSL
#include <openssl/ssl.h>
#endif

int main(void) {
#ifdef CONSUMER_USE_SSL
    OPENSSL_init_ssl(0, NULL);
#endif
    printf("find_package(OpenSSL) consumer linked against: %s\\n",
           OpenSSL_version(OPENSSL_VERSION));
    return 0;
}
EOF

    cat <<'EOF' > ${SRC_DIR}/CMakeLists.txt
cmake_minimum_required(VERSION 3.5)
project(opensslconsumer C)

# Standard OpenSSL discovery, exactly as a third-party project would do it.
find_package(OpenSSL REQUIRED)

if(NOT EXPECTED_PREFIX)
  message(FATAL_ERROR "EXPECTED_PREFIX must be set to the install prefix under test")
endif()
get_filename_component(EXPECTED_PREFIX_REAL "${EXPECTED_PREFIX}" REALPATH)

# Fail if CMake selected a system OpenSSL rather than the install under test.
function(assert_within_prefix var_name path)
  if("${path}" STREQUAL "")
    return()
  endif()
  get_filename_component(_resolved "${path}" REALPATH)
  string(FIND "${_resolved}" "${EXPECTED_PREFIX_REAL}/" _idx)
  if(NOT _idx EQUAL 0)
    message(FATAL_ERROR
      "find_package(OpenSSL) resolved ${var_name} to '${path}' (real path "
      "'${_resolved}'), which is outside the install prefix under test "
      "'${EXPECTED_PREFIX_REAL}'. A system OpenSSL was selected.")
  endif()
endfunction()

assert_within_prefix(OPENSSL_INCLUDE_DIR "${OPENSSL_INCLUDE_DIR}")
assert_within_prefix(OPENSSL_CRYPTO_LIBRARY "${OPENSSL_CRYPTO_LIBRARY}")
if(WITH_SSL)
  assert_within_prefix(OPENSSL_SSL_LIBRARY "${OPENSSL_SSL_LIBRARY}")
endif()

# Regression guard for the suffixed-Libs bug. FindOpenSSL resolves openssl.pc
# through pkg_check_modules and recognizes only the exact library names
# 'ssl'/'crypto' (plus 'dl'/'z'). It appends anything else to the imported
# targets' INTERFACE_LINK_LIBRARIES verbatim, as a bare name with no -L path,
# so the link fails with "cannot find -lcrypto-<product>".
foreach(_target OpenSSL::Crypto OpenSSL::SSL)
  if(TARGET ${_target})
    get_target_property(_iface ${_target} INTERFACE_LINK_LIBRARIES)
    if(_iface)
      foreach(_lib IN LISTS _iface)
        if(_lib MATCHES "^(-l)?(lib)?(ssl|crypto)-")
          message(FATAL_ERROR
            "FindOpenSSL treated '${_lib}' as a bare extra dependency of "
            "${_target} (INTERFACE_LINK_LIBRARIES: ${_iface}). The shim "
            "pkg-config modules must report unsuffixed OpenSSL library names.")
        endif()
      endforeach()
    endif()
  endif()
endforeach()

message(STATUS "OPENSSL_VERSION: ${OPENSSL_VERSION}")
message(STATUS "OPENSSL_INCLUDE_DIR: ${OPENSSL_INCLUDE_DIR}")
message(STATUS "OPENSSL_CRYPTO_LIBRARY: ${OPENSSL_CRYPTO_LIBRARY}")
message(STATUS "OPENSSL_SSL_LIBRARY: ${OPENSSL_SSL_LIBRARY}")

add_executable(opensslconsumer main.c)
target_link_libraries(opensslconsumer PRIVATE OpenSSL::Crypto)

if(WITH_SSL)
  if(NOT TARGET OpenSSL::SSL)
    message(FATAL_ERROR "OpenSSL::SSL target was not created")
  endif()
  target_link_libraries(opensslconsumer PRIVATE OpenSSL::SSL)
  target_compile_definitions(opensslconsumer PRIVATE CONSUMER_USE_SSL)
endif()
EOF
}

# Configure, build and run the standard-CMake OpenSSL consumer. Building it
# matters: the failure only surfaces in the final link command.
function test_cmake_find_package_openssl() {
    local INSTALL_NAME=$1
    local IS_STATIC=$2      # "ON" for static, "OFF" for shared
    local WITH_SSL=${3:-ON}
    local INSTALL_DIR=${SCRATCH_DIR}/${INSTALL_NAME}

    local LIB_DIR
    LIB_DIR=$(get_lib_dir "${INSTALL_DIR}")

    echo ""
    echo "=============================================="
    echo "Testing standard CMake find_package(OpenSSL) for: ${INSTALL_NAME}"
    echo "Static: ${IS_STATIC}  WITH_SSL: ${WITH_SSL}"
    echo "=============================================="

    local BUILD_DIR=${SCRATCH_DIR}/build-openssl-consumer
    rm -rf "${BUILD_DIR:?}"
    sync

    local CMAKE_FLAGS=(
        "-H${SCRATCH_DIR}/openssl-consumer-src"
        "-B${BUILD_DIR}"
        "-GNinja"
        "-DEXPECTED_PREFIX=${INSTALL_DIR}"
        "-DWITH_SSL=${WITH_SSL}"
        # FindOpenSSL hints come from OPENSSL_ROOT_DIR and pkg-config, so point
        # both at the prefix under test; a system OpenSSL must not win.
        "-DOPENSSL_ROOT_DIR=${INSTALL_DIR}"
    )
    if [[ "${IS_STATIC}" == "ON" ]]; then
        # Makes FindOpenSSL use --static, resolving Requires.private.
        CMAKE_FLAGS+=("-DOPENSSL_USE_STATIC_LIBS=TRUE")
    fi

    local PKG_CONFIG_PATH="${INSTALL_DIR}/${LIB_DIR}/pkgconfig"
    export PKG_CONFIG_PATH

    ${CMAKE_COMMAND} "${CMAKE_FLAGS[@]}"
    ${CMAKE_COMMAND} --build "${BUILD_DIR}"

    run_with_library_path "${INSTALL_DIR}/${LIB_DIR}" \
        "${BUILD_DIR}/opensslconsumer" || fail "find_package(OpenSSL) consumer failed to run"

    echo "Standard CMake find_package(OpenSSL) test passed!"
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

    # Run the application with the installed shared libraries.
    run_with_library_path "${INSTALL_DIR}/${LIB_DIR}" \
        "${BUILD_DIR}/myapp" || fail "Test application failed to run"

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

    local PKG_CONFIG_PATH="${INSTALL_DIR}/${LIB_DIR}/pkgconfig"
    export PKG_CONFIG_PATH

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

    run_with_library_path "${INSTALL_DIR}/${LIB_DIR}" \
        "${TEST_DIR}/test" || fail "pkg-config test application failed to run"

    echo "pkg-config test passed for ${PC_NAME}!"
}

# Verify the shim-facing modules describe the unsuffixed OpenSSL interface:
# all three names resolve, the cohabitant include dir does not leak, and the
# module and linker names they reference are unsuffixed.
function test_openssl_compat_pkg_config() {
    local INSTALL_NAME=$1
    local IS_STATIC=$2  # "ON" for static, "OFF" for shared
    local INSTALL_DIR=${SCRATCH_DIR}/${INSTALL_NAME}

    # Detect library directory (lib or lib64)
    local LIB_DIR
    LIB_DIR=$(get_lib_dir "${INSTALL_DIR}")
    local PC_DIR="${INSTALL_DIR}/${LIB_DIR}/pkgconfig"

    local PKG_CONFIG_STATIC_FLAG=""
    if [[ "${IS_STATIC}" == "ON" ]]; then
        PKG_CONFIG_STATIC_FLAG="--static"
    fi

    local SUFFIX
    SUFFIX=$(require_product_suffix "${PC_DIR}")

    echo ""
    echo "=============================================="
    echo "Testing OpenSSL shim pkg-config modules for: ${INSTALL_NAME}"
    echo "Static: ${IS_STATIC}"
    echo "Product suffix: '${SUFFIX}'"
    echo "=============================================="

    local PKG_CONFIG_PATH="${PC_DIR}"
    export PKG_CONFIG_PATH

    # All three OpenSSL module names must resolve from the install prefix.
    local PC_NAME
    for PC_NAME in openssl libcrypto libssl; do
        if ! pkg-config --exists "${PC_NAME}"; then
            fail "pkg-config cannot find package: ${PC_NAME}"
        fi

        # The shim includedir is the plain include/ directory, where the shim
        # installs its include/openssl symlink. Emitting include/aws-lc here
        # would leak it into every consumer of libcrypto.
        local RESOLVED_INCLUDEDIR
        RESOLVED_INCLUDEDIR=$(pkg-config --variable=includedir "${PC_NAME}")
        if [[ "${RESOLVED_INCLUDEDIR}" != "${INSTALL_DIR}/include" ]]; then
            fail "'${PC_NAME}' includedir is '${RESOLVED_INCLUDEDIR}', expected '${INSTALL_DIR}/include'"
        fi

        local CFLAGS
        CFLAGS=$(pkg-config --cflags "${PC_NAME}")
        echo "${PC_NAME} CFLAGS: ${CFLAGS}"
        assert_exact_token "${CFLAGS}" "-I${INSTALL_DIR}/include" "'${PC_NAME}' Cflags"
        assert_no_exact_token "${CFLAGS}" "-I${INSTALL_DIR}/include/aws-lc" "'${PC_NAME}' Cflags"

        # No dependency field of a shim-facing file may name a suffixed token.
        assert_no_suffixed_openssl_tokens "${PC_DIR}/${PC_NAME}.pc"
    done

    # Unsuffixed linker names, as exact tokens, with the -L path that resolves
    # them.
    local LIBS
    for PC_NAME in libcrypto openssl; do
        LIBS=$(pkg-config ${PKG_CONFIG_STATIC_FLAG} --libs "${PC_NAME}")
        echo "${PC_NAME} LIBS: ${LIBS}"
        assert_exact_token "${LIBS}" "-L${INSTALL_DIR}/${LIB_DIR}" "'${PC_NAME}' Libs"
        assert_exact_token "${LIBS}" "-lcrypto" "'${PC_NAME}' Libs"
        assert_no_exact_token "${LIBS}" "-lcrypto${SUFFIX}" "'${PC_NAME}' Libs"
        assert_no_exact_token "${LIBS}" "-lssl${SUFFIX}" "'${PC_NAME}' Libs"
    done

    for PC_NAME in libssl openssl; do
        LIBS=$(pkg-config ${PKG_CONFIG_STATIC_FLAG} --libs "${PC_NAME}")
        assert_exact_token "${LIBS}" "-lssl" "'${PC_NAME}' Libs"
    done

    # --static additionally resolves Requires.private/Libs.private.
    LIBS=$(pkg-config --static --libs libssl)
    echo "libssl static LIBS: ${LIBS}"
    assert_exact_token "${LIBS}" "-lssl" "'libssl' static Libs"
    assert_exact_token "${LIBS}" "-lcrypto" "'libssl' static Libs"
    assert_no_exact_token "${LIBS}" "-lcrypto${SUFFIX}" "'libssl' static Libs"

    local SSL_REQUIRES
    SSL_REQUIRES=$(pkg-config --print-requires-private libssl)
    assert_exact_token "${SSL_REQUIRES}" "libcrypto" "'libssl' Requires.private"
    assert_no_exact_token "${SSL_REQUIRES}" "libcrypto${SUFFIX}" "'libssl' Requires.private"

    local OPENSSL_REQUIRES
    OPENSSL_REQUIRES=$(pkg-config --print-requires openssl)
    echo "openssl Requires: ${OPENSSL_REQUIRES}"
    assert_exact_token "${OPENSSL_REQUIRES}" "libcrypto" "'openssl' Requires"
    assert_exact_token "${OPENSSL_REQUIRES}" "libssl" "'openssl' Requires"
    assert_no_exact_token "${OPENSSL_REQUIRES}" "libcrypto${SUFFIX}" "'openssl' Requires"
    assert_no_exact_token "${OPENSSL_REQUIRES}" "libssl${SUFFIX}" "'openssl' Requires"

    # End-to-end: an SSL consumer must compile, link and run through the shim
    # modules alone, proving -lssl/-lcrypto resolve the shim symlinks.
    local SSL_TEST_DIR=${SCRATCH_DIR}/pkgconfig-ssl-test
    rm -rf "${SSL_TEST_DIR:?}"
    mkdir -p ${SSL_TEST_DIR}
    cat <<EOF > ${SSL_TEST_DIR}/test.c
#include <openssl/crypto.h>
#include <openssl/ssl.h>
#include <stdio.h>
int main(void) {
    const SSL_METHOD *method = TLS_method();
    SSL_CTX *ctx = SSL_CTX_new(method);
    if (ctx == NULL) {
        return 1;
    }
    SSL_CTX_free(ctx);
    printf("shim libssl+libcrypto consumer ok: %s\\n",
           OpenSSL_version(OPENSSL_VERSION));
    return 0;
}
EOF

    local SSL_CFLAGS SSL_LIBS
    SSL_CFLAGS=$(pkg-config --cflags libssl libcrypto)
    SSL_LIBS=$(pkg-config ${PKG_CONFIG_STATIC_FLAG} --libs libssl libcrypto)
    echo "ssl consumer CFLAGS: ${SSL_CFLAGS}"
    echo "ssl consumer LIBS: ${SSL_LIBS}"
    assert_exact_token "${SSL_LIBS}" "-lssl" "'libssl libcrypto' Libs"
    assert_exact_token "${SSL_LIBS}" "-lcrypto" "'libssl libcrypto' Libs"

    ${CC:-cc} ${SSL_TEST_DIR}/test.c ${SSL_CFLAGS} ${SSL_LIBS} -o ${SSL_TEST_DIR}/test

    run_with_library_path "${INSTALL_DIR}/${LIB_DIR}" \
        "${SSL_TEST_DIR}/test" || fail "shim libssl+libcrypto consumer failed to run"

    # The libssh2 pattern: pkg-config resolves Requires.private to compute
    # Cflags, so this fails unless libcrypto.pc exists under that exact name.
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

    PKG_CONFIG_PATH="${CONSUMER_DIR}:${PKG_CONFIG_PATH}"
    if ! pkg-config --cflags --libs shimconsumer > /dev/null; then
        fail "pkg-config failed to resolve 'Requires.private: libcrypto' for a consumer package"
    fi

    echo "OpenSSL shim pkg-config tests passed!"
}

# The shim must leave the native cohabitant modules untouched: suffixed module
# and linker names, and the cohabitant include directory.
function test_native_pkg_config_unchanged() {
    local INSTALL_NAME=$1
    local IS_STATIC=$2  # "ON" for static, "OFF" for shared
    local INSTALL_DIR=${SCRATCH_DIR}/${INSTALL_NAME}

    local LIB_DIR
    LIB_DIR=$(get_lib_dir "${INSTALL_DIR}")
    local PC_DIR="${INSTALL_DIR}/${LIB_DIR}/pkgconfig"

    local PKG_CONFIG_STATIC_FLAG=""
    if [[ "${IS_STATIC}" == "ON" ]]; then
        PKG_CONFIG_STATIC_FLAG="--static"
    fi

    local SUFFIX
    SUFFIX=$(require_product_suffix "${PC_DIR}")

    echo ""
    echo "=============================================="
    echo "Testing native cohabitant pkg-config modules for: ${INSTALL_NAME}"
    echo "Product suffix: '${SUFFIX}'"
    echo "=============================================="

    local PKG_CONFIG_PATH="${PC_DIR}"
    export PKG_CONFIG_PATH

    local PC_NAME
    for PC_NAME in "aws-lc" "libcrypto${SUFFIX}" "libssl${SUFFIX}"; do
        if ! pkg-config --exists "${PC_NAME}"; then
            fail "pkg-config cannot find native package: ${PC_NAME}"
        fi
        local RESOLVED_INCLUDEDIR
        RESOLVED_INCLUDEDIR=$(pkg-config --variable=includedir "${PC_NAME}")
        if [[ "${RESOLVED_INCLUDEDIR}" != "${INSTALL_DIR}/include/aws-lc" ]]; then
            fail "native '${PC_NAME}' includedir is '${RESOLVED_INCLUDEDIR}', expected '${INSTALL_DIR}/include/aws-lc'"
        fi
    done

    local LIBS
    LIBS=$(pkg-config ${PKG_CONFIG_STATIC_FLAG} --libs "libcrypto${SUFFIX}")
    echo "libcrypto${SUFFIX} LIBS: ${LIBS}"
    assert_exact_token "${LIBS}" "-lcrypto${SUFFIX}" "native 'libcrypto${SUFFIX}' Libs"
    assert_no_exact_token "${LIBS}" "-lcrypto" "native 'libcrypto${SUFFIX}' Libs"

    LIBS=$(pkg-config ${PKG_CONFIG_STATIC_FLAG} --libs "libssl${SUFFIX}")
    echo "libssl${SUFFIX} LIBS: ${LIBS}"
    assert_exact_token "${LIBS}" "-lssl${SUFFIX}" "native 'libssl${SUFFIX}' Libs"
    assert_no_exact_token "${LIBS}" "-lssl" "native 'libssl${SUFFIX}' Libs"

    local REQUIRES
    REQUIRES=$(pkg-config --print-requires "aws-lc")
    echo "aws-lc Requires: ${REQUIRES}"
    assert_exact_token "${REQUIRES}" "libcrypto${SUFFIX}" "native 'aws-lc' Requires"
    assert_exact_token "${REQUIRES}" "libssl${SUFFIX}" "native 'aws-lc' Requires"
    assert_no_exact_token "${REQUIRES}" "libcrypto" "native 'aws-lc' Requires"
    assert_no_exact_token "${REQUIRES}" "libssl" "native 'aws-lc' Requires"

    REQUIRES=$(pkg-config --print-requires-private "libssl${SUFFIX}")
    assert_exact_token "${REQUIRES}" "libcrypto${SUFFIX}" "native 'libssl${SUFFIX}' Requires.private"
    assert_no_exact_token "${REQUIRES}" "libcrypto" "native 'libssl${SUFFIX}' Requires.private"

    echo "Native cohabitant pkg-config tests passed!"
}

# BUILD_LIBSSL=OFF: no libssl module under either name, and openssl.pc must not
# require one -- a dangling requirement makes 'pkg-config --exists' fail.
function test_pkg_config_no_libssl() {
    local INSTALL_NAME=$1
    local INSTALL_DIR=${SCRATCH_DIR}/${INSTALL_NAME}

    local LIB_DIR
    LIB_DIR=$(get_lib_dir "${INSTALL_DIR}")
    local PC_DIR="${INSTALL_DIR}/${LIB_DIR}/pkgconfig"

    local SUFFIX
    SUFFIX=$(require_product_suffix "${PC_DIR}")

    echo ""
    echo "=============================================="
    echo "Testing BUILD_LIBSSL=OFF pkg-config modules for: ${INSTALL_NAME}"
    echo "Product suffix: '${SUFFIX}'"
    echo "=============================================="

    local PC_FILE
    for PC_FILE in "libssl.pc" "libssl${SUFFIX}.pc"; do
        if [[ -e "${PC_DIR}/${PC_FILE}" ]]; then
            fail "${PC_FILE} should not be installed when BUILD_LIBSSL=OFF"
        fi
    done

    # Nor a dangling libssl symlink: -e follows symlinks, so a dangling one is
    # caught by -L without -e.
    local LIB_FILE
    for LIB_FILE in "libssl.so" "libssl.a" "libssl${SUFFIX}.so" "libssl${SUFFIX}.a"; do
        if [[ -e "${INSTALL_DIR}/${LIB_DIR}/${LIB_FILE}" ]]; then
            fail "${LIB_FILE} should not be installed when BUILD_LIBSSL=OFF"
        fi
        if [[ -L "${INSTALL_DIR}/${LIB_DIR}/${LIB_FILE}" ]]; then
            fail "${LIB_FILE} is a dangling symlink; it should not be installed when BUILD_LIBSSL=OFF"
        fi
    done

    for PC_FILE in "aws-lc.pc" "openssl.pc" "libcrypto.pc" "libcrypto${SUFFIX}.pc"; do
        if [[ ! -f "${PC_DIR}/${PC_FILE}" ]]; then
            fail "${PC_FILE} not found in ${PC_DIR} (BUILD_LIBSSL=OFF)"
        fi
    done

    # Restrict pkg-config to this install. PKG_CONFIG_PATH alone still searches
    # the host's built-in directories, which may contain a system libssl.pc.
    local PKG_CONFIG_PATH=""
    local PKG_CONFIG_LIBDIR="${PC_DIR}"
    export PKG_CONFIG_PATH PKG_CONFIG_LIBDIR

    if pkg-config --exists libssl; then
        fail "pkg-config resolved 'libssl' when BUILD_LIBSSL=OFF"
    fi
    if pkg-config --exists "libssl${SUFFIX}"; then
        fail "pkg-config resolved 'libssl${SUFFIX}' when BUILD_LIBSSL=OFF"
    fi

    # These would fail if the Requires line still named a missing libssl.
    local PC_NAME
    for PC_NAME in openssl libcrypto "aws-lc" "libcrypto${SUFFIX}"; do
        if ! pkg-config --exists "${PC_NAME}"; then
            fail "pkg-config cannot find package '${PC_NAME}' (BUILD_LIBSSL=OFF); it likely still requires a missing libssl"
        fi
    done

    local REQUIRES
    REQUIRES=$(pkg-config --print-requires openssl)
    echo "openssl Requires: ${REQUIRES}"
    assert_exact_token "${REQUIRES}" "libcrypto" "'openssl' Requires (BUILD_LIBSSL=OFF)"
    assert_no_exact_token "${REQUIRES}" "libssl" "'openssl' Requires (BUILD_LIBSSL=OFF)"
    assert_no_exact_token "${REQUIRES}" "libssl${SUFFIX}" "'openssl' Requires (BUILD_LIBSSL=OFF)"

    REQUIRES=$(pkg-config --print-requires "aws-lc")
    echo "aws-lc Requires: ${REQUIRES}"
    assert_exact_token "${REQUIRES}" "libcrypto${SUFFIX}" "native 'aws-lc' Requires (BUILD_LIBSSL=OFF)"
    assert_no_exact_token "${REQUIRES}" "libssl${SUFFIX}" "native 'aws-lc' Requires (BUILD_LIBSSL=OFF)"

    # The shim libcrypto module is still fully unsuffixed.
    local LIBS
    LIBS=$(pkg-config --libs libcrypto)
    echo "libcrypto LIBS: ${LIBS}"
    assert_exact_token "${LIBS}" "-lcrypto" "'libcrypto' Libs (BUILD_LIBSSL=OFF)"
    assert_no_exact_token "${LIBS}" "-lcrypto${SUFFIX}" "'libcrypto' Libs (BUILD_LIBSSL=OFF)"
    assert_no_suffixed_openssl_tokens "${PC_DIR}/libcrypto.pc"
    assert_no_suffixed_openssl_tokens "${PC_DIR}/openssl.pc"

    echo "BUILD_LIBSSL=OFF pkg-config tests passed!"
}

# Main test execution

echo ""
echo "=============================================="
echo "Setting up test applications"
echo "=============================================="
setup_test_app
setup_openssl_consumer_app

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
# test_openssl_compat_pkg_config subsumes a standalone libcrypto compile: it
# token-checks all three OpenSSL module names and compiles/runs a consumer
# against 'libssl libcrypto'.
test_openssl_compat_pkg_config install-dist-pkg-shim-shared OFF
test_cmake_find_package_openssl install-dist-pkg-shim-shared OFF ON

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
test_openssl_compat_pkg_config install-dist-pkg-shim-static ON
# The native pc files are identical across the shared and static shim
# installs, so they are checked once, here, where --static also resolves the
# Requires.private/Libs.private fields.
test_native_pkg_config_unchanged install-dist-pkg-shim-static ON
# The static install reproduces the original FindOpenSSL failure: its
# extra-dependency path only runs when the library it found is a static archive.
test_cmake_find_package_openssl install-dist-pkg-shim-static ON ON

# Test 5: ENABLE_DIST_PKG + OPENSSL_SHIM, BUILD_LIBSSL=OFF
echo ""
echo "############################################"
echo "# Test 5: SHIM + BUILD_LIBSSL=OFF          #"
echo "############################################"
install_aws_lc_dist_pkg install-dist-pkg-shim-nossl ON ON OFF
test_pkg_config_no_libssl install-dist-pkg-shim-nossl
test_pkg_config install-dist-pkg-shim-nossl openssl OFF
# Unlike the shim-shared/shim-static configs, this is the only compile/run
# against the shim modules here, so the libcrypto smoke test stays.
test_pkg_config install-dist-pkg-shim-nossl libcrypto OFF
test_cmake_find_package_openssl install-dist-pkg-shim-nossl OFF OFF

echo ""
echo "############################################"
echo "# All ENABLE_DIST_PKG tests passed!       #"
echo "############################################"
