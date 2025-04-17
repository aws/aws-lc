#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

source tests/ci/common_posix_setup.sh

if [[ -z "${RUST_OPENSSL_SRC_DIR}" ]]; then
    echo "RUST_OPENSSL_SRC_DIR environment variable must be set"
    exit 1
fi

# Create build directory and navigate to it
AWS_LC_SRC_DIR="${SRC_ROOT}"
AWS_LC_BUILD_DIR="${SYS_ROOT}/aws-lc-build"
AWS_LC_SHARED_INSTALL_DIR="${SYS_ROOT}/aws-lc-install-shared"
AWS_LC_STATIC_INSTALL_DIR="${SYS_ROOT}/aws-lc-install-static"

function validate_rust_openssl() {
    OPENSSL_DIR="${1}"
    OPENSSL_STATIC="${2}"
    
    # Find the path to libcrypto.so and store its directory as it can be different depending on OS distribution
    ADDITIONAL_ENV_VARS=()
    if [[ "${OPENSSL_STATIC}" -eq 0 ]]; then
        LIB_DIR=$(find "${OPENSSL_DIR}" -name "libcrypto.so" -exec dirname {} \; | head -n 1)
        ADDITIONAL_ENV_VARS+=("LD_LIBRARY_PATH=${LIB_DIR}:${LD_LIBRARY_PATH}")
    fi
    
    pushd "${RUST_OPENSSL_SRC_DIR}"
    cargo -v clean
    env OPENSSL_DIR="${OPENSSL_DIR}" OPENSSL_STATIC="${OPENSSL_STATIC}" "${ADDITIONAL_ENV_VARS[@]}" \
    cargo -v test -p openssl-sys --release --no-default-features "${@:3}"
    env OPENSSL_DIR="${OPENSSL_DIR}" OPENSSL_STATIC="${OPENSSL_STATIC}" "${ADDITIONAL_ENV_VARS[@]}" \
    cargo -v test -p openssl --release --no-default-features "${@:3}"
    
    popd # "${RUST_OPENSSL_SRC_DIR}"
}

AWS_LC_BUILD_ARGS=("-DBUILD_TESTING=OFF" "-DBUILD_TOOL=OFF" "-DCMAKE_BUILD_TYPE=RelWithDebInfo")

aws_lc_build "${AWS_LC_SRC_DIR}" "${AWS_LC_BUILD_DIR}" "${AWS_LC_SHARED_INSTALL_DIR}" "${AWS_LC_BUILD_ARGS[@]}" -DBUILD_SHARED_LIBS=1
aws_lc_build "${AWS_LC_SRC_DIR}" "${AWS_LC_BUILD_DIR}" "${AWS_LC_STATIC_INSTALL_DIR}" "${AWS_LC_BUILD_ARGS[@]}" -DBUILD_SHARED_LIBS=0

validate_rust_openssl "${AWS_LC_SHARED_INSTALL_DIR}" 0
validate_rust_openssl "${AWS_LC_STATIC_INSTALL_DIR}" 1

validate_rust_openssl "${AWS_LC_SHARED_INSTALL_DIR}" 0 -F bindgen
validate_rust_openssl "${AWS_LC_STATIC_INSTALL_DIR}" 1 -F bindgen
