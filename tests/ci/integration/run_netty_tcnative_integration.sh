#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -euxo pipefail

source tests/ci/common_posix_setup.sh

# Set up environment.

# SRC_ROOT(aws-lc)
#  - SCRATCH_FOLDER
#    - NETTY_TCNATIVE_SRC
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SRC_ROOT}/"scratch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"
NETTY_TCNATIVE_SRC="${SCRATCH_FOLDER}/netty-tcnative"
NETTY_TCNATIVE_GIT_URL="https://github.com/netty/netty-tcnative.git"
NETTY_TCNATIVE_REFSPEC="${1:-main}"
NETTY_TCNATIVE_PATCH_FOLDER="${SRC_ROOT}/tests/ci/integration/netty_tcnative_patch"

function build_netty_tcnative() {
    pushd "${NETTY_TCNATIVE_SRC}"
    
    local PKG_CONFIG_PATH
    PKG_CONFIG_PATH="$(find "${AWS_LC_INSTALL_FOLDER}" -type d -name pkgconfig)"
    export PKG_CONFIG_PATH
    
    local NETTY_LD_LIBRARY_PATH
    NETTY_LD_LIBRARY_PATH="$(pkg-config --variable=libdir libcrypto)"
    
    local NETTY_LDFLAGS
    NETTY_LDFLAGS="$(pkg-config --libs libssl libcrypto)"
    NETTY_LDFLAGS+="${LDFLAGS:-}"
    
    local NETTY_CFLAGS
    NETTY_CFLAGS="$(pkg-config --cflags libssl libcrypto)"
    NETTY_CFLAGS+="${CFLAGS:-}"
    
    env LD_LIBRARY_PATH="${NETTY_LD_LIBRARY_PATH}" LDFLAGS="${NETTY_LDFLAGS}" CFLAGS="${NETTY_CFLAGS}" ./mvnw "$@"
    
    unset PKG_CONFIG_PATH
    popd # "${NETTY_TCNATIVE_SRC}"
}


function clone_and_patch_netty_tcnative() {
    git clone "${NETTY_TCNATIVE_GIT_URL}" "${NETTY_TCNATIVE_SRC}"
    pushd "${NETTY_TCNATIVE_SRC}"
    git fetch origin "${NETTY_TCNATIVE_REFSPEC}"
    git checkout -b aws-lc "${NETTY_TCNATIVE_REFSPEC}"
    if [[ -e "${NETTY_TCNATIVE_PATCH_FOLDER}/${NETTY_TCNATIVE_REFSPEC}.patch" ]]; then
        patch -p1 -i "${NETTY_TCNATIVE_PATCH_FOLDER}/${NETTY_TCNATIVE_REFSPEC}.patch"
    else
        patch -p1 --no-backup-if-mismatch -i "${NETTY_TCNATIVE_PATCH_FOLDER}/latest.patch"
    fi
    popd # "${NETTY_TCNATIVE_SRC}"
}

function wrapper_aws_lc_build() {
    rm -rf "${AWS_LC_INSTALL_FOLDER:?}"/*
    rm -rf "${AWS_LC_BUILD_FOLDER:?}"/*
    aws_lc_build "${SRC_ROOT}" "${AWS_LC_BUILD_FOLDER}" "${AWS_LC_INSTALL_FOLDER}" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo "$@"
}

function verify_static_netty_build() {
    local UNAME_P
    local UNAME_S
    local TARGET_DIR
    local TARGET_JAR
    local INTERROGATE_DIR

    UNAME_P="$(uname -p)"
    UNAME_S="$(uname -s | tr '[:upper:]' '[:lower:]')"
    TARGET_DIR="${NETTY_TCNATIVE_SRC}/${1:?}/target"
    TARGET_JAR=$(find "${TARGET_DIR}" -name "*-${UNAME_S}-${UNAME_P}.jar")
    INTERROGATE_DIR="${SCRATCH_FOLDER}/inspect_jar"

    mkdir -p "${INTERROGATE_DIR}"
    pushd "${INTERROGATE_DIR}"
    unzip "${TARGET_JAR}"
    nm "META-INF/native/libnetty_tcnative_${UNAME_S}_${UNAME_P}.so" | grep awslc_api_version_num
    popd # "${INTERROGATE_DIR}"

    rm -rf "${INTERROGATE_DIR}"
}

# Make script execution idempotent.
mkdir -p "${SCRATCH_FOLDER}"
rm -rf "${SCRATCH_FOLDER:?}"/*
pushd "${SCRATCH_FOLDER}"

clone_and_patch_netty_tcnative

mkdir -p "${AWS_LC_BUILD_FOLDER}" "${AWS_LC_INSTALL_FOLDER}"

# Shared Build
wrapper_aws_lc_build "-DBUILD_SHARED_LIBS=1"

build_netty_tcnative -am -pl openssl-dynamic clean verify

# Shared FIPS Build
wrapper_aws_lc_build "-DBUILD_SHARED_LIBS=1" "-DFIPS=1"

build_netty_tcnative -am -pl openssl-dynamic clean verify

# Static Build
wrapper_aws_lc_build "-DBUILD_SHARED_LIBS=0"

build_netty_tcnative -am -pl openssl-static "-DopensslHome=${AWS_LC_INSTALL_FOLDER}" clean verify
verify_static_netty_build "openssl-static"

# Static FIPS Build
wrapper_aws_lc_build "-DBUILD_SHARED_LIBS=0" "-DFIPS=1"

build_netty_tcnative -am -pl openssl-static "-DopensslHome=${AWS_LC_INSTALL_FOLDER}" clean verify
verify_static_netty_build "openssl-static"

popd # "${SCRATCH_FOLDER}"
rm -rf "${SCRATCH_FOLDER:?}"
