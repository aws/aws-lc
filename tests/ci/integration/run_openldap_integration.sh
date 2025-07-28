#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

set -exuo pipefail

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#    - SCRATCH_FOLDER
#      - OPENLDAP_SRC_FOLDER
#        - main
#        ...
#      - OPENLDAP_PATCH_FOLDER
#        - main
#        ...
#      - AWS_LC_BUILD_FOLDER
#      - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SRC_ROOT}/OPENLDAP_BUILD_ROOT"
OPENLDAP_SRC_FOLDER="${SCRATCH_FOLDER}/openldap-src"
OPENLDAP_PATCH_FOLDER="${SRC_ROOT}/tests/ci/integration/openldap_patch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

function openldap_build() {
    local branch=${1}
    pushd ${branch}
    # Modify CFLAGS and LDFLAGS so compiler and linker can find AWS-LC's artifacts
    export STRICT_C_COMPILER="gcc"
    export CPPFLAGS="-I$AWS_LC_INSTALL_FOLDER/include"
    export LDFLAGS="$AWS_LC_INSTALL_FOLDER/lib/libcrypto.a $AWS_LC_INSTALL_FOLDER/lib/libssl.a"
    export LDFLAGS="$LDFLAGS -L$AWS_LC_INSTALL_FOLDER/lib"
    ./configure \
        --prefix=$AWS_LC_INSTALL_FOLDER \
        --enable-debug \
        --enable-static \
        --enable-slapd \
        --disable-syslog \
        --with-tls \
        --without-systemd
    make -j ${NUM_CPU_THREADS}
    # assert that neither libcrypto nor libssl are linked dynamically
    ldd ./servers/slapd/slapd | grep libcrypto || true | wc -l | xargs test 0 -eq
    ldd ./servers/slapd/slapd | grep libssl || true | wc -l | xargs test 0 -eq
    # assert that patched slapd binary is compiled against and linked to AWS-LC
    # for some reason, -V exits non-zero so use "true" to guard against pipefail
    ( ./servers/slapd/slapd -V || true ) |& grep AWS-LC | wc -l | xargs test 2 -eq
    popd
}

function openldap_run_tests() {
    local branch=${1}
    pushd ${branch}
    make -j ${NUM_CPU_THREADS} test
    popd
}

function openldap_patch() {
    local branch=${1}
    local src_dir="${OPENLDAP_SRC_FOLDER}/${branch}"
    local patch_dir="${OPENLDAP_PATCH_FOLDER}/${branch}"
    if [[ ! $(find -L ${patch_dir} -type f -name '*.patch') ]]; then
        echo "No patch for ${branch}!"
        exit 1
    fi
    git clone https://github.com/openldap/openldap.git ${src_dir} \
        --depth 1 \
        --branch ${branch}
    for patchfile in $(find -L ${patch_dir} -type f -name '*.patch'); do
      echo "Apply patch ${patchfile}..."
      cat ${patchfile} \
          | patch -p1 --quiet -d ${src_dir}
    done
}

if [[ "$#" -eq "0" ]]; then
    echo "No openldap branches provided for testing"
    exit 1
fi

mkdir -p ${SCRATCH_FOLDER}
rm -rf ${SCRATCH_FOLDER}/*
cd ${SCRATCH_FOLDER}

mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}

aws_lc_build ${SRC_ROOT} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} \
    -DBUILD_TESTING=OFF \
    -DBUILD_SHARED_LIBS=0

mkdir -p ${OPENLDAP_SRC_FOLDER}
pushd ${OPENLDAP_SRC_FOLDER}

# NOTE: As we add more versions to support, we may want to parallelize here
for branch in "$@"; do
    openldap_patch ${branch}
    openldap_build ${branch}
    openldap_run_tests ${branch}
done

popd
