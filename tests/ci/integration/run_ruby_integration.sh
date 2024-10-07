#!/bin/bash -exu
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

set -exuo pipefail

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#    - SCRATCH_FOLDER
#      - RUBY_SRC_FOLDER
#        - ruby_3_1
#      - RUBY_PATCH_FOLDER
#        - ruby_3_1
#      - AWS_LC_BUILD_FOLDER
#      - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SRC_ROOT}/RUBY_BUILD_ROOT"
RUBY_SRC_FOLDER="${SCRATCH_FOLDER}/ruby-src"
RUBY_PATCH_FOLDER="${SRC_ROOT}/tests/ci/integration/ruby_patch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

function ruby_build() {
    local branch=${1}
    pushd ${branch}
    ./autogen.sh
    mkdir -p build && cd build
    ../configure --with-openssl-dir=${AWS_LC_INSTALL_FOLDER} \
                 --with-openssl-lib=${AWS_LC_INSTALL_FOLDER}/lib \
                 --with-openssl-include=${AWS_LC_INSTALL_FOLDER}/include
    make -j ${NUM_CPU_THREADS}
    popd
}

function ruby_patch() {
    local branch=${1}
    local src_dir="${RUBY_SRC_FOLDER}/${branch}"
    local patch_dir="${RUBY_PATCH_FOLDER}/${branch}"
    if [[ ! $(find -L ${patch_dir} -type f -name '*.patch') ]]; then
        echo "No patch for ${branch}!"
        exit 1
    fi
    git clone https://github.com/ruby/ruby.git ${src_dir} \
        --depth 1 \
        --branch ${branch}
    for patchfile in $(find -L ${patch_dir} -type f -name '*.patch'); do
      echo "Apply patch ${patchfile}..."
      cat ${patchfile} | patch -p1 --quiet -d ${src_dir}
    done
}

if [[ "$#" -eq "0" ]]; then
    echo "No ruby branches provided for testing"
    exit 1
fi

mkdir -p ${SCRATCH_FOLDER}
rm -rf ${SCRATCH_FOLDER}/*
cd ${SCRATCH_FOLDER}

mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}

export CFLAGS="-DAWS_LC_INTERNAL_IGNORE_BN_SET_FLAGS=1"
aws_lc_build ${SRC_ROOT} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} -DBUILD_TESTING=OFF -DBUILD_SHARED_LIBS=1

mkdir -p ${RUBY_SRC_FOLDER}
pushd ${RUBY_SRC_FOLDER}

# NOTE: As we add more versions to support, we may want to parallelize here
for branch in "$@"; do
    ruby_patch ${branch}
    ruby_build ${branch}
done

popd
