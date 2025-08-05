#!/bin/bash -exu
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

set -exuo pipefail

# Set up environment.

# Default env parameters to "off"
FIPS=${FIPS:-"0"}

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
RUBY_BACKPORT_FOLDER="${SRC_ROOT}/tests/ci/integration/ruby_patch/ruby_release_backport"
RUBY_COMMON_FOLDER="${SRC_ROOT}/tests/ci/integration/ruby_patch/ruby_patch_common"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

function ruby_build() {
    local branch=${1}
    pushd "${RUBY_SRC_FOLDER}/${branch}"
    ./autogen.sh
    mkdir -p install
    ./configure --disable-install-doc \
                 --prefix="$PWD/install" \
                 --with-openssl-dir=${AWS_LC_INSTALL_FOLDER}
    make V=1 -j ${NUM_CPU_THREADS}
    make install
    # Check that AWS-LC was used.
    ./install/bin/ruby -e 'require "openssl"; puts OpenSSL::OPENSSL_VERSION' | grep -q "AWS-LC" && echo "AWS-LC found!" || exit 1
    ./miniruby ./tool/runruby.rb -e 'require "openssl"; puts OpenSSL::OPENSSL_VERSION' | grep -q "AWS-LC" && echo "AWS-LC found!" || exit 1

    ${AWS_LC_BUILD_FOLDER}/check-linkage.sh "$(find "$PWD/install" -name "openssl.so")" crypto || exit 1
    ${AWS_LC_BUILD_FOLDER}/check-linkage.sh "$(find "$PWD/install" -name "openssl.so")" ssl || exit 1

    make test-all TESTS="test/openssl/*.rb"
    make test-all TESTS="test/rubygems/test*.rb"

    # drb was moved from a default gem to a bundled gem in later versions of Ruby.
    if [[ "${branch}" != "master" && "${branch}" != "ruby_3_4" ]]; then
        make test-all TESTS="test/drb/*ssl*.rb"
    fi

    popd
}

function ruby_patch() {
    local branch=${1}
    local src_dir="${RUBY_SRC_FOLDER}/${branch}"
    local patch_dirs=("${RUBY_PATCH_FOLDER}/${branch}" "${RUBY_COMMON_FOLDER}")
    if [[ "${branch}" != "master" && ! $(find -L ${patch_dirs[0]} -type f -name '*.patch') ]]; then
        echo "No patch for ${branch}!"
        exit 1
    fi
    git clone https://github.com/ruby/ruby.git ${src_dir} \
        --depth 1 \
        --branch ${branch}

    # Add directory of backport patches if branch is a version later than Ruby 3.4.
    if [[ "${branch}" != "master" && "${branch}" != "ruby_3_4" ]]; then
        patch_dirs+=("${RUBY_BACKPORT_FOLDER}")
    fi

    for patch_dir in "${patch_dirs[@]}"; do
        for patchfile in $(find -L ${patch_dir} -type f -name '*.patch'); do
          echo "Apply patch ${patchfile}..."
          patch --strip 1 -F 3 --quiet -d ${src_dir} --input ${patchfile}
        done
    done
}

if [[ "$#" -eq "0" ]]; then
    echo "No ruby branches provided for testing"
    exit 1
fi

if [[ "${FIPS}" -eq "1" ]]; then
    export TEST_RUBY_OPENSSL_FIPS_ENABLED="true"
fi

mkdir -p ${SCRATCH_FOLDER}
rm -rf ${SCRATCH_FOLDER}/*
cd ${SCRATCH_FOLDER}

mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
aws_lc_build ${SRC_ROOT} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} -DBUILD_TESTING=OFF -DFIPS=${FIPS} -DBUILD_SHARED_LIBS=1

mkdir -p ${RUBY_SRC_FOLDER}

# NOTE: As we add more versions to support, we may want to parallelize here
for branch in "$@"; do
    ruby_patch ${branch}
    ruby_build ${branch}
done

