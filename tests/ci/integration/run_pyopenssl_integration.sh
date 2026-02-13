#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

set -exuo pipefail

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#  - SCRATCH_FOLDER
#    - pyopenssl-src
#      - <branch>
#      ...
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SYS_ROOT}/PYOPENSSL_BUILD_ROOT"
PYOPENSSL_SRC_FOLDER="${SCRATCH_FOLDER}/pyopenssl-src"
PYOPENSSL_PATCH_FOLDER="${SRC_ROOT}/tests/ci/integration/pyopenssl_patch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

function pyopenssl_clone() {
    local branch=${1}
    local src_dir="${PYOPENSSL_SRC_FOLDER}/${branch}"
    local patch_dir="${PYOPENSSL_PATCH_FOLDER}/${branch}"
    git clone https://github.com/pyca/pyopenssl.git ${src_dir} \
        --depth 1 \
        --branch ${branch}
    for patchfile in $(find -L ${patch_dir} -type f -name '*.patch'); do
        echo "Applying patch ${patchfile}..."
        patch -p1 --quiet -d ${src_dir} -i "${patchfile}"
    done
}

function pyopenssl_run_tests() {
    local branch=${1}
    local src_dir="${PYOPENSSL_SRC_FOLDER}/${branch}"
    pushd ${src_dir}

    # Create a fresh virtualenv for this branch.
    local venv="${src_dir}/.venv"
    python3 -m venv ${venv}
    source ${venv}/bin/activate

    # Upgrade pip and install build dependencies.
    python -m pip install --upgrade pip setuptools wheel

    # Install the Rust bindgen-cli, needed by cryptography when building
    # against AWS-LC. cargo should already be available in the CI environment.
    cargo install bindgen-cli

    # Pin cryptography version due to cffi change in v46
    # https://cryptography.io/en/latest/changelog/#v46-0-0
    python -m pip install 'cryptography<46'

    # Install PyOpenSSL from the patched source along with test dependencies.
    python -m pip install -e '.[test]'

    # Verify that PyOpenSSL is linked against AWS-LC.
    python -c "
from OpenSSL.SSL import SSLeay_version, OPENSSL_VERSION
version = SSLeay_version(OPENSSL_VERSION)
print('PyOpenSSL linked against:', version)
assert b'AWS-LC' in version, f'Expected AWS-LC, got: {version}'
"

    # Run PyOpenSSL's test suite.
    python -m pytest tests/ -v

    deactivate
    popd
}

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}

# Build and install AWS-LC as a shared library so that the cryptography
# Python package (which pyopenssl depends on) can link against it.
aws_lc_build ${SRC_ROOT} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} \
    -DBUILD_TESTING=OFF \
    -DBUILD_TOOL=OFF \
    -DBUILD_SHARED_LIBS=1 \
    -DCMAKE_BUILD_TYPE=RelWithDebInfo

export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"

# Set OPENSSL_DIR so the cryptography package builds against AWS-LC.
export OPENSSL_DIR="${AWS_LC_INSTALL_FOLDER}"

mkdir -p ${PYOPENSSL_SRC_FOLDER}

# Each subdirectory under PYOPENSSL_PATCH_FOLDER corresponds to a PyOpenSSL
# branch or tag to test against.
for branch_dir in ${PYOPENSSL_PATCH_FOLDER}/*/; do
    branch=$(basename ${branch_dir})
    pyopenssl_clone ${branch}
    pyopenssl_run_tests ${branch}
done
