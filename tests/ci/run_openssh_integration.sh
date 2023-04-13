#!/bin/bash -exu
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

# Set up environment.

# ROOT
#  |
#  - AWS_LC_DIR
#    |
#    - aws-lc
#  |
#  - SCRATCH_FOLDER
#    |
#    - openssh-portable
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER
#    - OPENSSH_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
AWS_LC_DIR=$(pwd)
pushd ..
ROOT=$(pwd)
popd

SCRATCH_FOLDER="${ROOT}/SCRATCH_AWSLC_OPENSSH_INTERN_TEST"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"
OPENSSH_WORKSPACE_FOLDER="${SCRATCH_FOLDER}/openssh-portable"
OPENSSH_INSTALL_FOLDER="${SCRATCH_FOLDER}/openssh-install"

NINJA_COMMAND=ninja
if ! ${NINJA_COMMAND} --version; then
  NINJA_COMMAND=ninja-build
fi

# Make script execution idempotent.
rm -rf "${SCRATCH_FOLDER}"
mkdir -p "${SCRATCH_FOLDER}"
pushd "${SCRATCH_FOLDER}"

# Test helper functions.

function aws_lc_build() {
  export GOPROXY=direct
  ${CMAKE_COMMAND} "${AWS_LC_DIR}" -GNinja "-B${AWS_LC_BUILD_FOLDER}" "-DCMAKE_INSTALL_PREFIX=${AWS_LC_INSTALL_FOLDER}" "$@"
  ${NINJA_COMMAND} -C "${AWS_LC_BUILD_FOLDER}" install
  ls -R "${AWS_LC_INSTALL_FOLDER}"
  rm -rf "${AWS_LC_BUILD_FOLDER:?}"/*
}

function install_aws_lc() {
  AWS_LC_LIB_FOLDER=$(readlink -f "${AWS_LC_INSTALL_FOLDER}"/lib*)
  echo "${AWS_LC_LIB_FOLDER}" > /etc/ld.so.conf.d/aws-lc.conf
  rm -f /etc/ld.so.cache
  ldconfig
}

function openssh_build() {
  pushd "${OPENSSH_WORKSPACE_FOLDER}"
  autoreconf
  export CFLAGS="-DAWS_LC_INTERNAL_IGNORE_BN_SET_FLAGS=1 -DHAVE_RSA_METH_FREE=1 -DHAVE_RSA_METH_DUP=1 -DHAVE_RSA_METH_SET1_NAME=1 -DHAVE_RSA_METH_SET_PRIV_ENC=1 -DHAVE_RSA_METH_SET_PRIV_DEC=1"
  ./configure --with-ssl-dir="${AWS_LC_INSTALL_FOLDER}" --prefix="${OPENSSH_INSTALL_FOLDER}" --disable-pkcs11
  make install
  ls -R "${OPENSSH_INSTALL_FOLDER}"
  popd
}

function checkout_openssh_branch() {
  pushd "${OPENSSH_WORKSPACE_FOLDER}"
  make clean
  git clean -f -d
  git checkout --track origin/"$1"
  popd
}

function openssh_run_tests() {
  pushd "${OPENSSH_WORKSPACE_FOLDER}"
  if ! id -u sshd; then
    useradd sshd
  fi
  export TEST_SSH_UNSAFE_PERMISSIONS=1
  export SKIP_LTESTS="$@"
  make tests
  popd
}

mkdir -p "${AWS_LC_BUILD_FOLDER}" "${AWS_LC_INSTALL_FOLDER}" "${OPENSSH_INSTALL_FOLDER}"

# Get latest OpenSSH version.
git clone https://github.com/openssh/openssh-portable.git
ls

# Buld AWS-LC as a shared library
aws_lc_build -DBUILD_SHARED_LIBS=1
install_aws_lc

# Using default branch. Build openssh and run tests.
openssh_build
openssh_run_tests "agent-subprocess forwarding"

# Using branch V_8_9
checkout_openssh_branch V_8_9
openssh_build
# In v8.9, the "percent" test requires the 'openssl' cli command
openssh_run_tests "percent agent-subprocess forwarding"

popd
