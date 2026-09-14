#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  |
#  - SRC_ROOT(aws-lc)
#  |
#  - SCRATCH_FOLDER
#    |
#    - openssh-portable
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER
#    - OPENSSH_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
SCRATCH_FOLDER="${SYS_ROOT}/SCRATCH_AWSLC_OPENSSH_INTERN_TEST"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"
OPENSSH_WORKSPACE_FOLDER="${SCRATCH_FOLDER}/openssh-portable"
OPENSSH_INSTALL_FOLDER="${SCRATCH_FOLDER}/openssh-install"

OPENSSH_REF="${1:-master}"

NINJA_COMMAND=ninja
if ! ${NINJA_COMMAND} --version; then
  NINJA_COMMAND=ninja-build
fi

# Make script execution idempotent.
rm -rf "${SCRATCH_FOLDER:?}"
mkdir -p "${SCRATCH_FOLDER}"
pushd "${SCRATCH_FOLDER}"

# Test helper functions.

function install_aws_lc() {
  AWS_LC_LIB_FOLDER=$(readlink -f "${AWS_LC_INSTALL_FOLDER}"/lib*)
  # This installs AWS-LC as the "libcrypto" for the system
  echo "${AWS_LC_LIB_FOLDER}" > /etc/ld.so.conf.d/aws-lc.conf
  rm -f /etc/ld.so.cache
  ldconfig
}

function openssh_build() {
  pushd "${OPENSSH_WORKSPACE_FOLDER}"
  if [ "${OPENSSH_REF}" == "master" ]; then
    patch -p1 --quiet -i "${SCRIPT_DIR}/openssh_patch/aws-lc-openssh.patch"
  fi
  autoreconf

  if [ "${OPENSSH_REF}" == "master" ] || [[ "${OPENSSH_REF}" == V_10_* ]]; then
    ./configure --with-ssl-dir="${AWS_LC_INSTALL_FOLDER}" --prefix="${OPENSSH_INSTALL_FOLDER}"
  else
    # The RSA_meth_XXX functions are not implemented by AWS-LC, and the implementation provided by OpenSSH also doesn't compile for us.
    # Fortunately, these functions are only needed for pkcs11 support, which is disabled for our build.
    # See: https://github.com/openssh/openssh-portable/pull/385
    export CFLAGS="-DHAVE_RSA_METH_DUP=1 -DHAVE_RSA_METH_SET1_NAME=1 -DHAVE_RSA_METH_GET_FINISH=1 "
    ./configure --with-ssl-dir="${AWS_LC_INSTALL_FOLDER}" --prefix="${OPENSSH_INSTALL_FOLDER}" --disable-pkcs11
  fi

  make -j "$NUM_CPU_THREADS"
  make install
  ls -R "${OPENSSH_INSTALL_FOLDER}"
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

# Regenerate the ML-DSA composite unit-test keys under the current keytype name.
function regenerate_mldsa_testdata() {
  local keygen="${OPENSSH_INSTALL_FOLDER}/bin/ssh-keygen"
  local pw="mekmitasdigoat"

  pushd "${OPENSSH_WORKSPACE_FOLDER}/regress/unittests/sshkey/testdata"
  rm -f mldsa44_ed25519_1 mldsa44_ed25519_1.pub mldsa44_ed25519_1_pw \
        mldsa44_ed25519_2 mldsa44_ed25519_2.pub mldsa44_ed25519_1-cert.pub \
        mldsa44_ed25519_1.fp mldsa44_ed25519_2.fp mldsa44_ed25519_1-cert.fp \
        mldsa44_ed25519_1.fp.bb mldsa44_ed25519_2.fp.bb
  "${keygen}" -t ssh-mldsa44-ed25519 -C "MLDSA44-ED25519 test key #1" -N "" -f mldsa44_ed25519_1
  "${keygen}" -t ssh-mldsa44-ed25519 -C "MLDSA44-ED25519 test key #2" -N "" -f mldsa44_ed25519_2
  cp mldsa44_ed25519_1 mldsa44_ed25519_1_pw
  "${keygen}" -pf mldsa44_ed25519_1_pw -N "${pw}"
  "${keygen}" -s rsa_2 -I hugo -n user1,user2 \
    -Oforce-command=/bin/ls -Ono-port-forwarding -Osource-address=10.0.0.0/8 \
    -V 19990101:20110101 -z 4 mldsa44_ed25519_1.pub
  "${keygen}" -s ed25519_1 -I julius -n host1,host2 -h \
    -V 19990101:20110101 -z 8 mldsa44_ed25519_1.pub
  "${keygen}" -lf mldsa44_ed25519_1 | awk '{print $2}' > mldsa44_ed25519_1.fp
  "${keygen}" -lf mldsa44_ed25519_2 | awk '{print $2}' > mldsa44_ed25519_2.fp
  "${keygen}" -lf mldsa44_ed25519_1-cert.pub | awk '{print $2}' > mldsa44_ed25519_1-cert.fp
  "${keygen}" -Bf mldsa44_ed25519_1 | awk '{print $2}' > mldsa44_ed25519_1.fp.bb
  "${keygen}" -Bf mldsa44_ed25519_2 | awk '{print $2}' > mldsa44_ed25519_2.fp.bb
  popd

  pushd "${OPENSSH_WORKSPACE_FOLDER}/regress/unittests/sshsig/testdata"
  rm -f mldsa44-ed25519 mldsa44-ed25519.pub mldsa44-ed25519.sig
  "${keygen}" -t ssh-mldsa44-ed25519 -C "MLDSA44-ED25519 test key" -N "" -f mldsa44-ed25519
  "${keygen}" -Y sign -f mldsa44-ed25519 -n unittest - < signed-data > mldsa44-ed25519.sig
  popd
}

mkdir -p "${AWS_LC_BUILD_FOLDER}" "${AWS_LC_INSTALL_FOLDER}" "${OPENSSH_INSTALL_FOLDER}"

# Get OpenSSH at the requested ref.
git clone --depth 1 --branch "${OPENSSH_REF}" https://github.com/openssh/openssh-portable.git "${OPENSSH_WORKSPACE_FOLDER}"
record_repo_commit "${OPENSSH_WORKSPACE_FOLDER}"
ls

# Build AWS-LC as a shared library
aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=1
install_aws_lc

openssh_build

if [ "${OPENSSH_REF}" == "master" ]; then
  regenerate_mldsa_testdata
fi

CODEBUILD_SKIPPED_TESTS="agent-subprocess forwarding multiplex channel-timeout forward-control agent-restrict connection-timeout"
if [ "${OPENSSH_REF}" == "V_8_9" ]; then
    # In v8.9, the "percent" test requires the 'openssl' cli command
    openssh_run_tests "percent ${CODEBUILD_SKIPPED_TESTS}"
else
    openssh_run_tests "${CODEBUILD_SKIPPED_TESTS}"
fi

popd
