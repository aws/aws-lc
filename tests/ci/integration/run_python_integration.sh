#!/bin/bash -exu
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

set -exuo pipefail

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#    - SCRATCH_FOLDER
#      - PYTHON_SRC_FOLDER
#        - 3.10
#        ...
#      - PYTHON_PATCH_FOLDER
#        - 3.10
#        ...
#      - AWS_LC_BUILD_FOLDER
#      - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SRC_ROOT}/PYTHON_BUILD_ROOT"
PYTHON_SRC_FOLDER="${SCRATCH_FOLDER}/python-src"
PYTHON_PATCH_FOLDER="${SRC_ROOT}/tests/ci/integration/python_patch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

function python_build() {
    local branch=${1}
    pushd ${branch}
    ./configure \
          --with-openssl=${AWS_LC_INSTALL_FOLDER} \
          --with-builtin-hashlib-hashes=blake2 \
          --with-ssl-default-suites=openssl
    make -j ${NUM_CPU_THREADS}
    popd
}

function python_run_tests() {
    local branch=${1}
    pushd ${branch}
    # We statically link, so need to call into python itself to assert that we're
    # correctly built against AWS-LC
    ./python -c 'import ssl; print(ssl.OPENSSL_VERSION)' | grep AWS-LC
    # see https://github.com/pypa/setuptools/issues/3007
    export SETUPTOOLS_USE_DISTUTILS=stdlib
    # A number of python module tests fail on our public CI images, but they're
    # all unrelated to AWS-LC and the ssl module. So, restrict the module tests
    # we run to those relevant to our CPython integration.
    local TEST_OPTS="\
        test_asyncio \
        test_audit \
        test_ftplib \
        test_hashlib \
        test_httplib \
        test_imaplib \
        test_logging \
        test_poplib \
        test_site \
        test_smtpnet \
        test_ssl \
        test_urllib \
        test_urllib2_localnet \
        test_xmlrpc \
    "
    make -j ${NUM_CPU_THREADS} test TESTOPTS="${TEST_OPTS}"
    popd
}

# The per-branch patch files do a few things:
#
#   - Modify various unit tests to account for error string differences between
#     OpenSSL and AWS-LC.
#   - In |test_bio|handshake|, check whether protocol is TLSv1.3 before testing
#     tls-unique channel binding behavior, as channel bindings are not defined
#     on that protocol
#   - Skip FFDH(E)-reliant tests, as AWS-LC doesn't support FFDH(E)
#   - Skip post handshake authentication tests, as AWS-LC doesn't support that
#   - Add test specifically for AWS-LC to codify the ssl module's behavior when
#     caller attempts to use post-handshake authentication
#   - For 3.10, modify Modules/Setup to point to the AWS-LC installation dir
#   - Modify the hashlib module's backing C code to only register BLAKE
#     functions if the expected NID is available in linked libcrypto
#   - Modify the ssl module's backing C code to separate notions of supporting
#     TLSv1.3 from supporting post-handshake authentication as some libraries
#     (namely AWS-LC) support TLSv1.3, but not the post-handshake
#     authentication portion of that protocol.
#   - Modify the ssl module's backing C code to account for AWS-LC's divergent
#     function signature and return value for |sk_SSL_CIPHER_find|
#
# TODO: Remove these patches when we make an upstream contribution.
function python_patch() {
    local branch=${1}
    local src_dir="${PYTHON_SRC_FOLDER}/${branch}"
    local patch_dir="${PYTHON_PATCH_FOLDER}/${branch}"
    if [[ ! $(find -L ${patch_dir} -type f -name '*.patch') ]]; then
        echo "No patch for ${branch}!"
        exit 1
    fi
    git clone https://github.com/python/cpython.git ${src_dir} \
        --depth 1 \
        --branch ${branch}
    for patchfile in $(find -L ${patch_dir} -type f -name '*.patch'); do
      echo "Apply patch ${patchfile}..."
      cat ${patchfile} \
          | sed -e "s|AWS_LC_INSTALL_PLACEHOLDER|${AWS_LC_INSTALL_FOLDER}|g" \
          | patch -p1 --quiet -d ${src_dir}
    done
}

if [[ "$#" -eq "0" ]]; then
    echo "No python branches provided for testing"
    exit 1
fi

mkdir -p ${SCRATCH_FOLDER}
rm -rf ${SCRATCH_FOLDER}/*
cd ${SCRATCH_FOLDER}

mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}

aws_lc_build ${SRC_ROOT} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} \
    -DBUILD_TESTING=OFF \
    -DBUILD_SHARED_LIBS=0

# Some systems install under "lib64" instead of "lib"
ln -s ${AWS_LC_INSTALL_FOLDER}/lib64 ${AWS_LC_INSTALL_FOLDER}/lib

mkdir -p ${PYTHON_SRC_FOLDER}
pushd ${PYTHON_SRC_FOLDER}

# Some environments disable IPv6 by default
which sysctl && ( sysctl -w net.ipv6.conf.all.disable_ipv6=0 || /bin/true )
echo 0 >/proc/sys/net/ipv6/conf/all/disable_ipv6 || /bin/true

# NOTE: As we add more versions to support, we may want to parallelize here
for branch in "$@"; do
    python_patch ${branch}
    python_build ${branch}
    python_run_tests ${branch}
done

popd
