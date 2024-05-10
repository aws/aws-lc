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

function python_run_3rd_party_tests() {
    local branch=${1}
    pushd ${branch}
    local venv='.venv'
    echo creating virtualenv to isolate dependencies...
    ./python -m virtualenv ${venv} || ./python -m venv ${venv}
    source ${venv}/bin/activate
    echo installing other OpenSSL-dependent modules...
    ./python -m ensurepip
    ./python -m pip install 'boto3[crt]' 'cryptography'
    # this appears to be needed by more recent python versions
    ./python -m pip install setuptools
    echo running minor integration test of those dependencies...
    ./python -c 'import ssl; print(ssl.OPENSSL_VERSION)' | grep AWS-LC
    ./python <<EOF
import boto3
import botocore
import awscrt

# make an API call to exercise SigV4 request signing in the CRT. the creds are
# nonsense, but that's OK because we sign and make a request over the network
# to determine that.
ak, sk, st = 'big', 'bad', 'wolf'
client = boto3.client(
    's3',
    aws_access_key_id=ak,
    aws_secret_access_key=sk,
    aws_session_token=st
)
try:
    client.list_buckets()
    assert False, "ListBuckets succeeded when it shouldn't have"
except botocore.exceptions.ClientError as e:
    # expect it to fail due to nonsense creds
    assert 'InvalidAccessKeyId' in e.response['Error']['Code']

import sys
assert sys.version_info.major == 3, 'Only python 3 supported'
if sys.version_info.minor == 14:
    print("Fernet import currently broken on mainline py release canddiate")
    print("Returning early for now, need to check in on this post-release")
    sys.exit()

import cryptography
import cryptography.hazmat.backends.openssl.backend
from cryptography.fernet import Fernet

# exercise simple round trip, then assert that PyCA has linked OpenSSL
k = Fernet.generate_key()
f = Fernet(k)
pt = b"hello world"
assert pt == f.decrypt(f.encrypt(pt))

version = cryptography.hazmat.backends.openssl.backend.openssl_version_text()
assert 'OpenSSL' in version, f"PyCA didn't link OpenSSL: {version}"

EOF
    deactivate # function defined by .venv/bin/activate
    rm -rf ${venv}
    popd
}

# The per-branch patch files do a few things for older versions (e.g. 3.10)
# that aren't taking non-security-critical patches (patches for newer versions
# likely only apply a subset of below):
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
    python_run_3rd_party_tests ${branch}
done

popd
