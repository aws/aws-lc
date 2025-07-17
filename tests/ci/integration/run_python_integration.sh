#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exu

source tests/ci/common_posix_setup.sh

set -exuo pipefail

# Set up environment.

# Default env parameters to "off"
FIPS=${FIPS:-"0"}
AWS_CRT_BUILD_USE_SYSTEM_LIBCRYPTO=${AWS_CRT_BUILD_USE_SYSTEM_LIBCRYPTO:-"0"}

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
CRT_SRC_FOLDER="${SCRATCH_FOLDER}/aws-crt-python"
PYTHON_SRC_FOLDER="${SCRATCH_FOLDER}/python-src"
PYTHON_PATCH_FOLDER="${SRC_ROOT}/tests/ci/integration/python_patch"
PYTHON_INTEG_TEST_FOLDER="${SRC_ROOT}/tests/ci/integration/python_tests"
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
    local python='./python'
    pushd ${branch}
    # We statically link, so need to call into python itself to assert that we're
    # correctly built against AWS-LC
    if [[ ${FIPS} == "1" ]]; then
        local expected_version_str='AWS-LC FIPS'
    else
        local expected_version_str='AWS-LC'
    fi
    ${python} -c 'import ssl; print(ssl.OPENSSL_VERSION)' | grep "${expected_version_str}"
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
        test_hmac \
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

function fetch_crt_python() {
    rm -rf ${CRT_SRC_FOLDER}
    mkdir -p ${CRT_SRC_FOLDER}
    pushd ${CRT_SRC_FOLDER}
    git clone https://github.com/awslabs/aws-crt-python.git .
    git submodule update --init
    popd
}

function install_crt_python() {
    # for some reason on python 3.12+, AWS CRT's setup.py can't find
    # setuptools/distutils installed to our virtualenv. for those versions,
    # return early and let the CRT use precompiled PyPI wheel backed by AWS-LC.
    python -c 'import ssl; print(ssl.OPENSSL_VERSION)' | grep "AWS-LC"
    if ! python -c 'import sys; assert sys.version_info.minor < 12, f"{sys.version_info}"'; then
        python -m pip install awscrt
        return
    fi
    python -m ensurepip
    # setupttols not installed by default on more recent python versions
    # see https://github.com/python/cpython/issues/95299
    python -m pip install setuptools wheel
    python -m pip list
    python -m pip install -e ${CRT_SRC_FOLDER}
    # below was adapted from aws-crt-python's CI
    # https://github.com/awslabs/aws-crt-python/blob/d76c3dacc94c1aa7dfc7346a77be78dc990b5171/.github/workflows/ci.yml#L159
    local awscrt_path=$(python -c "import _awscrt; print(_awscrt.__file__)")
    echo "AWSCRT_PATH: $awscrt_path"
    local linked_against=$(ldd $awscrt_path)
    echo "LINKED AGAINST: $linked_against"
    local uses_libcrypto_so=$(echo "$linked_against" | grep 'libcrypto*.so' | head -1)
    echo "USES LIBCRYTPO: $uses_libcrypto_so"
    # by default, the python CRT bindings bundle their own libcrypto wheel
    # built from AWS-LC. AWS_CRT_BUILD_USE_SYSTEM_LIBCRYPTO can be specified
    # in build environment to tell CRT to link against system libcrypto
    # (usually OpenSSL) instead.
    if [[ ${AWS_CRT_BUILD_USE_SYSTEM_LIBCRYPTO} == "1" ]]; then
        test -n "$uses_libcrypto_so"
    else
        test -z "$uses_libcrypto_so"
    fi
}

function python_run_3rd_party_tests() {
    local branch=${1}
    pushd ${branch}
    local venv=$(realpath '.venv')
    echo creating virtualenv to isolate dependencies...
    ./python -m virtualenv ${venv} || ./python -m venv ${venv}
    source ${venv}/bin/activate
    # assert that the virtual env's python is the binary we built w/ AWS-LC
    which python | grep ${venv}
    python -c 'import ssl; print(ssl.OPENSSL_VERSION)' | grep "AWS-LC"
    echo installing other OpenSSL-dependent modules...
    install_crt_python
    python -m pip install 'boto3[crt]'
    # cffi install is busted on newer release candidates, so allow install
    # failure for cryptography and pyopenssl on >= 3.14 for now.
    python -m pip install 'cryptography' \
        || python -c 'import sys; assert sys.version_info.minor >= 3.14'
    python -m pip install 'pyopenssl' \
        || python -c 'import sys; assert sys.version_info.minor >= 3.14'
    echo running minor integration test of those dependencies...
    for test in ${PYTHON_INTEG_TEST_FOLDER}/*.py; do
        python ${test}
    done
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

# Link AWS-LC dynamically against CPython's main, statically against
# versioned releases.
if [[ "${1}" == "main" ]]; then
    BUILD_SHARED_LIBS="ON"
    export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"
else
    BUILD_SHARED_LIBS="OFF"
fi

aws_lc_build ${SRC_ROOT} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} \
    -DBUILD_TESTING=OFF \
    -DBUILD_SHARED_LIBS=${BUILD_SHARED_LIBS} \
    -DFIPS=${FIPS}

fetch_crt_python

mkdir -p ${PYTHON_SRC_FOLDER}
pushd ${PYTHON_SRC_FOLDER}

# Some environments disable IPv6 by default
which sysctl && ( sysctl -w net.ipv6.conf.all.disable_ipv6=0 || /bin/true )
echo 0 >/proc/sys/net/ipv6/conf/all/disable_ipv6 || /bin/true

export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"

# NOTE: As we add more versions to support, we may want to parallelize here
for branch in "$@"; do
    python_patch ${branch}
    python_build ${branch}
    python_run_tests ${branch}
    python_run_3rd_party_tests ${branch}
done

popd
