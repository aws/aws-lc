#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

AWS_LC_DIR=${PWD##*/}
cd ../
ROOT=$(pwd)
mkdir -p aws-lc-build aws-lc-install s2n-tls-build
git clone https://github.com/aws/s2n-tls.git
ls

# s2n-tls's FindLibCrypto.cmake expects to find both the archive (.a) and shared object (.so) libcrypto
cmake ${AWS_LC_DIR} -GNinja "-B${ROOT}/aws-lc-build" "-DCMAKE_INSTALL_PREFIX=${ROOT}/aws-lc-install"
ninja -C aws-lc-build install
rm -rf aws-lc-build/*
cmake ${AWS_LC_DIR} -GNinja "-B${ROOT}/aws-lc-build" "-DCMAKE_INSTALL_PREFIX=${ROOT}/aws-lc-install" -DBUILD_SHARED_LIBS=1
ninja -C aws-lc-build install

cmake s2n-tls -GNinja "-B${ROOT}/s2n-tls-build" "-DCMAKE_PREFIX_PATH=${ROOT}/aws-lc-install"
ninja -C s2n-tls-build

cd "${ROOT}/s2n-tls-build"
ctest -j 8 --output-on-failure

# Test aws-lc's PQTLS 1.3 implementation against s2n-tls
# Test successful handshakes between s_client and s2nd
cd ../
./s2n-tls-build/bin/s2nd --ciphers PQ-TLS-1-0-2021-05-26 -i -n localhost 8888 &
S2ND_PID=$!
# The sleeps are necessary to give the OS time to assign/reclaim sockets
sleep 1
./aws-lc-build/tool/bssl s_client -connect localhost:8888 -curves x25519_kyber512 -min-version tls1.3
./aws-lc-build/tool/bssl s_client -connect localhost:8888 -curves prime256v1_kyber512 -min-version tls1.3
kill ${S2ND_PID}
sleep 1

# Test successful handshakes between s_server and s2nc
./aws-lc-build/tool/bssl s_server -curves x25519_kyber512 -accept 8888 -min-version tls1.3 &
sleep 1
./s2n-tls-build/bin/s2nc --ciphers PQ-TLS-1-0-2021-05-26 -i localhost 8888
sleep 1
./aws-lc-build/tool/bssl s_server -curves prime256v1_kyber512 -accept 8888 -min-version tls1.3 &
sleep 1
./s2n-tls-build/bin/s2nc --ciphers PQ-TLS-1-0-2021-05-26 -i localhost 8888

# Test unsuccessful attempted handshakes when s2n and bssl should not have any curves in common for TLS 1.3.
# This s2n security policy contains kyber round 2, but not the round 3 version that is in aws-lc.
./aws-lc-build/tool/bssl s_server -curves x25519_kyber512:prime256v1_kyber512 -accept 8888 -min-version tls1.3 &
sleep 1
./s2n-tls-build/bin/s2nc --ciphers PQ-TLS-1-0-2020-12 -i localhost 8888 &&\
    echo "Negotiated a successful handshake even though s2n-tls and bssl should not have had any common groups." && exit 1
sleep 1
./s2n-tls-build/bin/s2nd --ciphers PQ-TLS-1-0-2020-12 -i -n localhost 8888 &
sleep 1
./aws-lc-build/tool/bssl s_client -connect localhost:8888 -curves x25519_kyber512:prime256v1_kyber512 -min-version tls1.3 &&\
    echo "Negotiated a successful handshake even though s2n-tls and bssl should not have had any common groups." && exit 1

exit 0
