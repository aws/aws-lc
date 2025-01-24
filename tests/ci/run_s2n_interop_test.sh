#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
set -ex

source tests/ci/common_posix_setup.sh

scratch_folder=${SYS_ROOT}/"s2n-scratch"
s2n_url='https://github.com/aws/s2n-tls.git'
s2n_branch='main'
lc_url='https://github.com/aws/aws-lc.git'
lc_branch='main'

mkdir -p "${scratch_folder}"
rm -rf "${scratch_folder:?}"/*

# clone s2n-tls
git clone --depth 1 --branch "${s2n_branch}" "${s2n_url}" "${scratch_folder}/s2n-tls"

# clone aws-lc
git clone --depth 1 --branch "${lc_branch}" "${lc_url}" "${scratch_folder}/s2n-tls/aws-lc"

# build aws-lc
echo "building aws-lc"
cd "${scratch_folder}/s2n-tls/aws-lc"
cmake -GNinja -B build
ninja -C build
cmake --install build --prefix install

# build s2n-tls with aws-lc
echo "building s2n_tls"
cd "${scratch_folder}/s2n-tls"
cmake . -Bbuild-with-lc \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_PREFIX_PATH=aws-lc/install
cmake --build build-with-lc

# handshake test 1 - aws-lc bssl server with s2n-tls s2nc client for X25519MLKEM768:X25519
cd "${scratch_folder}/s2n-tls"
./aws-lc/build/tool/bssl s_server -curves X25519MLKEM768:X25519 -accept 45000 -debug &
S_PID=$!
sleep 2
./build-with-lc/bin/s2nc -c default_pq -i localhost 45000 > s2nc_out
kill $S_PID || true
grep "libcrypto" s2nc_out | grep "AWS-LC"
grep "CONNECTED" s2nc_out

# handshake test 2 -  s2n-tls s2nd server with aws-lc bssl client for X25519MLKEM768:X25519
cd "${scratch_folder}/s2n-tls"
./build-with-lc/bin/s2nd -c default_pq -i localhost 45000 > s2nd_out &
S_PID=$!
sleep 2
./aws-lc/build/tool/bssl s_client -curves X25519MLKEM768:X25519 -connect localhost:45000 -debug &
C_PID=$!
sleep 2
kill $S_PID || true
kill $C_PID || true
grep "libcrypto" s2nd_out | grep "AWS-LC"
grep "CONNECTED" s2nd_out

# handshake test 3 - aws-lc bssl server with s2n-tls s2nc client for SecP256r1MLKEM768
cd "${scratch_folder}/s2n-tls"
./aws-lc/build/tool/bssl s_server -curves SecP256r1MLKEM768 -accept 45000 -debug &
S_PID=$!
sleep 2
./build-with-lc/bin/s2nc -c default_pq -i localhost 45000 > s2nc_out
kill $S_PID || true
grep "libcrypto" s2nc_out | grep "AWS-LC"
grep "CONNECTED" s2nc_out

# handshake test 4 -  s2n-tls s2nd server with aws-lc bssl client for SecP256r1MLKEM768
cd "${scratch_folder}/s2n-tls"
./build-with-lc/bin/s2nd -c default_pq -i localhost 45000 > s2nd_out &
S_PID=$!
sleep 2
./aws-lc/build/tool/bssl s_client -curves SecP256r1MLKEM768 -connect localhost:45000 -debug &
C_PID=$!
sleep 2
kill $S_PID || true
kill $C_PID || true
grep "libcrypto" s2nd_out | grep "AWS-LC"
grep "CONNECTED" s2nd_out

rm -rf "${scratch_folder:?}"/*