#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
set -ex

source tests/ci/common_posix_setup.sh

SCRATCH_FOLDER=${SYS_ROOT}/"pq-tls-scratch"

AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"
AWS_LC_CMD="${AWS_LC_BUILD_FOLDER}/tool/bssl"

S2N_URL='https://github.com/aws/s2n-tls.git'
S2N_BRANCH='main'
S2N_TLS_SRC_FOLDER="${SCRATCH_FOLDER}/s2n-tls"
S2N_TLS_BUILD_FOLDER="${SCRATCH_FOLDER}/s2n-tls-build"
S2NC_CMD=${S2N_TLS_BUILD_FOLDER}/bin/s2nc
S2ND_CMD=${S2N_TLS_BUILD_FOLDER}/bin/s2nd

BSSL_URL='https://github.com/google/boringssl.git'
BSSL_BRANCH='main'
BSSL_SRC_FOLDER="${SCRATCH_FOLDER}/boring-ssl"
BSSL_BUILD_FOLDER="${SCRATCH_FOLDER}/boring-ssl-build"
BSSL_CMD="${SCRATCH_FOLDER}/boring-ssl-build/bssl"

SERVER_TIMEOUT_CMD="timeout --preserve-status --kill-after=60s 60s"
CLIENT_TIMEOUT_CMD="timeout --preserve-status --kill-after=10s 10s"

rm -rf "${SCRATCH_FOLDER:?}"
mkdir -p "$SCRATCH_FOLDER"

echo "build and install aws-lc"
# Using Debug build as it uses the '-g' compiler flag with gcc without any optimization
aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DCMAKE_BUILD_TYPE=Debug -DBUILD_TESTING=OFF

[[ -f ${AWS_LC_CMD} ]] || ( echo "Error building AWS-LC. ${AWS_LC_CMD} not found." && exit 1 )
echo "AWS-LC build succeeded. Found ${AWS_LC_CMD}"

echo "clone s2n-tls"
git clone --depth 1 --branch "$S2N_BRANCH" "$S2N_URL" "$S2N_TLS_SRC_FOLDER"

echo "build s2n-tls with aws-lc"
cd "$S2N_TLS_SRC_FOLDER"
cmake . "-B$S2N_TLS_BUILD_FOLDER" -GNinja \
  -DCMAKE_BUILD_TYPE=Debug \
  -DCMAKE_PREFIX_PATH="$AWS_LC_INSTALL_FOLDER"
# Suppress stdout for build
ninja -C "$S2N_TLS_BUILD_FOLDER" -j "$NUM_CPU_THREADS" > /dev/null

[[ -f ${S2NC_CMD} ]] || ( echo "Error building s2nc. ${S2NC_CMD} not found." && exit 1 )
[[ -f ${S2ND_CMD} ]] || ( echo "Error building s2nd. ${S2ND_CMD} not found." && exit 1 )
echo "s2n build succeeded. Found: ${S2NC_CMD} ${S2ND_CMD}"

for GROUP in X25519MLKEM768 SecP256r1MLKEM768; do
  echo "TLS Handshake: aws-lc server (bssl) with s2n-tls client (s2nc) for group $GROUP"
  ${SERVER_TIMEOUT_CMD} ${AWS_LC_CMD} s_server -curves $GROUP -accept 45000 -debug \
    &> "$AWS_LC_BUILD_FOLDER"/s_server_out &
  sleep 5 # to allow for the server to startup in the background thread
  S_PID=$!
  ${CLIENT_TIMEOUT_CMD} ${S2NC_CMD} -c default_pq -i localhost 45000 &> "$S2N_TLS_BUILD_FOLDER"/s2nc_out &
  wait $S_PID || true
  cat "$AWS_LC_BUILD_FOLDER"/s_server_out
  cat "$S2N_TLS_BUILD_FOLDER"/s2nc_out
  grep "libcrypto" "$S2N_TLS_BUILD_FOLDER"/s2nc_out | grep "AWS-LC"
  grep "CONNECTED" "$S2N_TLS_BUILD_FOLDER"/s2nc_out
  grep "KEM Group" "$S2N_TLS_BUILD_FOLDER"/s2nc_out | grep "$GROUP"

  echo "TLS Handshake: s2n-tls server (s2nd) with aws-lc client (bssl) for group $GROUP"
  ${SERVER_TIMEOUT_CMD} ${S2ND_CMD} -c default_pq -i localhost 45000 &> "$S2N_TLS_BUILD_FOLDER"/s2nd_out &
  sleep 5 # to allow for the server to startup in the background thread
  S_PID=$!
  ${CLIENT_TIMEOUT_CMD} ${AWS_LC_CMD} s_client -curves $GROUP -connect localhost:45000 -debug \
    &> "$AWS_LC_BUILD_FOLDER"/s_client_out &
  wait $S_PID || true
  cat "$S2N_TLS_BUILD_FOLDER"/s2nd_out
  cat "$AWS_LC_BUILD_FOLDER"/s_client_out
  grep "libcrypto" "$S2N_TLS_BUILD_FOLDER"/s2nd_out | grep "AWS-LC"
  grep "CONNECTED" "$S2N_TLS_BUILD_FOLDER"/s2nd_out
  grep "KEM Group" "$S2N_TLS_BUILD_FOLDER"/s2nd_out | grep "$GROUP"
done

echo "clone boring-ssl"
git clone --depth 1 --branch "$BSSL_BRANCH" "$BSSL_URL" "$BSSL_SRC_FOLDER"

echo "build boring-ssl with aws-lc"
cd "$BSSL_SRC_FOLDER"
# BoringSSL build fails with -DCMAKE_BUILD_TYPE=Release, when built in x86 ubuntu-22.04_gcc-12x container.
# Release builds use gcc optimization level 3 '-O3' which fails in the above linux container build.
# Optimizations are not required for this test, and it increases build time as well.
# Using Debug build that only uses the '-g' compiler flag with gcc without any optimization.
cmake . "-B$BSSL_BUILD_FOLDER" -GNinja -DCMAKE_BUILD_TYPE=Debug
# Suppress stdout for build
ninja -C "$BSSL_BUILD_FOLDER" -j "$NUM_CPU_THREADS" >/dev/null

[[ -f ${BSSL_CMD} ]] || ( echo "Error building BoringSSL. ${BSSL_CMD} not found." && exit 1 )
echo "BoringSSL build succeeded. Found ${BSSL_CMD}"

# BoringSSL supports only X25519MLKEM768 but not SecP256r1MLKEM768 for key exchange
for GROUP in X25519MLKEM768; do
  echo "TLS Handshake: aws-lc server (bssl) with boring-ssl client (bssl) for group $GROUP"
  ${SERVER_TIMEOUT_CMD} ${AWS_LC_CMD} s_server -curves $GROUP -accept 45000 -debug \
    &> "$AWS_LC_BUILD_FOLDER"/s_server_out &
  sleep 5 # to allow for the server to startup in the background thread
  S_PID=$!
  ${CLIENT_TIMEOUT_CMD} ${BSSL_CMD} s_client -curves $GROUP -connect localhost:45000 -debug \
    &> "$BSSL_BUILD_FOLDER"/s_client_out &
  wait $S_PID || true
  cat "$AWS_LC_BUILD_FOLDER"/s_server_out
  cat "$BSSL_BUILD_FOLDER"/s_client_out
  grep "Connected" "$AWS_LC_BUILD_FOLDER"/s_server_out
  grep "ECDHE group" "$AWS_LC_BUILD_FOLDER"/s_server_out | grep "$GROUP"
  grep "Connected" "$BSSL_BUILD_FOLDER"/s_client_out
  grep "ECDHE group" "$BSSL_BUILD_FOLDER"/s_client_out | grep "$GROUP"
  grep "subject" "$BSSL_BUILD_FOLDER"/s_client_out | grep "BoringSSL"

  echo "TLS Handshake: boring-ssl server (bssl) with aws-lc client (bssl) for group $GROUP"
  ${SERVER_TIMEOUT_CMD} ${BSSL_CMD} s_server -curves $GROUP -accept 45000 -debug \
    &> "$BSSL_BUILD_FOLDER"/s_server_out &
  sleep 5 # to allow for the server to startup in the background thread
  S_PID=$!
  ${CLIENT_TIMEOUT_CMD} ${AWS_LC_CMD} s_client -curves $GROUP -connect localhost:45000 -debug \
    &> "$AWS_LC_BUILD_FOLDER"/s_client_out &
  wait $S_PID || true
  cat "$BSSL_BUILD_FOLDER"/s_server_out
  cat "$AWS_LC_BUILD_FOLDER"/s_client_out
  grep "Connected" "$BSSL_BUILD_FOLDER"/s_server_out
  grep "ECDHE group" "$BSSL_BUILD_FOLDER"/s_server_out | grep "$GROUP"
  grep "Connected" "$AWS_LC_BUILD_FOLDER"/s_client_out
  grep "ECDHE group" "$AWS_LC_BUILD_FOLDER"/s_client_out | grep "$GROUP"
  grep "subject" "$AWS_LC_BUILD_FOLDER"/s_client_out | grep "BoringSSL"
done

rm -rf "${SCRATCH_FOLDER:?}"
