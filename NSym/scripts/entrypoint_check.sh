#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

# Translate Cryptol specifications to Ocaml
INFILE=./spec/SHA512rec.icry
OUTFILE=./proof/autospecs/SHA512/SHA512rec.ml
ASTFILE=./spec/SHA512rec.ast
cryptol-to-air -i $INFILE -o $OUTFILE -a $ASTFILE -u S0,S1,s0,s1,Ch,Maj,messageSchedule_Word,compress_Common_t1,compress_Common_t2,compress_Common_e,compress_Common_a,processBlock_Common_rec,processBlocks_rec

INFILE=./spec/SHA384rec.icry
OUTFILE=./proof/autospecs/SHA512/SHA384rec.ml
ASTFILE=./spec/SHA384rec.ast
cryptol-to-air -i $INFILE -o $OUTFILE -a $ASTFILE -u S0,S1,s0,s1,Ch,Maj,messageSchedule_Word,compress_Common_t1,compress_Common_t2,compress_Common_e,compress_Common_a,processBlock_Common_rec,processBlocks_rec

# Run test vector check for auto-generated specification
make -C ./proof sha384_spec
make -C ./proof sha512_spec

rm -rf build/
rm -rf build_src/

# Build crypto_test binary for Graviton2
./scripts/build_aarch64.sh "Release" "neoverse-n1"
./scripts/post_build.sh

cp -r ./build ./proof/

# Run SHA512 proof for Graviton2
export NSYM_SHA2_VERSION=SHA512
make -C ./proof sha2_grav2
# Run SHA384 proof for Graviton2
export NSYM_SHA2_VERSION=SHA384
make -C ./proof sha2_grav2

rm -rf build/
rm -rf build_src/

# Build crypto_test binary for Graviton3
./scripts/build_aarch64.sh "Release" "neoverse-512tvb"
./scripts/post_build.sh

cp -r ./build ./proof/

# Run SHA512 proof for Graviton3
export NSYM_SHA2_VERSION=SHA512
make -C ./proof sha2_grav3
# Run SHA384 proof for Graviton3
export NSYM_SHA2_VERSION=SHA384
make -C ./proof sha2_grav3
