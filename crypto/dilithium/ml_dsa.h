// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef ML_DSA_H
#define ML_DSA_H

#include <stddef.h>
#include <stdint.h>
#include <openssl/base.h>
#include <openssl/evp.h>

#define MLDSA65_PUBLIC_KEY_BYTES 1952
#define MLDSA65_PRIVATE_KEY_BYTES 4032
#define MLDSA65_SIGNATURE_BYTES 3309
#define MLDSA65_KEYGEN_SEED_BYTES 32
#define MLDSA65_SIGNATURE_SEED_BYTES 32

int ml_dsa_65_keypair(uint8_t *public_key,
                       uint8_t *secret_key);

int ml_dsa_65_sign(const uint8_t *secret_key,
                   uint8_t *sig,
                   size_t *sig_len,
                   const uint8_t *message,
                   size_t message_len,
                   const uint8_t *ctx_string,
                   size_t ctx_string_len);

int ml_dsa_65_verify(const uint8_t *public_key,
                     const uint8_t *sig,
                     size_t sig_len,
                     const uint8_t *message,
                     size_t message_len,
                     const uint8_t *ctx_string,
                     size_t ctx_string_len);
#endif
