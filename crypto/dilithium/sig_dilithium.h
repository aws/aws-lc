// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef SIG_DILITHIUM_H
#define SIG_DILITHIUM_H

#include <stddef.h>
#include <stdint.h>
#include <openssl/base.h>
#include <openssl/evp.h>

#define DILITHIUM3_PUBLIC_KEY_BYTES 1952
#define DILITHIUM3_PRIVATE_KEY_BYTES 4032
#define DILITHIUM3_SIGNATURE_BYTES 3309

// ml_dsa_65_keypair generates an ML-DSA-65 keypair and assigns a public key to
// |public_key| and a private key to |secret_key|. It returns 0 upon success.
int ml_dsa_65_keypair(uint8_t *public_key,
                       uint8_t *secret_key);

// ml_dsa_65_sign generates an ML-DSA-65 signature. Where |sig| is a pointer to
// output signature, |sig_len| is a pointer to output length of signature,
// |message| is a pointer to message to be signed, |message_len| is the length
// of the message, |ctx| is a pointer to the context string, |ctx_len| is the
// length of the context string (max length 255 bytes), and |secret_key| is a
// pointer to bit-packed secret key. It returns 0 upon success.
int ml_dsa_65_sign(uint8_t *sig, size_t *sig_len,
                    const uint8_t *message,
                    size_t message_len,
                    const uint8_t *ctx,
                    size_t ctx_len,
                    const uint8_t *secret_key);

// ml_dsa_65_verify generates an ML-DSA-65 signature. Where |sig| is a pointer
// to input signature, |sig_len| is the length of the signature, |message| is
// a pointer to message, |message_len| is the length of the message, |ctx| is a
// pointer to the context string, |ctx_len| is the length of the context string
// (max length 255 bytes) and |public_key| is a pointer to bit-packed public key.
// Returns 0 if signature could be verified successfully and -1 otherwise.
int ml_dsa_65_verify(const uint8_t *message,
                      size_t message_len,
                      const uint8_t *sig,
                      size_t sig_len,
                      const uint8_t *ctx,
                      size_t ctx_len,
                      const uint8_t *public_key);
#endif
