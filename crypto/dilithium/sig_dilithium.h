// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#ifndef SIG_DILITHIUM_H
#define SIG_DILITHIUM_H

#include <stddef.h>
#include <stdint.h>
#include <openssl/base.h>
#include <openssl/evp.h>

// The values below are taken from the |api.h| file in the
// |crypto/dilithium/pqcrystals_dilithium_ref_common| directory.
#define DILITHIUM3_PUBLIC_KEY_BYTES 1952
#define DILITHIUM3_PRIVATE_KEY_BYTES 4000
#define DILITHIUM3_SIGNATURE_BYTES 3293

// DILITHIUM3_keypair generates a Dilithium3 keypair and assigns a public key to
// |public_key| and a private key to |secret_key|. The function is a wrapper for
// the keygen function from the Dilithium source. It returns 0 upon success.
int DILITHIUM3_keypair(uint8_t *public_key,
                       uint8_t *secret_key);

// DILITHIUM3_sign generates a Dilithium3 signature. Where |sig| is a pointer to
// output signature, |sig_len| is a pointer to output length of signature,
// |message| is a pointer to message to be signed, |message_len| is the length
// of the message and |secret_key| is a pointer to bit-packed secret key.
// It returns 0 upon success.
int DILITHIUM3_sign(uint8_t *sig, size_t *sig_len,
                    const uint8_t *message,
                    size_t message_len,
                    const uint8_t *secret_key);

// DILITHIUM3_verify generates a Dilithium3 signature. Where |sig| is a pointer
// to input signature, |sig_len| is the length of the signature, |message| is
// a pointer to message, |message_len| is the length of the message and
// |public_key| is a pointer to bit-packed public key. Returns 0 if signature
// could be verified successfully and -1 otherwise.
int DILITHIUM3_verify(const uint8_t *message,
                      size_t message_len,
                      const uint8_t *sig,
                      size_t sig_len,
                      const uint8_t *public_key);

#endif
