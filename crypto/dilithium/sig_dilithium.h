// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#ifndef SIG_DILITHIUM_H
#define SIG_DILITHIUM_H

#include <stddef.h>
#include <stdint.h>
#include <openssl/evp.h>

#define DILITHIUM3_PUBLIC_KEY_BYTES 1952
#define DILITHIUM3_PRIVATE_KEY_BYTES 4000
#define DILITHIUM3_SIGNATURE_BYTES 3293

int DILITHIUM3_keypair(uint8_t *public_key, uint8_t *secret_key);

int DILITHIUM3_sign(uint8_t *sig, size_t *sig_len,
					const uint8_t *message, size_t message_len,
					const uint8_t *secret_key);

int DILITHIUM3_verify(const uint8_t *message, size_t message_len,
                    const uint8_t *sig, size_t sig_len,
                    const uint8_t *public_key);

#endif
