// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef OPENSSL_HEADER_CRYPTO_FIPSMODULE_SHA_SHA256_PRIVATE_NAMES_H
#define OPENSSL_HEADER_CRYPTO_FIPSMODULE_SHA_SHA256_PRIVATE_NAMES_H

// In Rust builds, libcrypto's SHA-224 and SHA-256 functions are Rust's
// (crypto/rust/sha256.c). bcm.c includes this header so that its copy of C's
// sha256.c takes private names instead, for bcm.c's own users: EVP_sha256,
// HMAC, ECDH, the self-tests and the integrity check. In FIPS builds those
// run inside bcm.o, which can't call into another module.
//
// bcm.c includes this before any code that names these functions. The
// headers that declare them come first, so their OPENSSL_EXPORT declarations
// keep the public names, and the private names get plain declarations,
// which libcrypto doesn't export.

#include <openssl/sha.h>

#include "internal.h"

#if defined(BORINGSSL_PREFIX)
#define BCM_C_SHA256_NAME(name) \
  BORINGSSL_ADD_PREFIX(BORINGSSL_PREFIX, bcm_c_##name)
#else
#define BCM_C_SHA256_NAME(name) bcm_c_##name
#endif

// The prefix headers may already rename these.
#undef SHA224_Init
#undef SHA256_Init
#undef SHA224_Init_from_state
#undef SHA256_Init_from_state
#undef SHA224_Update
#undef SHA256_Update
#undef SHA224_Final
#undef SHA256_Final
#undef SHA224
#undef SHA256
#undef SHA256_Transform
#undef SHA256_TransformBlocks
#undef SHA224_get_state
#undef SHA256_get_state

#define SHA224_Init BCM_C_SHA256_NAME(SHA224_Init)
#define SHA256_Init BCM_C_SHA256_NAME(SHA256_Init)
#define SHA224_Init_from_state BCM_C_SHA256_NAME(SHA224_Init_from_state)
#define SHA256_Init_from_state BCM_C_SHA256_NAME(SHA256_Init_from_state)
#define SHA224_Update BCM_C_SHA256_NAME(SHA224_Update)
#define SHA256_Update BCM_C_SHA256_NAME(SHA256_Update)
#define SHA224_Final BCM_C_SHA256_NAME(SHA224_Final)
#define SHA256_Final BCM_C_SHA256_NAME(SHA256_Final)
#define SHA224 BCM_C_SHA256_NAME(SHA224)
#define SHA256 BCM_C_SHA256_NAME(SHA256)
#define SHA256_Transform BCM_C_SHA256_NAME(SHA256_Transform)
#define SHA256_TransformBlocks BCM_C_SHA256_NAME(SHA256_TransformBlocks)
#define SHA224_get_state BCM_C_SHA256_NAME(SHA224_get_state)
#define SHA256_get_state BCM_C_SHA256_NAME(SHA256_get_state)

int SHA224_Init(SHA256_CTX *sha);
int SHA256_Init(SHA256_CTX *sha);
int SHA224_Init_from_state(SHA256_CTX *sha,
                           const uint8_t h[SHA224_CHAINING_LENGTH], uint64_t n);
int SHA256_Init_from_state(SHA256_CTX *sha,
                           const uint8_t h[SHA256_CHAINING_LENGTH], uint64_t n);
int SHA224_Update(SHA256_CTX *sha, const void *data, size_t len);
int SHA256_Update(SHA256_CTX *sha, const void *data, size_t len);
int SHA224_Final(uint8_t out[SHA224_DIGEST_LENGTH], SHA256_CTX *sha);
int SHA256_Final(uint8_t out[SHA256_DIGEST_LENGTH], SHA256_CTX *sha);
uint8_t *SHA224(const uint8_t *data, size_t len,
                uint8_t out[SHA224_DIGEST_LENGTH]);
uint8_t *SHA256(const uint8_t *data, size_t len,
                uint8_t out[SHA256_DIGEST_LENGTH]);
void SHA256_Transform(SHA256_CTX *sha, const uint8_t block[SHA256_CBLOCK]);
void SHA256_TransformBlocks(uint32_t state[8], const uint8_t *data,
                            size_t num_blocks);
int SHA224_get_state(SHA256_CTX *ctx, uint8_t out_h[SHA224_CHAINING_LENGTH],
                     uint64_t *out_n);
int SHA256_get_state(SHA256_CTX *ctx, uint8_t out_h[SHA256_CHAINING_LENGTH],
                     uint64_t *out_n);

#endif  // OPENSSL_HEADER_CRYPTO_FIPSMODULE_SHA_SHA256_PRIVATE_NAMES_H
