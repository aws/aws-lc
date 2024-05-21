// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// These APIs are marked as experimental as the development and standardization
// of KEMs (e.g., for FIPS 203) are being finalized.

#include <openssl/base.h>

#if defined(__cplusplus)
extern "C" {
#endif

// EVP_PKEY_keygen_deterministic is an operation defined for a KEM (Key
// Encapsulation Mechanism). For the KEM specified in |ctx|, the function
// performs deterministic keygen based on the value specified in |seed| of
// length |seed_len| bytes.
//
// EVP_PKEY_keygen_deterministic performs a deterministic key generation
// operation using the values from |ctx|, and the given |seed|. If |*out_pkey|
// is non-NULL, it overwrites |*out_pkey| with the resulting key. Otherwise, it
// sets |*out_pkey| to a newly-allocated |EVP_PKEY| containing the result.
// It returns one on success or zero on error.
OPENSSL_EXPORT int EVP_PKEY_keygen_deterministic(EVP_PKEY_CTX *ctx   /* IN  */,
                                                 EVP_PKEY **out_pkey /* OUT */,
                                                 const uint8_t *seed /* IN  */,
                                                 size_t seed_len     /* IN  */);

// EVP_PKEY_encapsulate_deterministic is an operation defined for a KEM (Key
// Encapsulation Mechanism). The function performs the same encapsulation
// operations as EVP_PKEY_encapsulate, however, rather than generating a random
// for the |shared_secret|, the value is derived from the provided |seed| of
// |seed_len|.
//
// It returns one on success or zero on error.
OPENSSL_EXPORT int EVP_PKEY_encapsulate_deterministic(EVP_PKEY_CTX *ctx          /* IN  */,
                                                      uint8_t *ciphertext        /* OUT */,
                                                      size_t  *ciphertext_len    /* OUT */,
                                                      uint8_t *shared_secret     /* OUT */,
                                                      size_t  *shared_secret_len /* OUT */,
                                                      const uint8_t *seed        /* IN  */,
                                                      size_t seed_len            /* IN  */);

#if defined(__cplusplus)
}  // extern C
#endif
