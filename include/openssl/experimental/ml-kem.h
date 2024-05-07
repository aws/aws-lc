// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// These APIs are marked as experimental as the development and standardization
// of KEMs (e.g., for FIPS 203) are being finalized.

#include <openssl/base.h>

#include <openssl/evp_errors.h>  // IWYU pragma: export
#include <openssl/thread.h>

#if defined(__cplusplus)
extern "C" {
#endif

// EVP_PKEY_keygen_deterministic is an operation defined for a KEM (Key
// Encapsulation Mechanism). For the KEM specified in |ctx|, the function
// performs deterministic keygen based on the value specified in |seed|.
//
// EVP_PKEY_keygen_deterministic performs a deterministic key generation
// operation using the values from |ctx|, and the given |seed|. If |*out_pkey|
// is non-NULL, it overwrites |*out_pkey| with the resulting key. Otherwise, it
// sets |*out_pkey| to a newly-allocated |EVP_PKEY| containing the result.
// It returns one on success or zero on error.
OPENSSL_EXPORT int EVP_PKEY_keygen_deterministic(EVP_PKEY_CTX *ctx   /* IN  */,
                                                 EVP_PKEY **out_pkey /* OUT */,
                                                 const uint8_t *seed /* IN  */);

// EVP_PKEY_encapsulate_deterministic is an operation defined for a KEM (Key
// Encapsulation Mechanism). For the KEM specified in |ctx|, the function:
//   1. generates a deterministic value (derived from |seed|) and writes it to
//      |shared_secret|,
//   2. encapsulates the shared secret, producing the ciphertext, by using
//      the public key in |ctx|, and writes the ciphertext to |ciphertext|,
//   3. writes the length of |ciphertext| and |shared_secret| to
//      |ciphertext_len| and |shared_secret_len|.
//
// The function requires that output buffers, |ciphertext| and |shared_secret|,
// be either both NULL or both non-NULL. Otherwise, a failure is returned.
//
// If both |ciphertext| and |shared_secret| are NULL it is assumed that
// the caller is doing a size check: the function will write the size of
// the ciphertext and the shared secret in |ciphertext_len| and
// |shared_secret_len| and return successfully.
//
// If both |ciphertext| and |shared_secret| are not NULL it is assumed that
// the caller is performing the actual operation. The function will check
// additionally if the lengths of the output buffers, |ciphertext_len| and
// |shared_secret_len|, are large enough for the KEM.
//
// NOTE: no allocation is done in the function, the caller is expected to
// provide large enough |ciphertext| and |shared_secret| buffers.
//
// It returns one on success or zero on error.
OPENSSL_EXPORT int EVP_PKEY_encapsulate_deterministic(EVP_PKEY_CTX *ctx          /* IN  */,
                                                      uint8_t *ciphertext        /* OUT */,
                                                      size_t  *ciphertext_len    /* OUT */,
                                                      uint8_t *shared_secret     /* OUT */,
                                                      size_t  *shared_secret_len /* OUT */,
                                                      const uint8_t *seed        /* IN  */);

#if defined(__cplusplus)
}  // extern C
#endif
