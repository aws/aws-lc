// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_HEADER_PQT_KEM_H
#define AWSLC_HEADER_PQT_KEM_H

#include <stdint.h>

#include <openssl/curve25519.h>
#include <openssl/ec.h>

#include "../ml_kem/ml_kem.h"

#if defined(__cplusplus)
extern "C" {
#endif

// Digest Constants
// ----------------
#define PQT25519_DIGEST EVP_sha256
#define PQT256_DIGEST EVP_sha256
#define PQT384_DIGEST EVP_sha384

// PQ KEM Constants
// ----------------
// ML-KEM 768 Constants
#define PQ768_PUBLIC_KEY_BYTES MLKEM768IPD_PUBLIC_KEY_BYTES
#define PQ768_SECRET_KEY_BYTES MLKEM768IPD_SECRET_KEY_BYTES
#define PQ768_CIPHERTEXT_BYTES MLKEM768IPD_CIPHERTEXT_BYTES
#define PQ768_SHARED_SECRET_LEN MLKEM768IPD_SHARED_SECRET_LEN
#define PQ768_KEYGEN_SEED_LEN MLKEM1024IPD_KEYGEN_SEED_LEN
#define PQ768_ENCAPS_SEED_LEN MLKEM1024IPD_ENCAPS_SEED_LEN

// ML-KEM 1024 Constants
#define PQ1024_PUBLIC_KEY_BYTES MLKEM1024IPD_PUBLIC_KEY_BYTES
#define PQ1024_SECRET_KEY_BYTES MLKEM1024IPD_SECRET_KEY_BYTES
#define PQ1024_CIPHERTEXT_BYTES MLKEM1024IPD_CIPHERTEXT_BYTES
#define PQ1024_SHARED_SECRET_LEN MLKEM1024IPD_SHARED_SECRET_LEN
#define PQ1024_KEYGEN_SEED_LEN MLKEM1024IPD_KEYGEN_SEED_LEN
#define PQ1024_ENCAPS_SEED_LEN MLKEM1024IPD_ENCAPS_SEED_LEN

// T KEM Constants
// ---------------

// NIST-P Keygen uses [group order] + [128 extra bits] to deterministically
// generate a key. The extra bits ensure that the bias is negligible. With 128
// extra bits, the bias is <=2^(-128). This method is described in Section A.2.1
// of FIPS 186-5 and Section 5.6.1.2.1 of NIST.SP.800-56Ar3.
#define NISTP_EXTRA_BYTES 16

#define P256_KEYGEN_SEED (32 + NISTP_EXTRA_BYTES)
#define P384_KEYGEN_SEED (48 + NISTP_EXTRA_BYTES)

// X25519 Constants, from Section 7.1 of RFC 9180
#define T25519_PUBLIC_KEY_BYTES X25519_PUBLIC_VALUE_LEN
#define T25519_SECRET_KEY_BYTES X25519_PRIVATE_KEY_LEN
#define T25519_CIPHERTEXT_BYTES T25519_PUBLIC_KEY_BYTES
#define T25519_SHARED_SECRET_LEN X25519_SHARED_KEY_LEN
#define T25519_KEYGEN_SEED_LEN T25519_SECRET_KEY_BYTES
#define T25519_ENCAPS_SEED_LEN T25519_SECRET_KEY_BYTES

// P256 Constants, from Section 7.1 of RFC 9180
#define T256_PUBLIC_KEY_BYTES 65
#define T256_SECRET_KEY_BYTES 32
#define T256_CIPHERTEXT_BYTES T256_PUBLIC_KEY_BYTES
#define T256_SHARED_SECRET_LEN 32
#define T256_KEYGEN_SEED_LEN P256_KEYGEN_SEED
#define T256_ENCAPS_SEED_LEN P256_KEYGEN_SEED

// P384 Constants, from Section 7.1 of RFC 9180
#define T384_PUBLIC_KEY_BYTES 97
#define T384_SECRET_KEY_BYTES 48
#define T384_CIPHERTEXT_BYTES T384_PUBLIC_KEY_BYTES
#define T384_SHARED_SECRET_LEN 48
#define T384_KEYGEN_SEED_LEN P384_KEYGEN_SEED
#define T384_ENCAPS_SEED_LEN P384_KEYGEN_SEED

// PQ/T KEM Constants
// ----------------
// Shared secret length for all PQT KEMs
#define PQT_SHARED_SECRET_LEN 32

// PQT25519 Constants
#define PQT25519_PUBLIC_KEY_BYTES \
  (PQ768_PUBLIC_KEY_BYTES + T25519_PUBLIC_KEY_BYTES)
#define PQT25519_SECRET_KEY_BYTES \
  (PQ768_SECRET_KEY_BYTES + T25519_SECRET_KEY_BYTES + T25519_PUBLIC_KEY_BYTES)
#define PQT25519_CIPHERTEXT_BYTES \
  (PQ768_CIPHERTEXT_BYTES + T25519_CIPHERTEXT_BYTES)
#define PQT25519_SHARED_SECRET_LEN PQT_SHARED_SECRET_LEN
#define PQT25519_KEYGEN_SEED_LEN \
  (PQ768_KEYGEN_SEED_LEN + T25519_KEYGEN_SEED_LEN)
#define PQT25519_ENCAPS_SEED_LEN \
  (PQ768_ENCAPS_SEED_LEN + T25519_ENCAPS_SEED_LEN)

// PQT256 Constants
#define PQT256_PUBLIC_KEY_BYTES (PQ768_PUBLIC_KEY_BYTES + T256_PUBLIC_KEY_BYTES)
#define PQT256_SECRET_KEY_BYTES \
  (PQ768_SECRET_KEY_BYTES + T256_SECRET_KEY_BYTES + T256_PUBLIC_KEY_BYTES)
#define PQT256_CIPHERTEXT_BYTES (PQ768_CIPHERTEXT_BYTES + T256_CIPHERTEXT_BYTES)
#define PQT256_SHARED_SECRET_LEN PQT_SHARED_SECRET_LEN
#define PQT256_KEYGEN_SEED_LEN (PQ768_KEYGEN_SEED_LEN + T256_KEYGEN_SEED_LEN)
#define PQT256_ENCAPS_SEED_LEN (PQ768_ENCAPS_SEED_LEN + T256_ENCAPS_SEED_LEN)

// PQT384 Constants
#define PQT384_PUBLIC_KEY_BYTES \
  (PQ1024_PUBLIC_KEY_BYTES + T384_PUBLIC_KEY_BYTES)
#define PQT384_SECRET_KEY_BYTES \
  (PQ1024_SECRET_KEY_BYTES + T384_SECRET_KEY_BYTES + T384_PUBLIC_KEY_BYTES)
#define PQT384_CIPHERTEXT_BYTES \
  (PQ1024_CIPHERTEXT_BYTES + T384_CIPHERTEXT_BYTES)
#define PQT384_SHARED_SECRET_LEN PQT_SHARED_SECRET_LEN
#define PQT384_KEYGEN_SEED_LEN (PQ1024_KEYGEN_SEED_LEN + T384_KEYGEN_SEED_LEN)
#define PQT384_ENCAPS_SEED_LEN (PQ1024_ENCAPS_SEED_LEN + T384_ENCAPS_SEED_LEN)

// PQT25519 Functions
int pqt25519_keygen(uint8_t *public_key, uint8_t *secret_key);
int pqt25519_encaps(uint8_t *ciphertext, uint8_t *shared_secret,
                    const uint8_t *public_key);
int pqt25519_decaps(uint8_t *shared_secret, const uint8_t *ciphertext,
                    const uint8_t *secret_key);
int pqt25519_keygen_deterministic(uint8_t *public_key, uint8_t *secret_key,
                                  const uint8_t *seed);
int pqt25519_encaps_deterministic(uint8_t *ciphertext, uint8_t *shared_secret,
                                  const uint8_t *public_key,
                                  const uint8_t *seed);

// PQT256 Functions
int pqt256_keygen(uint8_t *public_key, uint8_t *secret_key);
int pqt256_encaps(uint8_t *ciphertext, uint8_t *shared_secret,
                  const uint8_t *public_key);
int pqt256_decaps(uint8_t *shared_secret, const uint8_t *ciphertext,
                  const uint8_t *secret_key);
int pqt256_keygen_deterministic(uint8_t *public_key, uint8_t *secret_key,
                                const uint8_t *seed);
int pqt256_encaps_deterministic(uint8_t *ciphertext, uint8_t *shared_secret,
                                const uint8_t *public_key, const uint8_t *seed);

// PQT384 Functions
int pqt384_keygen(uint8_t *public_key, uint8_t *secret_key);
int pqt384_encaps(uint8_t *ciphertext, uint8_t *shared_secret,
                  const uint8_t *public_key);
int pqt384_decaps(uint8_t *shared_secret, const uint8_t *ciphertext,
                  const uint8_t *secret_key);
int pqt384_keygen_deterministic(uint8_t *public_key, uint8_t *secret_key,
                                const uint8_t *seed);
int pqt384_encaps_deterministic(uint8_t *ciphertext, uint8_t *shared_secret,
                                const uint8_t *public_key, const uint8_t *seed);

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // AWSLC_HEADER_PQT_KEM_H
