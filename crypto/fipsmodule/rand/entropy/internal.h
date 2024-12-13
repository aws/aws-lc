// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef OPENSSL_HEADER_CRYPTO_RAND_ENTROPY_INTERNAL_H
#define OPENSSL_HEADER_CRYPTO_RAND_ENTROPY_INTERNAL_H

#include <openssl/ctrdrbg.h>

#include "../new_rand_internal.h"
#include "../../cpucap/internal.h"

#if defined(__cplusplus)
extern "C" {
#endif

#define ENTROPY_JITTER_MAX_NUM_TRIES (3)

struct entropy_source_t {
  void *state;
  const struct entropy_source_methods *methods;
};

struct entropy_source_methods {
  int (*initialize)(struct entropy_source_t *entropy_source);
  void (*zeroize_thread)(struct entropy_source_t *entropy_source);
  void (*free_thread)(struct entropy_source_t *entropy_source);
  int (*get_seed)(const struct entropy_source_t *entropy_source,
    uint8_t seed[CTR_DRBG_ENTROPY_LEN]);
  int (*get_extra_entropy)(const struct entropy_source_t *entropy_source,
    uint8_t extra_entropy[CTR_DRBG_ENTROPY_LEN]);
  int (*get_prediction_resistance)(const struct entropy_source_t *entropy_source,
    uint8_t pred_resistance[RAND_PRED_RESISTANCE_LEN]);
};

// get_entropy_source will return an entropy source configured for the platform.
struct entropy_source_t * get_entropy_source(void);

OPENSSL_EXPORT int tree_jitter_initialize(struct entropy_source_t *entropy_source);
OPENSSL_EXPORT void tree_jitter_zeroize_thread_drbg(struct entropy_source_t *entropy_source);
OPENSSL_EXPORT void tree_jitter_free_thread_drbg(struct entropy_source_t *entropy_source);
OPENSSL_EXPORT int tree_jitter_get_seed(
  const struct entropy_source_t *entropy_source, uint8_t seed[CTR_DRBG_ENTROPY_LEN]);

// rndr_multiple8 writes |len| number of bytes to |buf| generated using the
// rndr instruction. |len| must be a multiple of 8.
// Outputs 1 on success, 0 otherwise.
OPENSSL_EXPORT int rndr_multiple8(uint8_t *buf, const size_t len);

// have_hw_rng_aarch64_for_testing wraps |have_hw_rng_aarch64| to allow usage
// in testing.
OPENSSL_EXPORT int have_hw_rng_aarch64_for_testing(void);

#if defined(OPENSSL_AARCH64) && !defined(OPENSSL_NO_ASM)

// CRYPTO_rndr_multiple8 writes |len| number of bytes to |buf| generated using
// the rndr instruction. |len| must be a multiple of 8 and positive.
// Outputs 1 on success, 0 otherwise.
int CRYPTO_rndr_multiple8(uint8_t *out, size_t out_len);

// Returns 1 if Armv8-A instruction rndr is available, 0 otherwise.
OPENSSL_INLINE int have_hw_rng_aarch64(void) {
  return CRYPTO_is_ARMv8_RNDR_capable();
}

#else  // defined(OPENSSL_AARCH64) && !defined(OPENSSL_NO_ASM)

OPENSSL_INLINE int CRYPTO_rndr_multiple8(uint8_t *out, size_t out_len) {
  return 0;
}

OPENSSL_INLINE int have_hw_rng_aarch64(void) {
  return 0;
}

#endif  // defined(OPENSSL_AARCH64) && !defined(OPENSSL_NO_ASM)

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_CRYPTO_RAND_ENTROPY_INTERNAL_H
