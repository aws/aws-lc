// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef OPENSSL_HEADER_CRYPTO_RAND_ENTROPY_INTERNAL_H
#define OPENSSL_HEADER_CRYPTO_RAND_ENTROPY_INTERNAL_H

#include <openssl/ctrdrbg.h>

#include "../new_rand_internal.h"

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

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_CRYPTO_RAND_ENTROPY_INTERNAL_H
