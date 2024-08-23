// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef OPENSSL_HEADER_CRYPTO_RAND_ENTROPY_INTERNAL_H
#define OPENSSL_HEADER_CRYPTO_RAND_ENTROPY_INTERNAL_H

#include <openssl/ctrdrbg.h>

#include "../new_rand_internal.h"

#if defined(__cplusplus)
extern "C" {
#endif

// I could make these array types!
struct entropy_source {
  int is_initialized;
  int (*initialize)(void);
  int (*cleanup)(void);
  int (*get_seed)(uint8_t seed[CTR_DRBG_ENTROPY_LEN]);
  int (*get_personalization_string)(uint8_t personalization_string[CTR_DRBG_ENTROPY_LEN]);
  int (*get_prediction_resistance)(uint8_t pred_resistance[RAND_PRED_RESISTANCE_LEN]);
  int (*randomize)(void);
};

// get_entropy_source will configure an entropy source in |entropy_source|.
int get_entropy_source(struct entropy_source *entropy_source);

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_CRYPTO_RAND_ENTROPY_INTERNAL_H
