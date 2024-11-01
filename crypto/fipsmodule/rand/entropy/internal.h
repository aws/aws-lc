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
  int (*initialize)(void);
  void (*cleanup)(void);
  int (*get_seed)(uint8_t seed[CTR_DRBG_ENTROPY_LEN]);
  int (*get_extra_entropy)(uint8_t extra_entropy[CTR_DRBG_ENTROPY_LEN]);
  int (*get_prediction_resistance)(uint8_t pred_resistance[RAND_PRED_RESISTANCE_LEN]);
  int (*randomize)(void);
};

// get_entropy_source will return an entropy source configured for the platform.
const struct entropy_source * get_entropy_source(void);

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_CRYPTO_RAND_ENTROPY_INTERNAL_H
