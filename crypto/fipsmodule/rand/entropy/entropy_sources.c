// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// This file mocks entropy sources. It's not final.
// We use it to implement the basic randomness generation code flow.

#include <openssl/base.h>

#include "internal.h"
#include "../internal.h"
#include "../../delocate.h"

static int entropy_get_prediction_resistance(
  const struct entropy_source_t *entropy_source,
  uint8_t pred_resistance[RAND_PRED_RESISTANCE_LEN]) {
  if (have_fast_rdrand() == 1 &&
      rdrand(pred_resistance, RAND_PRED_RESISTANCE_LEN) != 1) {
    return 0;
  }
  return 1;
}

static int entropy_get_extra_entropy(
  const struct entropy_source_t *entropy_source,
  uint8_t extra_entropy[CTR_DRBG_ENTROPY_LEN]) {
  CRYPTO_sysrand(extra_entropy, CTR_DRBG_ENTROPY_LEN);
  return 1;
}

// - Tree DRBG with Jitter Entropy as root for seeding.
// - OS as personalization string source.
// - If run-time is on an Intel CPU and it supports rdrand, use it as a source
//   for prediction resistance. Otherwise, no source.
DEFINE_LOCAL_DATA(struct entropy_source_methods, tree_jitter_entropy_source_methods) {
  out->initialize = tree_jitter_initialize;
  out->zeroize_thread = tree_jitter_zeroize_thread_drbg;
  out->free_thread = tree_jitter_free_thread_drbg;
  out->get_seed = tree_jitter_get_seed;
  out->get_extra_entropy = entropy_get_extra_entropy;
  if (have_fast_rdrand() == 1) {
    out->get_prediction_resistance = entropy_get_prediction_resistance;
  } else {
    out->get_prediction_resistance = NULL;
  }
}

struct entropy_source_t * get_entropy_source(void) {

  struct entropy_source_t *entropy_source = OPENSSL_zalloc(sizeof(struct entropy_source_t));
  if (entropy_source == NULL) {
    return NULL;
  }

  entropy_source->methods = tree_jitter_entropy_source_methods();

  // Make sure that the function table contains the minimal number of callbacks
  // that we expect. Also make sure that the entropy source is initialized such
  // that calling code can assume that.
  if (entropy_source->methods == NULL ||
      entropy_source->methods->zeroize_thread == NULL ||
      entropy_source->methods->free_thread == NULL ||
      entropy_source->methods->get_seed == NULL ||
      entropy_source->methods->initialize == NULL ||
      entropy_source->methods->initialize(entropy_source) != 1) {
    OPENSSL_free(entropy_source);
    return NULL;
  }

  return entropy_source;
}
