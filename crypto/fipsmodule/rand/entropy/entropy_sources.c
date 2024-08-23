// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// This file mocks entropy sources. It's not final.
// We use it to implement the basic randomness generation code flow.

#include <openssl/base.h>

#include "internal.h"

static int fake_void(void) {
  return 1;
}

static int fake_rand(uint8_t a[CTR_DRBG_ENTROPY_LEN]) {
  OPENSSL_cleanse(a, CTR_DRBG_ENTROPY_LEN);
  return 1;
}

static int fake_rand_(uint8_t a[RAND_PRED_RESISTANCE_LEN]) {
  OPENSSL_cleanse(a, RAND_PRED_RESISTANCE_LEN);
  return 1;
}

int get_entropy_source(struct entropy_source *entropy_source) {

  // In the future this function will lazily initialise a global entropy source.

  GUARD_PTR(entropy_source);

  entropy_source->is_initialized = 1;
  entropy_source->initialize = fake_void;
  entropy_source->cleanup = fake_void;
  entropy_source->get_seed = fake_rand;
  entropy_source->get_personalization_string = fake_rand;
  entropy_source->get_prediction_resistance = fake_rand_;
  entropy_source->randomize = fake_void;

  return 1;
}
