// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// This file mocks entropy sources. It's not final.
// We use it to implement the basic randomness generation code flow.

#include <openssl/base.h>

#include "internal.h"
#include "../internal.h"
#include "../../delocate.h"

static int entropy_default_initialize(void) {
  return 1;
}

static void entropy_default_cleanup(void) {
}

static int entropy_default_get_seed(uint8_t seed[CTR_DRBG_ENTROPY_LEN]) {
  CRYPTO_sysrand_for_seed(seed, CTR_DRBG_ENTROPY_LEN);
  return 1;
}

static int entropy_default_get_prediction_resistance(
  uint8_t pred_resistance[RAND_PRED_RESISTANCE_LEN]) {
  if (have_fast_rdrand() == 1 &&
      rdrand(pred_resistance, RAND_PRED_RESISTANCE_LEN) != 1) {
    return 0;
  }
  return 1;
}

static int entropy_default_randomize(void) {
  return 1;
}

// The default entropy source configuration using
// - OS randomness source for seeding.
// - Doesn't have a personalization string source.
// - If run-time is on an Intel CPU and it supports rdrand, use it as a source
//   for prediction resistance. Otherwise, no source.
DEFINE_LOCAL_DATA(struct entropy_source, default_entropy_source) {
  out->initialize = entropy_default_initialize;
  out->cleanup = entropy_default_cleanup;
  out->get_seed = entropy_default_get_seed;
  out->get_personalization_string = NULL;
  if (have_fast_rdrand() == 1) {
    out->get_prediction_resistance = entropy_default_get_prediction_resistance;
  } else {
    out->get_prediction_resistance = NULL;
  }
  out->randomize = entropy_default_randomize;
}

const struct entropy_source * get_entropy_source(void) {
  const struct entropy_source *ent_source = default_entropy_source();

  // Make sure that the function table contains the minimal number of callbacks
  // that we expect. Also make sure that the entropy source is initialized such
  // that calling code can assume that.
  if (ent_source->cleanup == NULL ||
      ent_source->get_seed == NULL ||
      ent_source->randomize == NULL ||
      ent_source->initialize == NULL ||
      ent_source->initialize() != 1) {
    return NULL;
  }

  return ent_source;
}
