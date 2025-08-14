// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// This file mocks entropy sources. It's not final.
// We use it to implement the basic randomness generation code flow.

#include <openssl/base.h>
#include <openssl/target.h>

#include "internal.h"
#include "../internal.h"
#include "../../delocate.h"
#include "../../../rand_extra/internal.h"

DEFINE_BSS_GET(const struct entropy_source_methods *, entropy_source_methods_override)
DEFINE_BSS_GET(int, allow_entropy_source_methods_override)
DEFINE_STATIC_MUTEX(global_entropy_source_lock)

static int entropy_get_prediction_resistance(
  const struct entropy_source_t *entropy_source,
  uint8_t pred_resistance[RAND_PRED_RESISTANCE_LEN]) {
#if defined(OPENSSL_X86_64)
  if (rdrand_multiple8(pred_resistance, RAND_PRED_RESISTANCE_LEN) == 1) {
    return 1;
  }
#elif defined(OPENSSL_AARCH64)
  if (rndr_multiple8(pred_resistance, RAND_PRED_RESISTANCE_LEN) == 1) {
    return 1;
  }
#endif
  return 0;
}

static int entropy_get_extra_entropy(
  const struct entropy_source_t *entropy_source,
  uint8_t extra_entropy[CTR_DRBG_ENTROPY_LEN]) {
  CRYPTO_sysrand(extra_entropy, CTR_DRBG_ENTROPY_LEN);
  return 1;
}

// - Tree DRBG with Jitter Entropy as root for seeding.
// - OS as personalization string source.
// - If run-time is on an x86_64 or Arm64 CPU and it supports rdrand
//   or rndr respectively, use it as a source for prediction resistance.
//   Otherwise, no source.
DEFINE_LOCAL_DATA(struct entropy_source_methods, tree_jitter_entropy_source_methods) {
  out->initialize = tree_jitter_initialize;
  out->zeroize_thread = tree_jitter_zeroize_thread_drbg;
  out->free_thread = tree_jitter_free_thread_drbg;
  out->get_seed = tree_jitter_get_seed;
  out->get_extra_entropy = entropy_get_extra_entropy;
  if (have_hw_rng_x86_64() == 1 ||
      have_hw_rng_aarch64() == 1) {
    out->get_prediction_resistance = entropy_get_prediction_resistance;
  } else {
    out->get_prediction_resistance = NULL;
  }
}

static const struct entropy_source_methods * get_entropy_source_methods(void) {
  if (*allow_entropy_source_methods_override_bss_get() == 1) {
    return *entropy_source_methods_override_bss_get();
  }

  return tree_jitter_entropy_source_methods();
}

struct entropy_source_t * get_entropy_source(void) {

  struct entropy_source_t *entropy_source = OPENSSL_zalloc(sizeof(struct entropy_source_t));
  if (entropy_source == NULL) {
    return NULL;
  }

  entropy_source->methods = get_entropy_source_methods();

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

int rndr_multiple8(uint8_t *buf, const size_t len) {
  if (len == 0 || ((len & 0x7) != 0)) {
    return 0;
  }
  return CRYPTO_rndr_multiple8(buf, len);
}

int have_hw_rng_aarch64_for_testing(void) {
  return have_hw_rng_aarch64();
}

// rdrand maximum retries as suggested by:
// Intel® Digital Random Number Generator (DRNG) Software Implementation Guide
// Revision 2.1
// https://software.intel.com/content/www/us/en/develop/articles/intel-digital-random-number-generator-drng-software-implementation-guide.html
#define RDRAND_MAX_RETRIES 10
OPENSSL_STATIC_ASSERT(RDRAND_MAX_RETRIES > 0, rdrand_max_retries_must_be_positive)

// rdrand_multiple8 should only be called if |have_hw_rng_x86_64| returned true.
int rdrand_multiple8(uint8_t *buf, size_t len) {
  if (len == 0 || ((len & 0x7) != 0)) {
    return 0;
  }

  // This retries all rdrand calls for the requested |len|.
  // |CRYPTO_rdrand_multiple8| will typically execute rdrand multiple times. But
  // it's easier to implement on the C-level and it should be a very rare event.
  for (size_t tries = 0; tries < RDRAND_MAX_RETRIES; tries++) {
    if (CRYPTO_rdrand_multiple8(buf, len) == 1) {
      return 1;
    }
  }

  return 0;
}

int have_hw_rng_x86_64_for_testing(void) {
  return have_hw_rng_x86_64();
}


void override_entropy_source_method_FOR_TESTING(
  const struct entropy_source_methods *override_entropy_source_methods) {

  CRYPTO_STATIC_MUTEX_lock_write(global_entropy_source_lock_bss_get());
  *allow_entropy_source_methods_override_bss_get() = 1;
  *entropy_source_methods_override_bss_get() = override_entropy_source_methods;
  CRYPTO_STATIC_MUTEX_unlock_write(global_entropy_source_lock_bss_get());
}
