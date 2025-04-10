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

static int entropy_get_prediction_resistance(
  const struct entropy_source_t *entropy_source,
  uint8_t pred_resistance[RAND_PRED_RESISTANCE_LEN]) {
#if defined(OPENSSL_X86_64)
  if (rdrand(pred_resistance, RAND_PRED_RESISTANCE_LEN) == 1) {
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
// - If run-time is on an Intel CPU and it supports rdrand, use it as a source
//   for prediction resistance. Otherwise, no source.
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

#if defined(OPENSSL_X86_64) && !defined(OPENSSL_NO_ASM)

// rdrand maximum retries as suggested by:
// Intel® Digital Random Number Generator (DRNG) Software Implementation Guide
// Revision 2.1
// https://software.intel.com/content/www/us/en/develop/articles/intel-digital-random-number-generator-drng-software-implementation-guide.html
#define RDRAND_MAX_RETRIES 10

OPENSSL_STATIC_ASSERT(RDRAND_MAX_RETRIES > 0, rdrand_max_retries_must_be_positive)
#define CALL_RDRAND_WITH_RETRY(rdrand_func, fail_ret_value)       \
    for (size_t tries = 0; tries < RDRAND_MAX_RETRIES; tries++) { \
      if ((rdrand_func) == 1) {                                   \
        break;                                                    \
      } else if (tries >= RDRAND_MAX_RETRIES - 1) {               \
        return fail_ret_value;                                    \
      }                                                           \
    }

// rdrand should only be called if either |have_rdrand| or |have_fast_rdrand|
// returned true.
int rdrand(uint8_t *buf, const size_t len) {
  const size_t len_multiple8 = len & ~7;
  CALL_RDRAND_WITH_RETRY(CRYPTO_rdrand_multiple8_buf(buf, len_multiple8), 0)
  const size_t remainder = len - len_multiple8;

  if (remainder != 0) {
    assert(remainder < 8);

    uint8_t rand_buf[8];
    CALL_RDRAND_WITH_RETRY(CRYPTO_rdrand(rand_buf), 0)
    OPENSSL_memcpy(buf + len_multiple8, rand_buf, remainder);
  }

  return 1;
}

#else

int rdrand(uint8_t *buf, const size_t len) {
  return 0;
}

#endif

void override_entropy_source_method_FOR_TESTING(
  const struct entropy_source_methods *override_entropy_source_methods) {

  *allow_entropy_source_methods_override_bss_get() = 1;
  *entropy_source_methods_override_bss_get() = override_entropy_source_methods;
}
