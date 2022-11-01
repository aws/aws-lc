/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0 OR ISC
------------------------------------------------------------------------------------
*/

#include <stdint.h>

#include <openssl/rand.h>

#include "pq_custom_randombytes.h"
#include "../fipsmodule/rand/internal.h"

// WARNING: THIS IMPLEMENTATION IS USED ONLY FOR TESTING PURPOSES.
//          DO NOT USE THESE APIS ON YOUR OWN.

static int use_deterministic_randombytes = 0;
static CTR_DRBG_STATE pq_custom_drbg_state;

static int *use_deterministic_randombytes_get(void) {
  return &use_deterministic_randombytes;
}

void pq_custom_randombytes_use_deterministic_for_testing(void) {
  *use_deterministic_randombytes_get() = 1;
}

static void pq_custom_drbg_init(const uint8_t *seed) {
  CTR_DRBG_init(&pq_custom_drbg_state, seed, NULL, 0);
}

static int pq_custom_drbg_bytes(uint8_t *out, size_t num_bytes) {
  return CTR_DRBG_generate(&pq_custom_drbg_state, out, num_bytes, NULL, 0);
}

void pq_custom_randombytes_init_for_testing(const uint8_t *seed) {
  if (*use_deterministic_randombytes_get() == 1) {
    pq_custom_drbg_init(seed);
  }
}

int pq_custom_randombytes(uint8_t *out, size_t num_bytes) {
  if (*use_deterministic_randombytes_get() == 1) {
    return pq_custom_drbg_bytes(out, num_bytes);
  } else {
    return RAND_bytes(out, num_bytes);
  }
}
