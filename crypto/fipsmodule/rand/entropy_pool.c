// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "internal.h"
#include "../../internal.h"

#if defined(AWSLC_FIPS)

// entropy_pool_validate_static_assumptions validates static assumptions on the
// entropy pool |entropy_pool|.
static int entropy_pool_validate_static_assumptions(
  struct entropy_pool *entropy_pool) {
  // By transitivity, |valid_available| and |index_read| are verified to be at
  // most |ENTROPY_POOL_SIZE|.
  if (entropy_pool->capacity > ENTROPY_POOL_SIZE ||
      entropy_pool->valid_available > entropy_pool->capacity ||
      entropy_pool->index_read > entropy_pool->capacity) {
    return 0;
  }
  return 1;
}

// entropy_pool_ensure_can_satisfy returns 1 if the entropy pool |entropy_pool|
// contains enough entropy to satisfy a get request of size |get_size|.
// Returns 0 otherwise - meaning that the entropy pool needs more entropy.
static int entropy_pool_ensure_can_satisfy(struct entropy_pool *entropy_pool,
  size_t get_size) {
  if (entropy_pool->valid_available < get_size) {
    return 0;
  }
  return 1;
}

static int entropy_pool_consume(struct entropy_pool *entropy_pool,
  uint8_t *get_buffer, size_t get_size) {

  if ((entropy_pool->index_read + get_size) > entropy_pool->capacity) {
    return 0;
  }

  OPENSSL_memcpy(get_buffer, entropy_pool->pool + entropy_pool->index_read,
    get_size);

  OPENSSL_cleanse(entropy_pool->pool + entropy_pool->index_read, get_size);
  entropy_pool->index_read = entropy_pool->index_read + get_size;
  entropy_pool->valid_available = entropy_pool->valid_available - get_size;

  return 1;
}

void RAND_entropy_pool_init(struct entropy_pool *entropy_pool) {
  RAND_entropy_pool_zeroize(entropy_pool);
  entropy_pool->capacity = ENTROPY_POOL_SIZE;
}

void RAND_entropy_pool_zeroize(struct entropy_pool *entropy_pool) {
  if (entropy_pool == NULL) {
    return;
  }

  OPENSSL_cleanse(entropy_pool->pool, ENTROPY_POOL_SIZE);
  OPENSSL_cleanse(entropy_pool, sizeof(struct entropy_pool));
}

int RAND_entropy_pool_add(struct entropy_pool *entropy_pool,
  uint8_t add_buffer[ENTROPY_POOL_SIZE]) {

  // An explicit (and simplifying) assumption is that the entire pool is
  // written with fresh entropy, every time.
  if (entropy_pool == NULL ||
      entropy_pool->capacity != ENTROPY_POOL_SIZE) {
    return 0;
  }

  OPENSSL_memcpy(entropy_pool->pool, add_buffer, ENTROPY_POOL_SIZE);
  entropy_pool->index_read = 0;
  entropy_pool->valid_available = ENTROPY_POOL_SIZE;

  return 1;
}

int RAND_entropy_pool_get(struct entropy_pool *entropy_pool,
  uint8_t *get_buffer, size_t get_size) {

  // Doesn't support requests bigger than the total size of the pool or zero.
  if (entropy_pool == NULL ||
      get_buffer == NULL ||
      get_size == 0 ||
      get_size > entropy_pool->capacity) {
    return 0;
  }

  if (entropy_pool_validate_static_assumptions(entropy_pool) != 1) {
    return 0;
  }

  if (entropy_pool_ensure_can_satisfy(entropy_pool, get_size) != 1) {
    // Out-side module call
    // Could create a soft-lock in the struct here
    RAND_module_entropy_depleted();
    // And then unlock struct here
    if (entropy_pool_ensure_can_satisfy(entropy_pool, get_size) != 1) {
      return 0;
    }
  }

  // Can't reach this point without entropy pool having enough entropy to
  // satisfy the request size.
  if (entropy_pool_consume(entropy_pool, get_buffer, get_size) != 1) {
    return 0;
  }

  return 1;
}

#endif // defined(AWSLC_FIPS)
