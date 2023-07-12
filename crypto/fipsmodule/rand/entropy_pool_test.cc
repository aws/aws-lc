// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "internal.h"

#include <gtest/gtest.h>

#if defined(AWSLC_FIPS)

// For standalone entropy pool tests, we add entropy through
// RAND_entropy_pool_add(). The reason is that if a valid RAND_entropy_pool_get()
// request cannot be satisfied, the "depleted" workflow will add entropy to the
// thread-local entropy pool, not the locally initialized pool in the standalone
// tests below.

const size_t entropy_pool_size_halfed = ENTROPY_POOL_SIZE / 2;
const uint8_t zero_entropy_pool[ENTROPY_POOL_SIZE] = {0};

static void fill_fake_entropy(uint8_t fake_entropy_buffer[ENTROPY_POOL_SIZE],
  char ch);
static void fill_fake_entropy(uint8_t fake_entropy_buffer[ENTROPY_POOL_SIZE],
  char ch) {
  for (size_t i = 0; i < ENTROPY_POOL_SIZE; i++) {
    fake_entropy_buffer[i] = ch;
  }
}

TEST(EntropyPool, BasicFlow) {
  uint8_t entropy_buffer[ENTROPY_POOL_SIZE] = {0};
  struct entropy_pool entropy_pool;
  uint8_t fake_entropy[ENTROPY_POOL_SIZE] = {0};
  fill_fake_entropy(fake_entropy, 'A');

  // Initially, the capacity should have value |ENTROPY_POOL_SIZE|. Rest of the
  // object should be zeroized.
  RAND_entropy_pool_init(&entropy_pool);
  EXPECT_EQ(entropy_pool.capacity, (size_t) ENTROPY_POOL_SIZE);
  EXPECT_EQ(entropy_pool.valid_available, (size_t) 0);
  EXPECT_EQ(entropy_pool.index_read, (size_t) 0);
  EXPECT_EQ(OPENSSL_memcmp(entropy_pool.pool, zero_entropy_pool, ENTROPY_POOL_SIZE), 0);

  // After adding entropy to the pool, expect the number of valid bytes to
  // match the amount added.
  RAND_entropy_pool_add(&entropy_pool, fake_entropy);
  EXPECT_EQ(entropy_pool.capacity, (size_t) ENTROPY_POOL_SIZE);
  EXPECT_EQ(entropy_pool.valid_available, (size_t) ENTROPY_POOL_SIZE);
  EXPECT_EQ(entropy_pool.index_read, (size_t) 0);
  EXPECT_EQ(OPENSSL_memcmp(entropy_pool.pool, fake_entropy, ENTROPY_POOL_SIZE), 0);

  // Consuming the entire pool. Expect the valid available bytes to be zero
  // and read pointer to be incremented by the consumed amount.
  EXPECT_TRUE(RAND_entropy_pool_get(&entropy_pool, entropy_buffer, ENTROPY_POOL_SIZE));
  EXPECT_EQ(entropy_pool.capacity, (size_t) ENTROPY_POOL_SIZE);
  EXPECT_EQ(entropy_pool.valid_available, (size_t) 0);
  EXPECT_EQ(entropy_pool.index_read, (size_t) ENTROPY_POOL_SIZE);
  EXPECT_EQ(OPENSSL_memcmp(entropy_pool.pool, zero_entropy_pool, ENTROPY_POOL_SIZE), 0);

  RAND_entropy_pool_zeroize(&entropy_pool);
  EXPECT_EQ(entropy_pool.capacity, (size_t) 0);
  EXPECT_EQ(entropy_pool.valid_available, (size_t) 0);
  EXPECT_EQ(entropy_pool.index_read, (size_t) 0);
  EXPECT_EQ(OPENSSL_memcmp(entropy_pool.pool, zero_entropy_pool, ENTROPY_POOL_SIZE), 0);

  // Initialize again but now consume a total of |ENTROPY_POOL_SIZE| bytes of
  // entropy over two get invocations.
  RAND_entropy_pool_init(&entropy_pool);
  RAND_entropy_pool_add(&entropy_pool, fake_entropy);

  EXPECT_TRUE(RAND_entropy_pool_get(&entropy_pool, entropy_buffer, entropy_pool_size_halfed));
  EXPECT_EQ(entropy_pool.capacity, (size_t) ENTROPY_POOL_SIZE);
  EXPECT_EQ(entropy_pool.valid_available, (size_t) entropy_pool_size_halfed);
  EXPECT_EQ(entropy_pool.index_read, (size_t) entropy_pool_size_halfed);
  // Should have zeroized first half of pool.
  EXPECT_EQ(OPENSSL_memcmp(entropy_pool.pool, zero_entropy_pool, entropy_pool_size_halfed), 0);

  EXPECT_TRUE(RAND_entropy_pool_get(&entropy_pool, entropy_buffer, entropy_pool_size_halfed));
  EXPECT_EQ(entropy_pool.capacity, (size_t) ENTROPY_POOL_SIZE);
  EXPECT_EQ(entropy_pool.valid_available, (size_t) 0);
  EXPECT_EQ(entropy_pool.index_read, (size_t) ENTROPY_POOL_SIZE);
  // Entire pool must now be zeroized.
  EXPECT_EQ(OPENSSL_memcmp(entropy_pool.pool, zero_entropy_pool, ENTROPY_POOL_SIZE), 0);
}

TEST(EntropyPool, BasicFailure) {
  uint8_t entropy_buffer[ENTROPY_POOL_SIZE] = {0};
  struct entropy_pool entropy_pool;
  uint8_t fake_entropy[ENTROPY_POOL_SIZE] = {0};
  fill_fake_entropy(fake_entropy, 'A');

  RAND_entropy_pool_init(&entropy_pool);
  RAND_entropy_pool_add(&entropy_pool, fake_entropy);

  // Input validation. Cannot:
  //  * Consume strictly more than |ENTROPY_POOL_SIZE| bytes per invocation.
  //  * Consume zero bytes.
  //  * Use NULL as argument for entropy pool.
  //  * Use NULL as argument for output buffer.
  EXPECT_FALSE(RAND_entropy_pool_get(&entropy_pool, entropy_buffer, ENTROPY_POOL_SIZE+1));
  EXPECT_FALSE(RAND_entropy_pool_get(&entropy_pool, entropy_buffer, 0));
  EXPECT_FALSE(RAND_entropy_pool_get(NULL, entropy_buffer, ENTROPY_POOL_SIZE));
  EXPECT_FALSE(RAND_entropy_pool_get(&entropy_pool, NULL, ENTROPY_POOL_SIZE));

  // Modify internal state to capture validations
  RAND_entropy_pool_add(&entropy_pool, fake_entropy);
  entropy_pool.capacity = ENTROPY_POOL_SIZE + 1;
  EXPECT_FALSE(RAND_entropy_pool_get(&entropy_pool, entropy_buffer, ENTROPY_POOL_SIZE));
  entropy_pool.capacity = ENTROPY_POOL_SIZE;
  EXPECT_TRUE(RAND_entropy_pool_get(&entropy_pool, entropy_buffer, ENTROPY_POOL_SIZE));

  RAND_entropy_pool_add(&entropy_pool, fake_entropy);
  entropy_pool.valid_available = ENTROPY_POOL_SIZE + 1;
  EXPECT_FALSE(RAND_entropy_pool_get(&entropy_pool, entropy_buffer, ENTROPY_POOL_SIZE));
  entropy_pool.valid_available = ENTROPY_POOL_SIZE;
  EXPECT_TRUE(RAND_entropy_pool_get(&entropy_pool, entropy_buffer, ENTROPY_POOL_SIZE));

  RAND_entropy_pool_add(&entropy_pool, fake_entropy);
  entropy_pool.index_read = ENTROPY_POOL_SIZE + 1;
  EXPECT_FALSE(RAND_entropy_pool_get(&entropy_pool, entropy_buffer, ENTROPY_POOL_SIZE));
  entropy_pool.index_read = 0;
  EXPECT_TRUE(RAND_entropy_pool_get(&entropy_pool, entropy_buffer, ENTROPY_POOL_SIZE));
}

TEST(EntropyPool, EntirePoolRefreshedAtAddTime) {
  uint8_t entropy_buffer[ENTROPY_POOL_SIZE] = {0};
  struct entropy_pool entropy_pool;
  uint8_t fake_entropy_A[ENTROPY_POOL_SIZE] = {0};
  fill_fake_entropy(fake_entropy_A, 'A');
  uint8_t fake_entropy_B[ENTROPY_POOL_SIZE] = {0};
  fill_fake_entropy(fake_entropy_B, 'B');

  // Even though there is still valid available entropy in the pool, the entire
  // pool must be refreshed when adding fresh entropy.
  RAND_entropy_pool_init(&entropy_pool);
  RAND_entropy_pool_add(&entropy_pool, fake_entropy_A);
  EXPECT_TRUE(RAND_entropy_pool_get(&entropy_pool, entropy_buffer, entropy_pool_size_halfed));
  EXPECT_GT(entropy_pool.valid_available, (size_t) 0);
  RAND_entropy_pool_add(&entropy_pool, fake_entropy_B);
  EXPECT_EQ(OPENSSL_memcmp(entropy_pool.pool, fake_entropy_B, ENTROPY_POOL_SIZE), 0);

  // If adding entropy twice in a row, entire pool should be refreshed even
  // though no entropy has been consumed (extra check for the special case of
  // previous unit test).
  RAND_entropy_pool_zeroize(&entropy_pool);
  RAND_entropy_pool_init(&entropy_pool);
  RAND_entropy_pool_add(&entropy_pool, fake_entropy_A);
  EXPECT_EQ(entropy_pool.valid_available, (size_t) ENTROPY_POOL_SIZE);
  EXPECT_EQ(OPENSSL_memcmp(entropy_pool.pool, fake_entropy_A, ENTROPY_POOL_SIZE), 0);
  RAND_entropy_pool_add(&entropy_pool, fake_entropy_B);
  EXPECT_EQ(entropy_pool.valid_available, (size_t) ENTROPY_POOL_SIZE);
  EXPECT_EQ(OPENSSL_memcmp(entropy_pool.pool, fake_entropy_B, ENTROPY_POOL_SIZE), 0);

  // If adding entropy twice in a row, entire pool should be refreshed even
  // though all entropy had been consumed.
  RAND_entropy_pool_zeroize(&entropy_pool);
  RAND_entropy_pool_init(&entropy_pool);
  RAND_entropy_pool_add(&entropy_pool, fake_entropy_A);
  EXPECT_EQ(entropy_pool.valid_available, (size_t) ENTROPY_POOL_SIZE);
  EXPECT_TRUE(RAND_entropy_pool_get(&entropy_pool, entropy_buffer, ENTROPY_POOL_SIZE));
  EXPECT_EQ(entropy_pool.valid_available, (size_t) 0);
  RAND_entropy_pool_add(&entropy_pool, fake_entropy_A);
  EXPECT_EQ(entropy_pool.valid_available, (size_t) ENTROPY_POOL_SIZE);
  RAND_entropy_pool_add(&entropy_pool, fake_entropy_B);
  EXPECT_EQ(entropy_pool.valid_available, (size_t) ENTROPY_POOL_SIZE);
  EXPECT_EQ(OPENSSL_memcmp(entropy_pool.pool, fake_entropy_B, ENTROPY_POOL_SIZE), 0);
}

#endif
