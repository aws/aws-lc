// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include  <gtest/gtest.h>

#include "internal.h"
#include "../test/test_util.h"

TEST(Ube, BasicTests) {
  uint64_t generation_number = 0;
  if (CRYPTO_get_ube_generation_number(&generation_number) == 0) {
    // In this case, UBE detection is disabled, so just return
    // successfully. This should be a persistent state; check that.
    ASSERT_FALSE(CRYPTO_get_ube_generation_number(&generation_number));
    return;
  }

  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));

  // Check stability.
  uint64_t current_generation_number = generation_number + 1;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&current_generation_number));
  ASSERT_EQ(current_generation_number, generation_number);

  // Check stability again.
  current_generation_number = generation_number + 2;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&current_generation_number));
  ASSERT_EQ(current_generation_number, generation_number);
}

TEST(Ube, MockedMethodTests) {
  uint64_t generation_number = 0;
  uint64_t cached_generation_number = 0;
  if (CRYPTO_get_ube_generation_number(&generation_number) == 0) {
    // In this case, UBE detection is disabled, so just return
    // successfully. The short-circuit feature means we can't mock detection
    // methods.
    return;
  }

  // The fork generation number is initially 1. Use 10 because it's larger...
  // Configuring specific values must change later on, since we might have tests
  // running concurrently.
  set_fork_generation_number_FOR_TESTING(10);

  // Generation number should have incremented once.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number + 1);

  // Should be stable again.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number);

  // Mock another process fork. We used 10 before. Hence, 11 should work.
  set_fork_generation_number_FOR_TESTING(11);

  // Generation number should have incremented once.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number + 1);

  // Should be stable again.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number);

  // The snapsafe generation number is initially 1. Again use 10.
  set_snapsafe_generation_number_FOR_TESTING(10);

  // Generation number should have incremented once.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number + 1);

  // Should be stable again.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number);

  // Mock another snapsafe event. We used 10 before. Hence, 11 should work.
  set_snapsafe_generation_number_FOR_TESTING(11);

  // Generation number should have incremented once.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number + 1);

  // Should be stable again.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number);

  // Now try to increment both fork and snapsafe generation numbers. We expect
  // to see one increment in the ube generation number and then stability.
  set_snapsafe_generation_number_FOR_TESTING(20);
  set_fork_generation_number_FOR_TESTING(20);

  // Check that ube generation number incremented once.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number + 1);

  // And that it's now stable.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number);
}

TEST(Ube, ExpectedSupportTests) {
  uint64_t generation_number = 0;
  // Operating systems where we expect UBE detection to be enabled.
  if (osIsAmazonLinux()) {
    ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  }
}
