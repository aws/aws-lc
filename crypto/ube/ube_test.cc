// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include  <gtest/gtest.h>

#include "internal.h"

TEST(Ube, BasicTests) {
  uint64_t generation_number = 0;
  ASSERT_TRUE(get_ube_generation_number(&generation_number));

  // Check stability.
  uint64_t current_generation_number = generation_number + 1;
  ASSERT_TRUE(get_ube_generation_number(&current_generation_number));
  ASSERT_EQ(current_generation_number, generation_number);

  // Check stability again.
  current_generation_number = generation_number + 2;
  ASSERT_TRUE(get_ube_generation_number(&current_generation_number));
  ASSERT_EQ(current_generation_number, generation_number);
}

TEST(Ube, MockedMethodTests) {
  uint64_t generation_number = 0;
  uint64_t cached_generation_number = 0;
  if (get_ube_generation_number(&generation_number) == 0) {
    // In this case, UBE detection is disabled, so just return
    // successfully. The short-circuit feature means we can't mock detection
    // methods.
    return;
  }

  // The fork generation number is initially 1. Add a larger offset to avoid
  // any noise. 
  set_fork_generation_number_FOR_TESTING(10);

  // Generation number should have incremented once.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number + 1);

  // Should be stable again.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number);

  // Mock another process fork. We used 10 before. Hence, 11 should work.
  set_fork_generation_number_FOR_TESTING(11);

  // Generation number should have incremented once.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number + 1);

  // Should be stable again.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number);

  // The snapsafe generation number is initially 1. Add a larger offset to avoid
  // any noise. 
  set_snapsafe_generation_number_FOR_TESTING(10);

  // Generation number should have incremented once.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number + 1);

  // Should be stable again.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number);

  // Mock another snapsafe event. We used 10 before. Hence, 11 should work.
  set_snapsafe_generation_number_FOR_TESTING(11);

  // Generation number should have incremented once.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number + 1);

  // Should be stable again.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number);
}
