// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include  <gtest/gtest.h>

#include "internal.h"
#include "../test/test_util.h"

class ubeTest : public ::testing::Test {
  public:
    void SetUp() override {
      uint64_t current_generation_number = 0;
      if (CRYPTO_get_ube_generation_number(&current_generation_number) == 1) {
        ube_detection_supported_ = true;
      }
    }

    void TearDown() override {
      disable_mocked_ube_detection_FOR_TESTING();
    }

  protected:
    bool UbeIsSupported(void) {
      return ube_detection_supported_;
    }

    void allowMockedUbe(void) {
      allow_mocked_ube_detection_FOR_TESTING();
    }

    bool ube_detection_supported_ = false;
};

TEST_F(ubeTest, BasicTests) {
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

TEST_F(ubeTest, MockedMethodTests) {

  allowMockedUbe();

  uint64_t generation_number = 0;
  uint64_t cached_generation_number = 0;

  // First test incrementing the fork generation number. Pick a starting point
  // and get initial UBE generation number
  set_fork_generation_number_FOR_TESTING(10);
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));

  // Should be stable again.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number);

  // Mock a process fork. We used 10 before. Hence, 11 should work.
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

  // Mock another process fork with higher increment.
  set_fork_generation_number_FOR_TESTING(13);

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

  // Mock another fork event but with a strictly smaller value.
  set_snapsafe_generation_number_FOR_TESTING(5);

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

  // Now test incrementing the snapsafe generation number. Before we used 10 as
  // the default value, use a smaller number now, say 5.
  set_snapsafe_generation_number_FOR_TESTING(5);
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));

  // Should be stable.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number);

  // Mock a snapsafe event. We used 5 before. Hence, 6 should work.
  set_snapsafe_generation_number_FOR_TESTING(6);

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

  // Mock another snapsafe event with higher increment.
  set_snapsafe_generation_number_FOR_TESTING(8);

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

  // Mock another snapsafe event but with a strictly smaller value.
  set_snapsafe_generation_number_FOR_TESTING(1);

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
  set_fork_generation_number_FOR_TESTING(20);
  set_snapsafe_generation_number_FOR_TESTING(20);
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));

  // And that it's now stable.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number);

  // Increment both, this time using higher increments than 1 and different
  // increment values.
  set_fork_generation_number_FOR_TESTING(24);
  set_snapsafe_generation_number_FOR_TESTING(23);

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

  // Try strictly smaller values. These are values previously used as fork and
  // snapsafe generation number. It should still result in a UBE generation
  // number increment.
  set_fork_generation_number_FOR_TESTING(1);
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
}

TEST_F(ubeTest, ExpectedSupportTests) {
  uint64_t generation_number = 0;
  // Operating systems where we expect UBE detection to be enabled.
  if (osIsAmazonLinux()) {
    ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  }
}
