// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include  <gtest/gtest.h>

#include <openssl/rand.h>

#include "internal.h"
#include "../test/ube_test.h"
#include "../test/test_util.h"

class ubeGenerationNumberTest : public::testing::Test {
  private:
    UbeBase ube_base_;

  protected:
    void SetUp() override {
      ube_base_.SetUp();
    }

    void TearDown() override {
      ube_base_.TearDown();
    }

    bool UbeIsSupported() const {
      return ube_base_.UbeIsSupported();
    }

    void allowMockedUbe() const {
      return ube_base_.allowMockedUbe();
    }
};

TEST_F(ubeGenerationNumberTest, BasicTests) {
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

static void MockedDetectionMethodTest(
  std::function<void(uint64_t)> set_method_generation_number) {

  uint64_t generation_number = 0;
  uint64_t cached_generation_number = 0;
  uint64_t mocked_generation_number = 0;

  uint8_t initial_mocked_generation_number[4] = {0};
  ASSERT_TRUE(RAND_bytes(initial_mocked_generation_number, 4));
  mocked_generation_number =
        ((uint64_t)initial_mocked_generation_number[0] << 24) |
        ((uint64_t)initial_mocked_generation_number[1] << 16) |
        ((uint64_t)initial_mocked_generation_number[2] << 8)  |
        ((uint64_t)initial_mocked_generation_number[3]);

  // Testing that UBE generation number is incremented when:
  //   mocked_generation_number + 1
  //   mocked_generation_number + 3
  //   mocked_generation_number - 1
  // Set our starting point and get initial UBE generation number
  set_method_generation_number(mocked_generation_number);
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));

  // Should be stable.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number);

  // Mock a UBE.
  set_method_generation_number(mocked_generation_number + 1);

  // UBE generation number should have incremented once.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number + 1);

  // Should be stable again.
  cached_generation_number = generation_number;
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, cached_generation_number);

  // Mock another UBE with higher increment.
  set_method_generation_number(mocked_generation_number + 3);

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

  // Mock another UBE but with a strictly smaller value.
  set_method_generation_number(mocked_generation_number - 1);

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

TEST_F(ubeGenerationNumberTest, MockedDetectionMethodTests) {

  allowMockedUbe();

  MockedDetectionMethodTest(
    [](uint64_t gn) {
      set_fork_ube_generation_number_FOR_TESTING(gn);
    }
  );

  MockedDetectionMethodTest(
    [](uint64_t gn) {
      set_vm_ube_generation_number_FOR_TESTING(gn);
    }
  );

  MockedDetectionMethodTest(
    [](uint64_t gn) {
      set_fork_ube_generation_number_FOR_TESTING(gn);
      set_vm_ube_generation_number_FOR_TESTING(gn);
    }
  );

  MockedDetectionMethodTest(
    [](uint64_t gn) {
      set_fork_ube_generation_number_FOR_TESTING(gn);
      set_vm_ube_generation_number_FOR_TESTING(gn + 1);
    }
  );
}

// Exercises the vm_ube generation number across the full 64-bit range. vmclock
// exposes a 64-bit vm_generation_counter (unlike the legacy 32-bit sysgenid),
// so the orchestration layer must detect changes in the high 32 bits and in
// values that exceed 2^32. |MockedDetectionMethodTest| above only covers a
// 32-bit-range value, so this guards the widening end-to-end.
TEST_F(ubeGenerationNumberTest, MockedVmUbe64BitValues) {
  allowMockedUbe();

  // A sequence of distinct 64-bit values. Consecutive entries differ only in
  // the high 32 bits, only in the low 32 bits, or wrap across the 2^32
  // boundary -- each transition must be detected as exactly one UBE.
  const uint64_t values[] = {
    0x0000000000000001ULL,
    0x0000000100000001ULL,  // high half changed, low half identical
    0x0000000100000002ULL,  // low half changed, high half identical
    0x00000000FFFFFFFFULL,  // drop below 2^32
    0x0000000100000000ULL,  // cross the 2^32 boundary
    0xFFFFFFFFFFFFFFFFULL,  // all bits set
    0x8000000000000000ULL,  // high bit only
  };

  uint64_t generation_number = 0;
  set_vm_ube_generation_number_FOR_TESTING(values[0]);
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));

  for (size_t i = 1; i < sizeof(values) / sizeof(values[0]); i++) {
    uint64_t before = generation_number;

    // Changing the mocked vm_ube generation number must bump the UBE
    // generation number exactly once.
    set_vm_ube_generation_number_FOR_TESTING(values[i]);
    generation_number = 0;
    ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
    ASSERT_EQ(generation_number, before + 1) << "at index " << i;

    // Stable when the value does not change.
    uint64_t stable = 0;
    ASSERT_TRUE(CRYPTO_get_ube_generation_number(&stable));
    ASSERT_EQ(stable, generation_number) << "instability at index " << i;
  }
}

// A change confined entirely to the high 32 bits of the vm_ube generation
// number must still be detected. A 32-bit-truncating implementation would miss
// this (both values alias to 0 in the low 32 bits) and fail to reseed.
TEST_F(ubeGenerationNumberTest, MockedVmUbeHighBitsOnlyChange) {
  allowMockedUbe();

  uint64_t generation_number = 0;
  set_vm_ube_generation_number_FOR_TESTING(0x0000000000000000ULL + 0x100000000ULL);
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));

  uint64_t before = generation_number;
  // Low 32 bits stay 0; only the high 32 bits differ.
  set_vm_ube_generation_number_FOR_TESTING(0x200000000ULL);
  generation_number = 0;
  ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  ASSERT_EQ(generation_number, before + 1);
}

TEST_F(ubeGenerationNumberTest, ExpectedSupportTests) {
  uint64_t generation_number = 0;
  // Operating systems where we expect UBE detection to be enabled.
  if (osIsAmazonLinux()) {
    ASSERT_TRUE(CRYPTO_get_ube_generation_number(&generation_number));
  }
}
