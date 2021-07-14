// -----------------------------------------------------------------------------
// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// -----------------------------------------------------------------------------

#include <openssl/base.h>

#if defined(OPENSSL_LINUX)

#include "snapsafe_detect.h"
#include "../../test/sysgenid_test_util.h"

#include <gtest/gtest.h>

#define NUMBER_OF_TEST_VALUES 5

// Make sure to tidy up if we mock the SysGenID device.
class SnapsafeGenerationTest : public testing::Test {
  public:
    void TearDown() override {
      maybe_cleanup();
    }
};

TEST_F(SnapsafeGenerationTest, SysGenIDretrieval) {
  // This test uses the mocked SysGenID test to be able to control the SysGenID
  // value. The real SysGenID device cannot be "rolled-back" and will always
  // strictly increment.
  // First part of this test fixture generates two snapsafe generation numbers
  // and compares them. Since the generation should be stable it is expected the
  // two values are equal.
  // Second part of this test fixture sets a new SysGenID value
  // (|new_sysgenid_value|), attempts to generate the snapsafe generation
  // number, and compares the new SysGenID value against the generation number
  // (|current_snapsafe_gen_num|). The expectation is that the two values are
  // equal.

  setup_sysgenid_support(MUST_BE_MOCKED);

  // Verify setting value works.
  uint32_t snapsafe_generation_set = 0;
  ASSERT_TRUE(new_sysgenid_value(1));
  ASSERT_TRUE(CRYPTO_get_snapsafe_generation(&snapsafe_generation_set));
  ASSERT_EQ(snapsafe_generation_set, (uint32_t) 1);

  // The snapsafe generation should be stable.
  uint32_t snapsafe_generation_stable = 0;
  ASSERT_TRUE(CRYPTO_get_snapsafe_generation(&snapsafe_generation_stable));
  ASSERT_EQ(snapsafe_generation_stable, snapsafe_generation_set);

  uint32_t new_sysgenid_value_hint = 1;
  uint32_t current_snapsafe_gen_num = 0;
  uint32_t test_sysgenid_values[NUMBER_OF_TEST_VALUES] = {
    0x03, // 2^0 + 2
    0x103, // 2^8 + 3
    0x10004, // 2^16 + 4
    0x1000005, // 2^24 + 5
    0xFFFFFFFF // 2^32 - 1
  };

  for (size_t i = 0; i < NUMBER_OF_TEST_VALUES; i++) {
    // Exercise all bytes of the 32-bit generation number.
    new_sysgenid_value_hint = test_sysgenid_values[i];
    ASSERT_TRUE(new_sysgenid_value(new_sysgenid_value_hint));
    ASSERT_TRUE(CRYPTO_get_snapsafe_generation(&current_snapsafe_gen_num));
    ASSERT_EQ(new_sysgenid_value_hint, current_snapsafe_gen_num);
  }
}

#endif // defined(OPENSSL_LINUX)
