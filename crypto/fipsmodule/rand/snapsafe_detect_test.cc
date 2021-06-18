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
  // First part of this test suite generates two snapsafe generation numbers and
  // compares them. Since the generation should be stable it is expected the two
  // values are equal.
  // Second part of this test suite This test sets a new SysGenID value
  // (|new_sysgenid_value|), attempts to generate the snapsafe generation
  // number, and compares the new SysGenID value against the generation number
  // (|current_snapsafe_gen_num|). The expectation is that the two values are
  // equal.

  int snapsafe_detection_should_be_ignored = 0; // no

  if (getenv("AWSLC_IGNORE_SNAPSAFE")) {
    snapsafe_detection_should_be_ignored = 1; // yes
    CRYPTO_snapsafe_detect_ignore_for_testing();
  }

  setup_sysgenid_support();

  // Set initial sysgenid value, such that we can call
  // |CRYPTO_get_snapsafe_generation| below.
  ASSERT_TRUE(set_new_sysgenid_value(1));

  uint32_t first_gen_num_call = 0;
  const int first_call_status = CRYPTO_get_snapsafe_generation(&first_gen_num_call);
  if (first_call_status == 0) {
    // Returning 0 means that snapsafe is not supported. Verify this should
    // indeed be the case.
    EXPECT_EQ(snapsafe_detection_should_be_ignored, 1);
    fprintf(stderr, "Snapsafe tests should be ignored; skipping them.\n");
    return;
  }
  ASSERT_EQ(first_gen_num_call, (uint32_t) 1);

  // The snapsafe generation should be stable.
  uint32_t second_gen_num_call = 0;
  ASSERT_TRUE(CRYPTO_get_snapsafe_generation(&second_gen_num_call));
  ASSERT_EQ(first_gen_num_call, second_gen_num_call);

  uint32_t new_sysgenid_value = 1;
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
    new_sysgenid_value = test_sysgenid_values[i];
    ASSERT_TRUE(set_new_sysgenid_value(new_sysgenid_value));
    ASSERT_TRUE(CRYPTO_get_snapsafe_generation(&current_snapsafe_gen_num));
    ASSERT_EQ(new_sysgenid_value, current_snapsafe_gen_num);
  }
}

#endif // defined(OPENSSL_LINUX)
