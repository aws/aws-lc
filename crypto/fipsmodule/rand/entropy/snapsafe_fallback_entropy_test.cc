// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/rand.h>

#include "internal.h"

#include <gtest/gtest.h>

#include <openssl/span.h>

#include "../../../test/test_util.h"

// This test is, strictly speaking, flaky, but we use large enough buffers
// (48 bytes) that the probability of failing when we should pass is negligible.

TEST(SnapsafeFallbackTest, NotObviouslyBroken) {
  static const uint8_t kZeros[CTR_DRBG_ENTROPY_LEN] = {0};

  uint8_t seed1[CTR_DRBG_ENTROPY_LEN];
  uint8_t seed2[CTR_DRBG_ENTROPY_LEN];

  struct entropy_source_t entropy_source = {0, 0};

  ASSERT_TRUE(snapsafe_fallback_initialize(&entropy_source));
  ASSERT_TRUE(snapsafe_fallback_get_seed(&entropy_source, seed1));
  ASSERT_TRUE(snapsafe_fallback_get_seed(&entropy_source, seed2));

  EXPECT_NE(Bytes(seed1), Bytes(seed2));
  EXPECT_NE(Bytes(seed1), Bytes(kZeros));
  EXPECT_NE(Bytes(seed2), Bytes(kZeros));

  uint8_t seed3[CTR_DRBG_ENTROPY_LEN];
  // Ensure that the implementation is not simply returning the memory unchanged.
  memcpy(seed3, seed1, CTR_DRBG_ENTROPY_LEN);
  ASSERT_TRUE(snapsafe_fallback_get_seed(&entropy_source, seed1));
  EXPECT_NE(Bytes(seed1), Bytes(seed3));
}
