// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include "internal.h"

#define MAX_EXTRACT_FROM_RNG (8*16)

// In the future this test can be improved by being able to predict whether the
// test is running on hardware that we expect to support RNDR. This will require
// amending the CI with such information.
// For now, simply ensure we exercise all code-paths in the CRYPTO_rndr
// implementation.
TEST(EntropySupport, Aarch64) {
#if !defined(OPENSSL_AARCH64)
  ASSERT_FALSE(have_hw_rng_aarch64_for_testing());
#else
  uint8_t buf[MAX_EXTRACT_FROM_RNG] = { 0 } ;
  if (have_hw_rng_aarch64_for_testing() == 1) {
    // Extracting 0 bytes is not supported.
    ASSERT_FALSE(rndr(buf, 0));

    for (size_t i = 1; i < MAX_EXTRACT_FROM_RNG; i++) {
      ASSERT_TRUE(rndr(buf, i));
    }
  }
#endif
}
