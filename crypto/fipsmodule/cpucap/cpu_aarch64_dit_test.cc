// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/crypto.h>
#include <gtest/gtest.h>

#include "internal.h"

#if defined(OPENSSL_AARCH64) && !defined(OPENSSL_STATIC_ARMCAP) && \
    !defined(OPENSSL_WINDOWS)

#if defined(ENABLE_AUTO_SET_RESET_DIT)
static void NestedMacroInvocation(uint64_t one) {
  SET_DIT_AUTO_RESET;
  uint64_t current_dit = armv8_get_dit();
  EXPECT_EQ(current_dit, one);
}
#endif // ENABLE_AUTO_SET_RESET_DIT

TEST(DITTest, SetReset) {
  uint64_t one = CRYPTO_is_ARMv8_DIT_capable_for_testing()? (uint64_t)1 : (uint64_t)0;

  uint64_t original_dit = 0, original_dit_2 = 0,
    current_dit = 0;
  original_dit = armv8_set_dit();
  EXPECT_EQ(original_dit, (uint64_t)0);

  // the case of a nested call of setting DIT
  original_dit_2 = armv8_set_dit();
  EXPECT_EQ(original_dit_2, one);

  current_dit = armv8_get_dit();
  EXPECT_EQ(current_dit, one);

  armv8_restore_dit(&original_dit);
  current_dit = armv8_get_dit();
  EXPECT_EQ(current_dit, (uint64_t)0);

#if defined(ENABLE_AUTO_SET_RESET_DIT)
  { // invoke the macro within a scope
    // to test that it restores the CPU DIT flag at the end
    SET_DIT_AUTO_RESET;
    current_dit = armv8_get_dit();
    EXPECT_EQ(current_dit, one);
    // Nested macro invocation will exit the scope leaving DIT = 1
    NestedMacroInvocation(one);
    current_dit = armv8_get_dit();
    EXPECT_EQ(current_dit, one);
  }
  current_dit = armv8_get_dit();
  EXPECT_EQ(current_dit, (uint64_t)0);
#endif // ENABLE_AUTO_SET_RESET_DIT
}

#endif  // OPENSSL_AARCH64 && !OPENSSL_STATIC_ARMCAP && !OPENSSL_WINDOWS
