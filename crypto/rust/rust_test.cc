// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <vector>

#include <gtest/gtest.h>

#include <openssl/err.h>

#include "../test/test_util.h"
#include "internal.h"

TEST(RustTest, ByteSum) {
  const uint8_t data[] = {1, 2, 3, 250};
  uint64_t sum = 0;
  ASSERT_TRUE(CRYPTO_rust_byte_sum(data, sizeof(data), &sum));
  EXPECT_EQ(sum, 256u);

  std::vector<uint8_t> large(4096, 0xff);
  ASSERT_TRUE(CRYPTO_rust_byte_sum(large.data(), large.size(), &sum));
  EXPECT_EQ(sum, 4096u * 0xff);
}

TEST(RustTest, ByteSumEmpty) {
  uint64_t sum = 1;
  ASSERT_TRUE(CRYPTO_rust_byte_sum(nullptr, 0, &sum));
  EXPECT_EQ(sum, 0u);
}

TEST(RustTest, ByteSumNull) {
  const uint8_t data[] = {1};
  uint64_t sum = 0;

  ERR_clear_error();
  EXPECT_FALSE(CRYPTO_rust_byte_sum(nullptr, 1, &sum));
  EXPECT_TRUE(ErrorEquals(ERR_get_error(), ERR_LIB_CRYPTO,
                          ERR_R_PASSED_NULL_PARAMETER));

  EXPECT_FALSE(CRYPTO_rust_byte_sum(data, sizeof(data), nullptr));
  EXPECT_TRUE(ErrorEquals(ERR_get_error(), ERR_LIB_CRYPTO,
                          ERR_R_PASSED_NULL_PARAMETER));
}
