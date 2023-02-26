#include <gtest/gtest.h>
#include <openssl/mem.h>

#define KYBER_K 4 /* Needed for proper macro expansion */
#include "pqcrystals_kyber_ref_common/verify.h"

/*
 * This test is needed because the verify function has been modified from the
 * original Kyber reference code and we want to ensure the proper behavior is
 * maintained.
 */
TEST(KyberRefTest, verify) {
  uint8_t buf_len = 32;
  uint8_t *buf_a = (uint8_t *)OPENSSL_malloc(buf_len);
  ASSERT_NE(buf_a, nullptr);
  uint8_t *buf_b = (uint8_t *)OPENSSL_malloc(buf_len);
  ASSERT_NE(buf_b, nullptr);

  /* verify should return 0 when the buffers are equal */
  for (uint8_t i = 0; i < buf_len; i++) {
    buf_a[i] = i;
    buf_b[i] = i;
  }
  EXPECT_EQ(verify(buf_a, buf_b, buf_len), 0);

  /* verify should return 1 when the buffers differ */
  for (uint8_t i = 0; i < buf_len; i++) {
    buf_a[i] = i;
    buf_b[i] = i+1;
  }
  EXPECT_EQ(verify(buf_a, buf_b, buf_len), 1);

  OPENSSL_free(buf_a);
  OPENSSL_free(buf_b);
}
