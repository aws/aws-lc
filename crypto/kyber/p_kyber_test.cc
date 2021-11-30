#include <gtest/gtest.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include "../crypto/evp_extra/internal.h"
#include "openssl/base.h"
#include "openssl/evp.h"

TEST(Kyber512Test, EVP_PKEY_keygen) {
  EVP_PKEY_CTX *kyber_pkey_ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_KYBER512, nullptr);
  ASSERT_NE(kyber_pkey_ctx, nullptr);

  EVP_PKEY *kyber_pkey = EVP_PKEY_new();
  ASSERT_NE(kyber_pkey, nullptr);

  EXPECT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx));
  EXPECT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx, &kyber_pkey));
  ASSERT_NE(kyber_pkey->pkey.ptr, nullptr);

  const KYBER_512_KEY *kyber512Key = (KYBER_512_KEY *)(kyber_pkey->pkey.ptr);
  EXPECT_TRUE(kyber512Key->has_private);

  uint8_t *buf = nullptr;
  size_t buf_size;
  EXPECT_TRUE(EVP_PKEY_get_raw_public_key(kyber_pkey, buf, &buf_size));
  EXPECT_EQ((size_t)KYBER512_PUBLICKEY_BYTES, buf_size);

  buf = (uint8_t *)OPENSSL_malloc(buf_size);
  ASSERT_NE(buf, nullptr);
  EXPECT_TRUE(EVP_PKEY_get_raw_public_key(kyber_pkey, buf, &buf_size));

  buf_size = 0;
  EXPECT_FALSE(EVP_PKEY_get_raw_public_key(kyber_pkey, buf, &buf_size));

  uint32_t err = ERR_get_error();
  EXPECT_EQ(ERR_LIB_EVP, ERR_GET_LIB(err));
  EXPECT_EQ(EVP_R_BUFFER_TOO_SMALL, ERR_GET_REASON(err));
  OPENSSL_free(buf);
  buf = nullptr;

  EXPECT_TRUE(EVP_PKEY_get_raw_private_key(kyber_pkey, buf, &buf_size));
  EXPECT_EQ((size_t)KYBER512_SECRETKEY_BYTES, buf_size);

  buf = (uint8_t *)OPENSSL_malloc(buf_size);
  ASSERT_NE(buf, nullptr);
  EXPECT_TRUE(EVP_PKEY_get_raw_private_key(kyber_pkey, buf, &buf_size));

  buf_size = 0;
  EXPECT_FALSE(EVP_PKEY_get_raw_private_key(kyber_pkey, buf, &buf_size));
  err = ERR_get_error();
  EXPECT_EQ(ERR_LIB_EVP, ERR_GET_LIB(err));
  EXPECT_EQ(EVP_R_BUFFER_TOO_SMALL, ERR_GET_REASON(err));
  OPENSSL_free(buf);

  EVP_PKEY_CTX_free(kyber_pkey_ctx);
}

TEST(Kyber512Test, EVP_PKEY_cmp) {
  EVP_PKEY_CTX *kyber_pkey_ctx1 = EVP_PKEY_CTX_new_id(EVP_PKEY_KYBER512, nullptr);
  ASSERT_NE(kyber_pkey_ctx1, nullptr);

  EVP_PKEY *kyber_pkey1 = EVP_PKEY_new();
  ASSERT_NE(kyber_pkey1, nullptr);

  EXPECT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx1));
  EXPECT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx1, &kyber_pkey1));
  ASSERT_NE(kyber_pkey1->pkey.ptr, nullptr);

  EVP_PKEY_CTX *kyber_pkey_ctx2 = EVP_PKEY_CTX_new_id(EVP_PKEY_KYBER512, nullptr);
  ASSERT_NE(kyber_pkey_ctx2, nullptr);

  EVP_PKEY *kyber_pkey2 = EVP_PKEY_new();
  ASSERT_NE(kyber_pkey2, nullptr);

  EXPECT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx2));
  EXPECT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx2, &kyber_pkey2));
  ASSERT_NE(kyber_pkey2->pkey.ptr, nullptr);

  EXPECT_EQ(0, EVP_PKEY_cmp(kyber_pkey1, kyber_pkey2));
  EXPECT_EQ(1, EVP_PKEY_cmp(kyber_pkey1, kyber_pkey1));
  EXPECT_EQ(1, EVP_PKEY_cmp(kyber_pkey2, kyber_pkey2));

  EVP_PKEY_CTX_free(kyber_pkey_ctx1);
  EVP_PKEY_CTX_free(kyber_pkey_ctx2);
}

