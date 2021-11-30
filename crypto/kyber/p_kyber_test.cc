#include <gtest/gtest.h>

#include "openssl/base.h"
#include "openssl/evp.h"
#include "../crypto/evp_extra/internal.h"

TEST(Kyber512Test, EVP_keygen) {
  EVP_PKEY_CTX *kyber_pkey_ctx =
      EVP_PKEY_CTX_new_id(EVP_PKEY_KYBER512, NULL);
  EXPECT_NE(kyber_pkey_ctx, nullptr);

  EVP_PKEY *kyber_pkey = EVP_PKEY_new();
  EXPECT_NE(kyber_pkey, nullptr);

  ASSERT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx));
  ASSERT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx, &kyber_pkey));
  EXPECT_NE(kyber_pkey->pkey.ptr, nullptr);

  const KYBER_512_KEY *kyber512Key = (KYBER_512_KEY *)(kyber_pkey->pkey.ptr);
  ASSERT_TRUE(kyber512Key->has_private);

  EVP_PKEY_CTX_free(kyber_pkey_ctx);
}
