/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0
------------------------------------------------------------------------------------
*/

#include <gtest/gtest.h>
#include <openssl/evp.h>
#include <vector>
#include "../fipsmodule/evp/internal.h"
#include "../kyber/kem_kyber.h"
#include "../test/file_test.h"
#include "../test/test_util.h"
#include "../rand_extra/pq_custom_randombytes.h"
#include "./internal.h"

static void RunTest(FileTest *t)
{
  std::string count;
  std::vector<uint8_t> seed, pk, sk, ct, ss;

  size_t shared_secret_len = KYBER512_SHARED_SECRET_BYTES;
  size_t ciphertext_len = KYBER512_CIPHERTEXT_BYTES;
  uint8_t shared_secret[KYBER512_SHARED_SECRET_BYTES];
  uint8_t ciphertext[KYBER512_CIPHERTEXT_BYTES];

  ASSERT_TRUE(t->GetAttribute(&count, "count"));
  ASSERT_TRUE(t->GetBytes(&seed, "seed"));
  ASSERT_TRUE(t->GetBytes(&pk, "pk"));
  ASSERT_TRUE(t->GetBytes(&sk, "sk"));
  ASSERT_TRUE(t->GetBytes(&ct, "ct"));
  ASSERT_TRUE(t->GetBytes(&ss, "ss"));

  pq_custom_randombytes_use_deterministic_for_testing();
  pq_custom_randombytes_init_for_testing(seed.data());

  EVP_PKEY_CTX *kyber_pkey_ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_KYBER512, nullptr);
  ASSERT_NE(kyber_pkey_ctx, nullptr);

  EVP_PKEY *kyber_pkey = EVP_PKEY_new();
  ASSERT_NE(kyber_pkey, nullptr);

  EXPECT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx));
  EXPECT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx, &kyber_pkey));
  const KYBER512_KEY *kyber512Key = (KYBER512_KEY *)(kyber_pkey->pkey.ptr);
  EXPECT_EQ(Bytes(pk),
            Bytes(kyber512Key->pub, KYBER512_PUBLIC_KEY_BYTES));
  EXPECT_EQ(Bytes(sk),
            Bytes(kyber512Key->priv, KYBER512_SECRET_KEY_BYTES));

  ASSERT_TRUE(EVP_PKEY_encapsulate(kyber_pkey_ctx, ciphertext, &ciphertext_len, shared_secret, &shared_secret_len));
  EXPECT_EQ(Bytes(ct),
            Bytes(ciphertext, KYBER512_CIPHERTEXT_BYTES));

  ASSERT_TRUE(EVP_PKEY_decapsulate(kyber_pkey_ctx, shared_secret, &shared_secret_len, ciphertext, ciphertext_len));
  EXPECT_EQ(Bytes(ss),
            Bytes(shared_secret, KYBER512_SHARED_SECRET_BYTES));

  EVP_PKEY_CTX_free(kyber_pkey_ctx);
}

TEST(Kyber512Test, KAT) {
 FileTestGTest("crypto/evp_extra/pq_kem_kat_tests_kyber512.txt", RunTest);
}
