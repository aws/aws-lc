#include <stdlib.h>
#include <string.h>

#include <string>
#include <vector>

#include <gtest/gtest.h>

#include <openssl/randombytes.h>
#include <openssl/pq_kem.h>

#include "../test/file_test.h"
#include "../test/test_util.h"
#include "./internal.h"

static void RunTest(FileTest *t)
{
  std::string count;
  std::vector<uint8_t> seed, pk, sk, ct, ss;
  ASSERT_TRUE(t->GetAttribute(&count, "count"));
  ASSERT_TRUE(t->GetBytes(&seed, "seed"));
  ASSERT_TRUE(t->GetBytes(&pk, "pk"));
  ASSERT_TRUE(t->GetBytes(&sk, "sk"));
  ASSERT_TRUE(t->GetBytes(&ct, "ct"));
  ASSERT_TRUE(t->GetBytes(&ss, "ss"));

  //Seed the DRNG
  randombytes_init(seed.data(), 48);

  const EVP_PQ_KEM *kyber_kem = &EVP_PQ_KEM_kyber512;
  EXPECT_NE(kyber_kem, nullptr);

  EVP_PQ_KEM_CTX *ctx = EVP_PQ_KEM_CTX_new();
  EXPECT_NE(ctx, nullptr);

  ASSERT_TRUE(EVP_PQ_KEM_CTX_init(ctx, kyber_kem));
  ASSERT_TRUE(EVP_PQ_KEM_generate_keypair(ctx));
  EXPECT_EQ(Bytes(pk),
            Bytes(ctx->public_key, kyber_kem->public_key_length));
  EXPECT_EQ(Bytes(sk),
            Bytes(ctx->private_key, kyber_kem->private_key_length));

  ASSERT_TRUE(EVP_PQ_KEM_encapsulate(ctx));
  EXPECT_EQ(Bytes(ct),
            Bytes(ctx->ciphertext, kyber_kem->ciphertext_length));

  ASSERT_TRUE(EVP_PQ_KEM_decapsulate(ctx));
  EXPECT_EQ(Bytes(ss),
            Bytes(ctx->shared_secret, kyber_kem->shared_secret_length));
}

TEST(Kyber512Test, KAT_tests) {
 FileTestGTest("crypto/evp_extra/pq_kem_kat_tests_kyber512.txt", RunTest);
}
