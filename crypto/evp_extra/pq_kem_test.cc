#include <gtest/gtest.h>

#include "openssl/pq_kem.h"
#include "../crypto/test/test_util.h"
#include "openssl/mem.h"


TEST(PQCryptoTest, Basic) {
  // Basic functional test for KYBER512
  const EVP_PQ_KEM *kyber_kem = &EVP_PQ_KEM_kyber512;
  EXPECT_NE(kyber_kem, nullptr);

  // Simulate two sides of the key exchange mechanism.
  EVP_PQ_KEM_CTX *ctxA = EVP_PQ_KEM_CTX_new();
  EVP_PQ_KEM_CTX *ctxB = EVP_PQ_KEM_CTX_new();
  EXPECT_NE(ctxA, nullptr);
  EXPECT_NE(ctxB, nullptr);

  ASSERT_TRUE(EVP_PQ_KEM_CTX_init(ctxA, kyber_kem));
  ASSERT_TRUE(EVP_PQ_KEM_CTX_init(ctxB, kyber_kem));

  // Alice generates the key pair.
  ASSERT_TRUE(EVP_PQ_KEM_generate_keypair(ctxA));

  // Alice passes the public key to Bob.
  OPENSSL_memcpy(ctxB->public_key, ctxA->public_key,
                 ctxB->kem->public_key_length);

  // Bob generates a shared secret and encapsulates it.
  ASSERT_TRUE(EVP_PQ_KEM_encapsulate(ctxB));

  // Bob sends the ciphertext to Alice.
  OPENSSL_memcpy(ctxA->ciphertext, ctxB->ciphertext,
                 ctxA->kem->ciphertext_length);

  // Alice decapsulates the ciphertext to obtain the shared secret.
  ASSERT_TRUE(EVP_PQ_KEM_decapsulate(ctxA));

  // Verify that Alice and Bob have the same shared secret.
  for (int i = 0; i < ctxA->kem->shared_secret_length; i++) {
    EXPECT_EQ(ctxA->shared_secret[i], ctxB->shared_secret[i]);
  }

  // Invalidate the ciphertext and run decapsulate on it.
  ctxA->ciphertext[0] ^= 1;

  // Decapsulate should return success.
  ASSERT_TRUE(EVP_PQ_KEM_decapsulate(ctxA));

  // But the shared secret should be different from Bob's.
  unsigned char tmp = 0;
  for (int i = 0; i < ctxA->kem->shared_secret_length; i++) {
    tmp |= (ctxA->shared_secret[i] ^ ctxB->shared_secret[i]);
  }
  EXPECT_NE(tmp, 0);

  EVP_PQ_KEM_CTX_free(ctxA);
  EVP_PQ_KEM_CTX_free(ctxB);
}
