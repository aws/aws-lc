#include <gtest/gtest.h>
#include <openssl/base.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/mem.h>

#include "../crypto/evp_extra/internal.h"
#include "../fipsmodule/evp/internal.h"
#include "../internal.h"
#include "kem_kyber.h"

TEST(Kyber512Test, KeyGeneration) {
  EVP_PKEY_CTX *kyber_pkey_ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_KYBER512, nullptr);
  ASSERT_NE(kyber_pkey_ctx, nullptr);

  EVP_PKEY *kyber_pkey = EVP_PKEY_new();
  ASSERT_NE(kyber_pkey, nullptr);

  EXPECT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx));
  EXPECT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx, &kyber_pkey));
  ASSERT_NE(kyber_pkey->pkey.ptr, nullptr);

  const KYBER512_KEY *kyber512Key = (KYBER512_KEY *)(kyber_pkey->pkey.ptr);
  EXPECT_TRUE(kyber512Key->has_private);

  uint8_t *buf = nullptr;
  size_t buf_size;
  EXPECT_TRUE(EVP_PKEY_get_raw_public_key(kyber_pkey, buf, &buf_size));
  EXPECT_EQ((size_t)KYBER512_PUBLIC_KEY_BYTES, buf_size);

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
  EXPECT_EQ((size_t)KYBER512_SECRET_KEY_BYTES, buf_size);

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

TEST(Kyber512Test, KeyComparison) {
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

TEST(Kyber512Test, NewKeyFromBytes) {
  // Source key
  EVP_PKEY_CTX *kyber_pkey_ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_KYBER512, nullptr);
  ASSERT_NE(kyber_pkey_ctx, nullptr);

  EVP_PKEY *kyber_pkey = EVP_PKEY_new();
  ASSERT_NE(kyber_pkey, nullptr);

  EXPECT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx));
  EXPECT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx, &kyber_pkey));
  ASSERT_NE(kyber_pkey->pkey.ptr, nullptr);
  const KYBER512_KEY *kyber512Key = (KYBER512_KEY *)(kyber_pkey->pkey.ptr);

  // New raw public key
  EVP_PKEY *new_public = EVP_PKEY_new_raw_public_key(EVP_PKEY_KYBER512,
                                                     NULL,
                                                     kyber512Key->pub,
                                                     KYBER512_PUBLIC_KEY_BYTES);
  ASSERT_NE(new_public, nullptr);

  uint8_t *buf = nullptr;
  size_t buf_size;
  EXPECT_FALSE(EVP_PKEY_get_raw_private_key(new_public, buf, &buf_size));
  uint32_t err = ERR_get_error();
  EXPECT_EQ(ERR_LIB_EVP, ERR_GET_LIB(err));
  EXPECT_EQ(EVP_R_NOT_A_PRIVATE_KEY, ERR_GET_REASON(err));

  // EVP_PKEY_cmp just compares the public keys so this should return 1
  EXPECT_EQ(1, EVP_PKEY_cmp(kyber_pkey, new_public));

  // New raw private key
  EVP_PKEY *new_private = EVP_PKEY_new_raw_private_key(EVP_PKEY_KYBER512,
                                                       NULL,
                                                       kyber512Key->priv,
                                                       KYBER512_SECRET_KEY_BYTES);
  ASSERT_NE(new_private, nullptr);
  const KYBER512_KEY *newKyber512Key = (KYBER512_KEY *)(new_private->pkey.ptr);
  EXPECT_EQ(0, OPENSSL_memcmp(kyber512Key->priv, newKyber512Key->priv, KYBER512_SECRET_KEY_BYTES));

  EVP_PKEY_CTX_free(kyber_pkey_ctx);
  EVP_PKEY_free(new_public);
  EVP_PKEY_free(new_private);
}

TEST(Kyber512Test, KeySize) {
  EVP_PKEY_CTX *kyber_pkey_ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_KYBER512, nullptr);
  ASSERT_NE(kyber_pkey_ctx, nullptr);

  EVP_PKEY *kyber_pkey = EVP_PKEY_new();
  ASSERT_NE(kyber_pkey, nullptr);

  EXPECT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx));
  EXPECT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx, &kyber_pkey));

  EXPECT_EQ(KYBER512_PUBLIC_KEY_BYTES + KYBER512_SECRET_KEY_BYTES, EVP_PKEY_size(kyber_pkey));
  EXPECT_EQ(8*(KYBER512_PUBLIC_KEY_BYTES + KYBER512_SECRET_KEY_BYTES), EVP_PKEY_bits(kyber_pkey));

  EVP_PKEY_CTX_free(kyber_pkey_ctx);
}

TEST(Kyber512Test, KEMOperations) {
  // Basic functional test for KYBER512.
  // Simulate two sides of the key exchange mechanism.
  size_t shared_secret_len = KYBER512_SHARED_SECRET_BYTES;
  size_t ciphertext_len = KYBER512_CIPHERTEXT_BYTES;
  uint8_t shared_secret_alice[KYBER512_SHARED_SECRET_BYTES];
  uint8_t shared_secret_bob[KYBER512_SHARED_SECRET_BYTES];
  uint8_t ciphertext_alice[KYBER512_CIPHERTEXT_BYTES];
  uint8_t ciphertext_bob[KYBER512_CIPHERTEXT_BYTES];

  // Alice generates the key pair.
  EVP_PKEY_CTX *kyber_pkey_ctx_alice = EVP_PKEY_CTX_new_id(EVP_PKEY_KYBER512, nullptr);
  EVP_PKEY *kyber_pkey_alice = EVP_PKEY_new();
  EXPECT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx_alice));
  EXPECT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx_alice, &kyber_pkey_alice));

  // Alice passes the public key to Bob.
  const KYBER512_KEY *kyber_key_alice = (KYBER512_KEY *)(kyber_pkey_alice->pkey.ptr);

  EVP_PKEY_CTX *kyber_pkey_ctx_bob = EVP_PKEY_CTX_new_id(EVP_PKEY_KYBER512, nullptr);
  EVP_PKEY *kyber_pkey_bob = EVP_PKEY_new_raw_public_key(EVP_PKEY_KYBER512,
                                                         NULL,
                                                         kyber_key_alice->pub, /* this method performs a memcpy internally */
                                                         KYBER512_PUBLIC_KEY_BYTES);
  kyber_pkey_ctx_bob->pkey = kyber_pkey_bob;

  // Bob generates a shared secret and encapsulates it.
  ASSERT_TRUE(EVP_PKEY_encapsulate(kyber_pkey_ctx_bob, ciphertext_bob, &ciphertext_len, shared_secret_bob, &shared_secret_len));

  // Bob sends the ciphertext to Alice.
  OPENSSL_memcpy(ciphertext_alice, ciphertext_bob, ciphertext_len);

  // Alice decapsulates the ciphertext to obtain the shared secret.
  ASSERT_TRUE(EVP_PKEY_decapsulate(kyber_pkey_ctx_alice, shared_secret_alice, &shared_secret_len, ciphertext_alice, ciphertext_len));

  // Verify that Alice and Bob have the same shared secret.
  for (size_t i = 0; i < shared_secret_len; i++) {
    EXPECT_EQ(shared_secret_alice[i], shared_secret_bob[i]);
  }

  // Invalidate the ciphertext and run decapsulate on it.
  ciphertext_alice[0] ^= 1;

  // Decapsulate should return success.
  ASSERT_TRUE(EVP_PKEY_decapsulate(kyber_pkey_ctx_alice, shared_secret_alice, &shared_secret_len, ciphertext_alice, ciphertext_len));

  // But the shared secret should be different from Bob's.
  unsigned char tmp = 0;
  for (size_t i = 0; i < shared_secret_len; i++) {
    tmp |= (shared_secret_alice[i] ^ shared_secret_bob[i]);
  }
  EXPECT_NE(tmp, 0);

  EVP_PKEY_CTX_free(kyber_pkey_ctx_alice);
  EVP_PKEY_CTX_free(kyber_pkey_ctx_bob);
}

TEST(Kyber512Test, KEMSizeChecks) {
  size_t shared_secret_len = 0;
  size_t ciphertext_len = 0;

  EVP_PKEY_CTX *kyber_pkey_ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_KYBER512, nullptr);
  EVP_PKEY *kyber_pkey = EVP_PKEY_new();
  EXPECT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx));
  EXPECT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx, &kyber_pkey));

  ASSERT_TRUE(EVP_PKEY_encapsulate(kyber_pkey_ctx, NULL, &ciphertext_len, NULL, &shared_secret_len));
  EXPECT_EQ(shared_secret_len, (size_t)KYBER512_SHARED_SECRET_BYTES);
  EXPECT_EQ(ciphertext_len, (size_t)KYBER512_CIPHERTEXT_BYTES);

  shared_secret_len = 0;

  ASSERT_TRUE(EVP_PKEY_decapsulate(kyber_pkey_ctx, NULL, &shared_secret_len, NULL, ciphertext_len));
  EXPECT_EQ(shared_secret_len, (size_t)KYBER512_SHARED_SECRET_BYTES);

  // Verify that encaps/decaps fail when given too small buffer lengths.
  uint8_t shared_secret[KYBER512_SHARED_SECRET_BYTES];
  uint8_t ciphertext[KYBER512_CIPHERTEXT_BYTES];

  // encapsulate -- ciphertext_len too small, shared_secret_len ok.
  ciphertext_len -= 1;
  ASSERT_FALSE(EVP_PKEY_encapsulate(kyber_pkey_ctx, ciphertext, &ciphertext_len, shared_secret, &shared_secret_len));
  
  // encapsulate -- ciphertext_len ok, shared_secret_len too small.
  ciphertext_len += 1;
  shared_secret_len -= 1;
  ASSERT_FALSE(EVP_PKEY_encapsulate(kyber_pkey_ctx, ciphertext, &ciphertext_len, shared_secret, &shared_secret_len));

  // decapsulate -- shared_secret_len too small
  ASSERT_FALSE(EVP_PKEY_decapsulate(kyber_pkey_ctx, shared_secret, &shared_secret_len, ciphertext, ciphertext_len));

  // Final check that everything works with good ciphertext_len and share_secret_len.
  shared_secret_len += 1;
  ASSERT_TRUE(EVP_PKEY_encapsulate(kyber_pkey_ctx, ciphertext, &ciphertext_len, shared_secret, &shared_secret_len));
  ASSERT_TRUE(EVP_PKEY_decapsulate(kyber_pkey_ctx, shared_secret, &shared_secret_len, ciphertext, ciphertext_len));

  EVP_PKEY_CTX_free(kyber_pkey_ctx);
}

TEST(Kyber512Test, KEMInvalidKeyType) {
  size_t shared_secret_len = KYBER512_SHARED_SECRET_BYTES;
  size_t ciphertext_len = KYBER512_CIPHERTEXT_BYTES;
  uint8_t shared_secret[KYBER512_SHARED_SECRET_BYTES];
  uint8_t ciphertext[KYBER512_CIPHERTEXT_BYTES];

  // encap and decap should fail on wrong key type
  EVP_PKEY_CTX *kyber_pkey_ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_KYBER512, nullptr);
  EVP_PKEY *kyber_pkey = EVP_PKEY_new();
  EXPECT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx));
  EXPECT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx, &kyber_pkey));
  // Swap the key for invalid type
  EVP_PKEY_CTX *rsa_pkey_ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_RSA, nullptr);
  EVP_PKEY *rsa_pkey = EVP_PKEY_new();
  rsa_pkey_ctx->pkey = rsa_pkey;
  kyber_pkey_ctx->pkey = rsa_pkey;
  ASSERT_FALSE(EVP_PKEY_encapsulate(kyber_pkey_ctx, ciphertext, &ciphertext_len, shared_secret, &shared_secret_len));
  ASSERT_FALSE(EVP_PKEY_decapsulate(kyber_pkey_ctx, shared_secret, &shared_secret_len, ciphertext, ciphertext_len));
  // Swap the key back to the original one so that the cleanups happen correctly
  kyber_pkey_ctx->pkey = kyber_pkey;

  EVP_PKEY_CTX_free(kyber_pkey_ctx);
  EVP_PKEY_CTX_free(rsa_pkey_ctx);
}

TEST(Kyber512Test, KEMFailureModes) {
  size_t shared_secret_len = KYBER512_SHARED_SECRET_BYTES;
  size_t ciphertext_len = KYBER512_CIPHERTEXT_BYTES;
  uint8_t shared_secret[KYBER512_SHARED_SECRET_BYTES];
  uint8_t ciphertext[KYBER512_CIPHERTEXT_BYTES];

  // NULL EVP_PKEY_CTX
  ASSERT_FALSE(EVP_PKEY_encapsulate(NULL, ciphertext, &ciphertext_len, shared_secret, &shared_secret_len));
  ASSERT_FALSE(EVP_PKEY_decapsulate(NULL, shared_secret, &shared_secret_len, ciphertext, ciphertext_len));
}
