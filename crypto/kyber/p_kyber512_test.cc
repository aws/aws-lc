#include <gtest/gtest.h>
#include <openssl/base.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/mem.h>

#include "../crypto/evp_extra/internal.h"
#include "../fipsmodule/evp/internal.h"
#include "../internal.h"
#include "kem_kyber.h"

static uint8_t* get_pub_from_kyber_key(EVP_PKEY *pkey) {
  if (EVP_PKEY_id(pkey) == EVP_PKEY_KYBER512) {
    KYBER512_KEY *key = (KYBER512_KEY *)(pkey->pkey.ptr);
    return key->pub;
  } else if (EVP_PKEY_id(pkey) == EVP_PKEY_KYBER768) {
    KYBER768_KEY *key = (KYBER768_KEY *)(pkey->pkey.ptr);
    return key->pub;
  }
  return nullptr;
}

static uint8_t* get_priv_from_kyber_key(EVP_PKEY *pkey) {
  if (EVP_PKEY_id(pkey) == EVP_PKEY_KYBER512) {
    KYBER512_KEY *key = (KYBER512_KEY *)(pkey->pkey.ptr);
    return key->priv;
  } else if (EVP_PKEY_id(pkey) == EVP_PKEY_KYBER768) {
    KYBER768_KEY *key = (KYBER768_KEY *)(pkey->pkey.ptr);
    return key->priv;
  }
  return nullptr;
}

static uint8_t get_has_private_from_kyber_key(EVP_PKEY *pkey) {
  if (EVP_PKEY_id(pkey) == EVP_PKEY_KYBER512) {
    KYBER512_KEY *key = (KYBER512_KEY *)(pkey->pkey.ptr);
    return key->has_private;
  } else if (EVP_PKEY_id(pkey) == EVP_PKEY_KYBER768) {
    KYBER768_KEY *key = (KYBER768_KEY *)(pkey->pkey.ptr);
    return key->has_private;
  }
  return 0;
}

static size_t kyber_public_key_size(int pkey_id) {
  if (pkey_id == EVP_PKEY_KYBER512) {
    return KYBER512_PUBLIC_KEY_BYTES;
  } else if (pkey_id == EVP_PKEY_KYBER768) {
    return KYBER768_PUBLIC_KEY_BYTES;
  }
  return 0;
}

static size_t kyber_secret_key_size(int pkey_id) {
  if (pkey_id == EVP_PKEY_KYBER512) {
    return KYBER512_SECRET_KEY_BYTES;
  } else if (pkey_id == EVP_PKEY_KYBER768) {
    return KYBER768_SECRET_KEY_BYTES;
  }
  return 0;
}

static size_t kyber_shared_secret_size(int pkey_id) {
  if (pkey_id == EVP_PKEY_KYBER512) {
    return KYBER512_SHARED_SECRET_BYTES;
  } else if (pkey_id == EVP_PKEY_KYBER768) {
    return KYBER768_SHARED_SECRET_BYTES;
  }
  return 0;
}

static size_t kyber_ciphertext_size(int pkey_id) {
  if (pkey_id == EVP_PKEY_KYBER512) {
    return KYBER512_CIPHERTEXT_BYTES;
  } else if (pkey_id == EVP_PKEY_KYBER768) {
    return KYBER768_CIPHERTEXT_BYTES;
  }
  return 0;
}

TEST(KyberTest, KeyGeneration) {
  for (int pkey_id : {EVP_PKEY_KYBER512, EVP_PKEY_KYBER768}) {
    EVP_PKEY_CTX *kyber_pkey_ctx = EVP_PKEY_CTX_new_id(pkey_id, nullptr);
    ASSERT_NE(kyber_pkey_ctx, nullptr);

    EVP_PKEY *kyber_pkey = EVP_PKEY_new();
    ASSERT_NE(kyber_pkey, nullptr);

    EXPECT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx));
    EXPECT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx, &kyber_pkey));
    ASSERT_NE(kyber_pkey->pkey.ptr, nullptr);

    EXPECT_TRUE(get_has_private_from_kyber_key(kyber_pkey));

    uint8_t *buf = nullptr;
    size_t buf_size;
    EXPECT_TRUE(EVP_PKEY_get_raw_public_key(kyber_pkey, buf, &buf_size));
    EXPECT_EQ(kyber_public_key_size(pkey_id), buf_size);

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
    EXPECT_EQ(kyber_secret_key_size(pkey_id), buf_size);

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
}

TEST(KyberTest, KeyComparison) {
  for (int pkey_id : {EVP_PKEY_KYBER512, EVP_PKEY_KYBER768}) {
    EVP_PKEY_CTX *kyber_pkey_ctx1 = EVP_PKEY_CTX_new_id(pkey_id, nullptr);
    ASSERT_NE(kyber_pkey_ctx1, nullptr);

    EVP_PKEY *kyber_pkey1 = EVP_PKEY_new();
    ASSERT_NE(kyber_pkey1, nullptr);

    EXPECT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx1));
    EXPECT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx1, &kyber_pkey1));
    ASSERT_NE(kyber_pkey1->pkey.ptr, nullptr);

    EVP_PKEY_CTX *kyber_pkey_ctx2 = EVP_PKEY_CTX_new_id(pkey_id, nullptr);
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
}

TEST(KyberTest, NewKeyFromBytes) {
  for (int pkey_id : {EVP_PKEY_KYBER512, EVP_PKEY_KYBER768}) {
    // Source key
    EVP_PKEY_CTX *kyber_pkey_ctx = EVP_PKEY_CTX_new_id(pkey_id, nullptr);
    ASSERT_NE(kyber_pkey_ctx, nullptr);

    EVP_PKEY *kyber_pkey = EVP_PKEY_new();
    ASSERT_NE(kyber_pkey, nullptr);

    EXPECT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx));
    EXPECT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx, &kyber_pkey));
    ASSERT_NE(kyber_pkey->pkey.ptr, nullptr);

    uint8_t *pub  = get_pub_from_kyber_key(kyber_pkey);
    uint8_t *priv = get_priv_from_kyber_key(kyber_pkey);

    size_t pk_bytes = kyber_public_key_size(pkey_id);
    size_t sk_bytes = kyber_secret_key_size(pkey_id);

    // New raw public key
    EVP_PKEY *new_public = EVP_PKEY_new_raw_public_key(pkey_id, NULL, pub, pk_bytes);
                                                       
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
    EVP_PKEY *new_private = EVP_PKEY_new_raw_private_key(pkey_id, NULL, priv, sk_bytes);
    ASSERT_NE(new_private, nullptr);
    uint8_t *new_priv = get_priv_from_kyber_key(new_private);
    EXPECT_EQ(0, OPENSSL_memcmp(priv, new_priv, sk_bytes));

    EVP_PKEY_CTX_free(kyber_pkey_ctx);
    EVP_PKEY_free(new_public);
    EVP_PKEY_free(new_private);
  }
}

TEST(KyberTest, KeySize) {
  for (int pkey_id : {EVP_PKEY_KYBER512, EVP_PKEY_KYBER768}) {
    EVP_PKEY_CTX *kyber_pkey_ctx = EVP_PKEY_CTX_new_id(pkey_id, nullptr);
    ASSERT_NE(kyber_pkey_ctx, nullptr);

    EVP_PKEY *kyber_pkey = EVP_PKEY_new();
    ASSERT_NE(kyber_pkey, nullptr);

    EXPECT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx));
    EXPECT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx, &kyber_pkey));

    size_t pk_bytes = kyber_public_key_size(pkey_id);
    size_t sk_bytes = kyber_secret_key_size(pkey_id);

    EXPECT_EQ(pk_bytes + sk_bytes, (size_t) EVP_PKEY_size(kyber_pkey));
    EXPECT_EQ(8 * (pk_bytes + sk_bytes), (size_t) EVP_PKEY_bits(kyber_pkey));

    EVP_PKEY_CTX_free(kyber_pkey_ctx);
  }
}

TEST(KyberTest, KEMOperations) {
  for (int pkey_id : {EVP_PKEY_KYBER512, EVP_PKEY_KYBER768}) {
    // Basic functional test for Kyber that simulates two sides
    // of the key exchange mechanism.
    size_t shared_secret_len = kyber_shared_secret_size(pkey_id);
    size_t ciphertext_len = kyber_ciphertext_size(pkey_id);
    size_t public_key_len = kyber_public_key_size(pkey_id);

    uint8_t *shared_secret_alice = (uint8_t*) OPENSSL_malloc(shared_secret_len);
    uint8_t *shared_secret_bob   = (uint8_t*) OPENSSL_malloc(shared_secret_len);
    uint8_t *ciphertext_alice    = (uint8_t*) OPENSSL_malloc(ciphertext_len);
    uint8_t *ciphertext_bob      = (uint8_t*) OPENSSL_malloc(ciphertext_len);

    ASSERT_NE(shared_secret_alice, nullptr);
    ASSERT_NE(shared_secret_bob, nullptr);
    ASSERT_NE(ciphertext_alice, nullptr);
    ASSERT_NE(ciphertext_bob, nullptr);

    // Alice generates the key pair.
    EVP_PKEY_CTX *kyber_pkey_ctx_alice = EVP_PKEY_CTX_new_id(pkey_id, nullptr);
    EVP_PKEY *kyber_pkey_alice = EVP_PKEY_new();
    EXPECT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx_alice));
    EXPECT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx_alice, &kyber_pkey_alice));

    // Alice passes the public key to Bob.
    uint8_t *pub_alice = get_pub_from_kyber_key(kyber_pkey_alice);
    EVP_PKEY_CTX *kyber_pkey_ctx_bob = EVP_PKEY_CTX_new_id(pkey_id, nullptr);
    EVP_PKEY *kyber_pkey_bob = EVP_PKEY_new_raw_public_key(pkey_id, NULL, pub_alice, public_key_len);
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

    OPENSSL_free(shared_secret_alice);
    OPENSSL_free(shared_secret_bob);
    OPENSSL_free(ciphertext_alice);
    OPENSSL_free(ciphertext_bob);

    EVP_PKEY_CTX_free(kyber_pkey_ctx_alice);
    EVP_PKEY_CTX_free(kyber_pkey_ctx_bob);
  }
}

TEST(KyberTest, KEMSizeChecks) {
  for (int pkey_id : {EVP_PKEY_KYBER512, EVP_PKEY_KYBER768}) {
    size_t shared_secret_len = 0;
    size_t ciphertext_len = 0;

    size_t expected_ss_len = kyber_shared_secret_size(pkey_id);
    size_t expected_ct_len = kyber_ciphertext_size(pkey_id);

    EVP_PKEY_CTX *kyber_pkey_ctx = EVP_PKEY_CTX_new_id(pkey_id, nullptr);
    EVP_PKEY *kyber_pkey = EVP_PKEY_new();
    EXPECT_TRUE(EVP_PKEY_keygen_init(kyber_pkey_ctx));
    EXPECT_TRUE(EVP_PKEY_keygen(kyber_pkey_ctx, &kyber_pkey));

    ASSERT_TRUE(EVP_PKEY_encapsulate(kyber_pkey_ctx, NULL, &ciphertext_len, NULL, &shared_secret_len));
    EXPECT_EQ(shared_secret_len, expected_ss_len);
    EXPECT_EQ(ciphertext_len, expected_ct_len);

    shared_secret_len = 0;

    ASSERT_TRUE(EVP_PKEY_decapsulate(kyber_pkey_ctx, NULL, &shared_secret_len, NULL, ciphertext_len));
    EXPECT_EQ(shared_secret_len, expected_ss_len);

    // Verify that encaps/decaps fail when given too small buffer lengths.
    uint8_t *shared_secret = (uint8_t*) OPENSSL_malloc(shared_secret_len);
    uint8_t *ciphertext = (uint8_t*) OPENSSL_malloc(ciphertext_len);
    ASSERT_NE(shared_secret, nullptr);
    ASSERT_NE(ciphertext, nullptr);

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
    OPENSSL_free(shared_secret);
    OPENSSL_free(ciphertext);
  }
}

TEST(KyberTest, KEMInvalidKeyType) {
  for (int pkey_id : {EVP_PKEY_KYBER512, EVP_PKEY_KYBER768}) {
    size_t shared_secret_len = kyber_shared_secret_size(pkey_id);
    size_t ciphertext_len = kyber_ciphertext_size(pkey_id);

    uint8_t *shared_secret = (uint8_t*) OPENSSL_malloc(shared_secret_len);
    uint8_t *ciphertext = (uint8_t*) OPENSSL_malloc(ciphertext_len);
    ASSERT_NE(shared_secret, nullptr);
    ASSERT_NE(ciphertext, nullptr);

    // encap and decap should fail on wrong key type
    EVP_PKEY_CTX *kyber_pkey_ctx = EVP_PKEY_CTX_new_id(pkey_id, nullptr);
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

    OPENSSL_free(shared_secret);
    OPENSSL_free(ciphertext);

    EVP_PKEY_CTX_free(kyber_pkey_ctx);
    EVP_PKEY_CTX_free(rsa_pkey_ctx);
  }
}

TEST(KyberTest, KEMFailureModes) {
  for (int pkey_id : {EVP_PKEY_KYBER512, EVP_PKEY_KYBER768}) {
    size_t shared_secret_len = kyber_shared_secret_size(pkey_id);
    size_t ciphertext_len = kyber_ciphertext_size(pkey_id);

    uint8_t *shared_secret = (uint8_t*) OPENSSL_malloc(shared_secret_len);
    uint8_t *ciphertext = (uint8_t*) OPENSSL_malloc(ciphertext_len);
    ASSERT_NE(shared_secret, nullptr);
    ASSERT_NE(ciphertext, nullptr);

    // NULL EVP_PKEY_CTX
    ASSERT_FALSE(EVP_PKEY_encapsulate(NULL, ciphertext, &ciphertext_len, shared_secret, &shared_secret_len));
    ASSERT_FALSE(EVP_PKEY_decapsulate(NULL, shared_secret, &shared_secret_len, ciphertext, ciphertext_len));

    OPENSSL_free(shared_secret);
    OPENSSL_free(ciphertext);
  }
}
