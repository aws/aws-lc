// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <gtest/gtest.h>
#include <openssl/base.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/mem.h>
#include <openssl/obj.h>
#include "../test/test_util.h"

#include <vector>
#include "../crypto/evp_extra/internal.h"
#include "../fipsmodule/evp/internal.h"
#include "../internal.h"
#include "sig_dilithium.h"

TEST(Dilithium3Test, KeyGeneration) {
  // Basic key generation tests for Dilithium3
  // Generate a Dilithium3 key
  EVP_PKEY_CTX *dilithium_pkey_ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_DILITHIUM3, nullptr);
  ASSERT_NE(dilithium_pkey_ctx, nullptr);

  EVP_PKEY *dilithium_pkey = EVP_PKEY_new();
  ASSERT_NE(dilithium_pkey, nullptr);

  EXPECT_TRUE(EVP_PKEY_keygen_init(dilithium_pkey_ctx));
  EXPECT_TRUE(EVP_PKEY_keygen(dilithium_pkey_ctx, &dilithium_pkey));
  ASSERT_NE(dilithium_pkey->pkey.ptr, nullptr);

  const DILITHIUM3_KEY *dilithium3Key = (DILITHIUM3_KEY *)(dilithium_pkey->pkey.ptr);
  EXPECT_TRUE(dilithium3Key->has_private);

  // Extract public key and check it is of the correct size
  uint8_t *buf = nullptr;
  size_t buf_size;
  EXPECT_TRUE(EVP_PKEY_get_raw_public_key(dilithium_pkey, buf, &buf_size));
  EXPECT_EQ((size_t)DILITHIUM3_PUBLIC_KEY_BYTES, buf_size);

  buf = (uint8_t *)OPENSSL_malloc(buf_size);
  ASSERT_NE(buf, nullptr);
  EXPECT_TRUE(EVP_PKEY_get_raw_public_key(dilithium_pkey, buf, &buf_size));

  buf_size = 0;
  EXPECT_FALSE(EVP_PKEY_get_raw_public_key(dilithium_pkey, buf, &buf_size));

  uint32_t err = ERR_get_error();
  EXPECT_EQ(ERR_LIB_EVP, ERR_GET_LIB(err));
  EXPECT_EQ(EVP_R_BUFFER_TOO_SMALL, ERR_GET_REASON(err));
  OPENSSL_free(buf);
  buf = nullptr;

  // Extract private key and check it is of the correct size
  EXPECT_TRUE(EVP_PKEY_get_raw_private_key(dilithium_pkey, buf, &buf_size));
  EXPECT_EQ((size_t)DILITHIUM3_PRIVATE_KEY_BYTES, buf_size);

  buf = (uint8_t *)OPENSSL_malloc(buf_size);
  ASSERT_NE(buf, nullptr);
  EXPECT_TRUE(EVP_PKEY_get_raw_private_key(dilithium_pkey, buf, &buf_size));

  buf_size = 0;
  EXPECT_FALSE(EVP_PKEY_get_raw_private_key(dilithium_pkey, buf, &buf_size));
  err = ERR_get_error();
  EXPECT_EQ(ERR_LIB_EVP, ERR_GET_LIB(err));
  EXPECT_EQ(EVP_R_BUFFER_TOO_SMALL, ERR_GET_REASON(err));
  OPENSSL_free(buf);

  EVP_PKEY_CTX_free(dilithium_pkey_ctx);
  EVP_PKEY_free(dilithium_pkey);
}

TEST(Dilithium3Test, KeyComparison) {
  // Generate two Dilithium3 keys are check that they are not equal.
  EVP_PKEY_CTX *dilithium_pkey_ctx1 = EVP_PKEY_CTX_new_id(EVP_PKEY_DILITHIUM3, nullptr);
  ASSERT_NE(dilithium_pkey_ctx1, nullptr);

  EVP_PKEY *dilithium_pkey1 = EVP_PKEY_new();
  ASSERT_NE(dilithium_pkey1, nullptr);

  EXPECT_TRUE(EVP_PKEY_keygen_init(dilithium_pkey_ctx1));
  EXPECT_TRUE(EVP_PKEY_keygen(dilithium_pkey_ctx1, &dilithium_pkey1));
  ASSERT_NE(dilithium_pkey1->pkey.ptr, nullptr);

  EVP_PKEY_CTX *dilithium_pkey_ctx2 = EVP_PKEY_CTX_new_id(EVP_PKEY_DILITHIUM3, nullptr);
  ASSERT_NE(dilithium_pkey_ctx2, nullptr);

  EVP_PKEY *dilithium_pkey2 = EVP_PKEY_new();
  ASSERT_NE(dilithium_pkey2, nullptr);

  EXPECT_TRUE(EVP_PKEY_keygen_init(dilithium_pkey_ctx2));
  EXPECT_TRUE(EVP_PKEY_keygen(dilithium_pkey_ctx2, &dilithium_pkey2));
  ASSERT_NE(dilithium_pkey2->pkey.ptr, nullptr);

  EXPECT_EQ(0, EVP_PKEY_cmp(dilithium_pkey1, dilithium_pkey2));

  EVP_PKEY_free(dilithium_pkey1);
  EVP_PKEY_free(dilithium_pkey2);
  EVP_PKEY_CTX_free(dilithium_pkey_ctx1);
  EVP_PKEY_CTX_free(dilithium_pkey_ctx2);
}

TEST(Dilithium3Test, NewKeyFromBytes) {
  // Test the generation of a Dilithium3 key from bytes
  // Source key
  EVP_PKEY_CTX *dilithium_pkey_ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_DILITHIUM3, nullptr);
  ASSERT_NE(dilithium_pkey_ctx, nullptr);

  EVP_PKEY *dilithium_pkey = EVP_PKEY_new();
  ASSERT_NE(dilithium_pkey, nullptr);

  EXPECT_TRUE(EVP_PKEY_keygen_init(dilithium_pkey_ctx));
  EXPECT_TRUE(EVP_PKEY_keygen(dilithium_pkey_ctx, &dilithium_pkey));
  ASSERT_NE(dilithium_pkey->pkey.ptr, nullptr);
  const DILITHIUM3_KEY *dilithium3Key = (DILITHIUM3_KEY *)(dilithium_pkey->pkey.ptr);

  // New raw public key
  EVP_PKEY *new_public = EVP_PKEY_new_raw_public_key(EVP_PKEY_DILITHIUM3,
                                                     NULL,
                                                     dilithium3Key->pub,
                                                     DILITHIUM3_PUBLIC_KEY_BYTES);
  ASSERT_NE(new_public, nullptr);

  uint8_t *buf = nullptr;
  size_t buf_size;
  EXPECT_FALSE(EVP_PKEY_get_raw_private_key(new_public, buf, &buf_size));
  uint32_t err = ERR_get_error();
  EXPECT_EQ(ERR_LIB_EVP, ERR_GET_LIB(err));
  EXPECT_EQ(EVP_R_NOT_A_PRIVATE_KEY, ERR_GET_REASON(err));

  // EVP_PKEY_cmp just compares the public keys so this should return 1
  EXPECT_EQ(1, EVP_PKEY_cmp(dilithium_pkey, new_public));

  // New raw private key
  EVP_PKEY *new_private = EVP_PKEY_new_raw_private_key(EVP_PKEY_DILITHIUM3,
                                                       NULL,
                                                       dilithium3Key->priv,
                                                       DILITHIUM3_PRIVATE_KEY_BYTES);
  ASSERT_NE(new_private, nullptr);
  const DILITHIUM3_KEY *newDilithium3Key = (DILITHIUM3_KEY *)(new_private->pkey.ptr);
  EXPECT_EQ(0, OPENSSL_memcmp(dilithium3Key->priv, newDilithium3Key->priv,
                              DILITHIUM3_PRIVATE_KEY_BYTES));

  EVP_PKEY_CTX_free(dilithium_pkey_ctx);
  EVP_PKEY_free(new_public);
  EVP_PKEY_free(new_private);
  EVP_PKEY_free(dilithium_pkey);
}

TEST(Dilithium3Test, KeySize) {
  // Test the key size of Dilithium3 key is as expected
  EVP_PKEY_CTX *dilithium_pkey_ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_DILITHIUM3, nullptr);
  ASSERT_NE(dilithium_pkey_ctx, nullptr);

  EVP_PKEY *dilithium_pkey = EVP_PKEY_new();
  ASSERT_NE(dilithium_pkey, nullptr);

  EXPECT_TRUE(EVP_PKEY_keygen_init(dilithium_pkey_ctx));
  EXPECT_TRUE(EVP_PKEY_keygen(dilithium_pkey_ctx, &dilithium_pkey));

  EXPECT_EQ(DILITHIUM3_SIGNATURE_BYTES, EVP_PKEY_size(dilithium_pkey));
  EXPECT_EQ(8*(DILITHIUM3_PUBLIC_KEY_BYTES), EVP_PKEY_bits(dilithium_pkey));

  EVP_PKEY_CTX_free(dilithium_pkey_ctx);
  EVP_PKEY_free(dilithium_pkey);
}

TEST(Dilithium3Test, Encoding) {
  // Test Dilithium keypairs are extractable, and encode/parse correctly.
  //generate dilithium key
  EVP_PKEY_CTX *dilithium_pkey_ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_DILITHIUM3, nullptr);
  EVP_PKEY *dilithium_pkey = EVP_PKEY_new();
  EVP_PKEY_keygen_init(dilithium_pkey_ctx);
  EVP_PKEY_keygen(dilithium_pkey_ctx, &dilithium_pkey);
  const DILITHIUM3_KEY *dilithium3Key = (DILITHIUM3_KEY *)(dilithium_pkey->pkey.ptr);

  //Create a public key.
  bssl::UniquePtr<EVP_PKEY> pubkey(EVP_PKEY_new_raw_public_key(EVP_PKEY_DILITHIUM3,
                                                               NULL,
                                                               dilithium3Key->pub,
                                                               DILITHIUM3_PUBLIC_KEY_BYTES));
  ASSERT_TRUE(pubkey);
  EXPECT_EQ(EVP_PKEY_DILITHIUM3, EVP_PKEY_id(pubkey.get()));

  // The public key must be extractable.
  uint8_t pub_buf[1952];
  size_t pub_len;
  ASSERT_TRUE(EVP_PKEY_get_raw_public_key(pubkey.get(), nullptr, &pub_len));
  EXPECT_EQ(pub_len, 1952u);
  ASSERT_TRUE(EVP_PKEY_get_raw_public_key(pubkey.get(), pub_buf, &pub_len));

  // The public key must encode properly.
  bssl::ScopedCBB cbb;
  uint8_t *der;
  size_t der_len;
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_public_key(cbb.get(), pubkey.get()));
  ASSERT_TRUE(CBB_finish(cbb.get(), &der, &der_len));
  bssl::UniquePtr<uint8_t> free_der(der);

  // The public key must parse properly.
  CBS cbs;
  CBS_init(&cbs, der, der_len);
  EVP_PKEY *dilithium_pkey_from_der = EVP_parse_public_key(&cbs);
  ASSERT_TRUE(dilithium_pkey_from_der);
  EXPECT_EQ(1, EVP_PKEY_cmp(dilithium_pkey, dilithium_pkey_from_der));

  // Create a private key.
  bssl::UniquePtr<EVP_PKEY> privkey(EVP_PKEY_new_raw_private_key(EVP_PKEY_DILITHIUM3,
                                                                 NULL,
                                                                 dilithium3Key->priv,
                                                                 DILITHIUM3_PRIVATE_KEY_BYTES));
  ASSERT_TRUE(privkey);
  EXPECT_EQ(EVP_PKEY_DILITHIUM3, EVP_PKEY_id(privkey.get()));

  // The private key must be extractable.
  uint8_t priv_buf[4000];
  size_t priv_len;
  ASSERT_TRUE(EVP_PKEY_get_raw_private_key(privkey.get(), nullptr, &priv_len));
  EXPECT_EQ(priv_len, 4000u);
  ASSERT_TRUE(EVP_PKEY_get_raw_private_key(privkey.get(), priv_buf, &priv_len));

  // The private key must encode properly.
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_private_key(cbb.get(), privkey.get()));
  ASSERT_TRUE(CBB_finish(cbb.get(), &der, &der_len));
  free_der.reset(der);

  // The private key must parse properly.
  CBS_init(&cbs, der, der_len);
  EVP_PKEY *dilithium_priv_from_der = EVP_parse_private_key(&cbs);
  ASSERT_TRUE(dilithium_priv_from_der);
  const DILITHIUM3_KEY *dilithium3Key_from_der = (DILITHIUM3_KEY *)(dilithium_priv_from_der->pkey.ptr);
  // The private key dilithium3Key_from_der must be equal to the original key
  EXPECT_EQ(Bytes(dilithium3Key->priv, DILITHIUM3_PRIVATE_KEY_BYTES),
            Bytes(dilithium3Key_from_der->priv, DILITHIUM3_PRIVATE_KEY_BYTES));

  EVP_PKEY_CTX_free(dilithium_pkey_ctx);
  EVP_PKEY_free(dilithium_pkey);
  EVP_PKEY_free(dilithium_pkey_from_der);
  EVP_PKEY_free(dilithium_priv_from_der);
}

TEST(Dilithium3Test, SIGOperations) {
  // Test basic functionality for Dilithium3
  // Generate a Dilithium3 key
  EVP_PKEY_CTX *dilithium_pkey_ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_DILITHIUM3, nullptr);
  ASSERT_NE(dilithium_pkey_ctx, nullptr);

  EVP_PKEY *dilithium_pkey = EVP_PKEY_new();
  ASSERT_NE(dilithium_pkey, nullptr);

  EXPECT_TRUE(EVP_PKEY_keygen_init(dilithium_pkey_ctx));
  EXPECT_TRUE(EVP_PKEY_keygen(dilithium_pkey_ctx, &dilithium_pkey));

  // sign a message
  bssl::ScopedEVP_MD_CTX md_ctx;
  uint8_t signature[DILITHIUM3_SIGNATURE_BYTES];
  size_t signature_len = DILITHIUM3_SIGNATURE_BYTES;
  std::vector<uint8_t> msg = {
      0x4a, 0x41, 0x4b, 0x45, 0x20, 0x4d, 0x41, 0x53, 0x53, 0x49,
      0x4d, 0x4f, 0x20, 0x41, 0x57, 0x53, 0x32, 0x30, 0x32, 0x32, 0x2e};
  std::vector<uint8_t> badmsg = {
      0x4a, 0x41, 0x4b, 0x45, 0x20, 0x4d, 0x41, 0x53, 0x53, 0x49,
      0x4d, 0x4f, 0x20, 0x41, 0x57, 0x53, 0x32, 0x30, 0x32, 0x31, 0x2e};

  ASSERT_TRUE(EVP_DigestSignInit(md_ctx.get(), NULL, NULL, NULL, dilithium_pkey));
  ASSERT_TRUE(EVP_DigestSign(md_ctx.get(), signature, &signature_len,
                             msg.data(), msg.size()));

  // verify the correct signed message
  ASSERT_TRUE(EVP_DigestVerify(md_ctx.get(), signature, signature_len,
                               msg.data(), msg.size()));

  // verify the signed message fails upon a bad message
  ASSERT_FALSE(EVP_DigestVerify(md_ctx.get(), signature, signature_len,
                                badmsg.data(), badmsg.size()));

  // sign the bad message
  uint8_t signature1[DILITHIUM3_SIGNATURE_BYTES];
  ASSERT_TRUE(EVP_DigestSign(md_ctx.get(), signature1, &signature_len,
                             badmsg.data(), badmsg.size()));

  // check that the two signatures are not equal
  EXPECT_NE(0, OPENSSL_memcmp(signature, signature1, signature_len));

  // verify the signed message fails upon a bad signature
  ASSERT_FALSE(EVP_DigestVerify(md_ctx.get(), signature1, signature_len,
                                msg.data(), msg.size()));

  EVP_PKEY_free(dilithium_pkey);
  EVP_PKEY_CTX_free(dilithium_pkey_ctx);
  md_ctx.Reset();
}
