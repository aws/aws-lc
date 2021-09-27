// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/crypto.h>
#include <openssl/service_indicator.h>

#include <gtest/gtest.h>

#include <openssl/aead.h>
#include <openssl/aes.h>
#include <openssl/bn.h>
#include <openssl/des.h>
#include <openssl/dh.h>
#include <openssl/digest.h>
#include <openssl/ec.h>
#include <openssl/ecdsa.h>
#include <openssl/ec_key.h>
#include <openssl/nid.h>
#include <openssl/rsa.h>
#include <openssl/sha.h>

#include "../../test/abi_test.h"
#include "../../test/file_test.h"
#include "../../test/test_util.h"

static const uint8_t kAESKey[16] = {
    'A','W','S','-','L','C','C','r','y','p','t','o',' ','K', 'e','y'};
static const uint8_t kPlaintext[64] = {
    'A','W','S','-','L','C','C','r','y','p','t','o','M','o','d','u','l','e',
    ' ','F','I','P','S',' ','K','A','T',' ','E','n','c','r','y','p','t','i',
    'o','n',' ','a','n','d',' ','D','e','c','r','y','p','t','i','o','n',' ',
    'P','l','a','i','n','t','e','x','t','!'};

#if defined(AWSLC_FIPS)
static const uint8_t kAESIV[AES_BLOCK_SIZE] = {0};

static void hex_dump(const uint8_t *in, size_t len) {
  for (size_t i = 0; i < len; i++) {
    fprintf(stderr, "%02x", in[i]);
  }
}

static int check_test(const uint8_t *expected, const uint8_t *actual,
                      size_t expected_len, const char *name) {
  if (OPENSSL_memcmp(actual, expected, expected_len) != 0) {
    fprintf(stderr, "%s failed.\nExpected: ", name);
    hex_dump(expected, expected_len);
    fprintf(stderr, "\nCalculated: ");
    hex_dump(actual, expected_len);
    fprintf(stderr, "\n");
    fflush(stderr);
    return 0;
  }
  return 1;
}

static const uint8_t kAESCBCCiphertext[64] = {
    0xa4, 0xc1, 0x5c, 0x51, 0x2a, 0x2e, 0x2a, 0xda, 0xd9, 0x02, 0x23,
    0xe7, 0xa9, 0x34, 0x9d, 0xd8, 0x5c, 0xb3, 0x65, 0x54, 0x72, 0xc8,
    0x06, 0xf1, 0x36, 0xc3, 0x97, 0x73, 0x87, 0xca, 0x44, 0x99, 0x21,
    0xb8, 0xdb, 0x93, 0x22, 0x00, 0x89, 0x7c, 0x1c, 0xea, 0x36, 0x23,
    0x18, 0xdb, 0xc1, 0x52, 0x8c, 0x23, 0x66, 0x11, 0x0d, 0xa8, 0xe9,
    0xb8, 0x08, 0x8b, 0xaa, 0x81, 0x47, 0x01, 0xa4, 0x4f
};

TEST(ServiceIndicatorTest, BasicTest) {
  int approved = AWSLC_NOT_APPROVED;

  // Call an approved service.
  bssl::ScopedEVP_AEAD_CTX aead_ctx;
  uint8_t nonce[EVP_AEAD_MAX_NONCE_LENGTH] = {0};
  uint8_t output[256];
  size_t out_len;
  ASSERT_TRUE(EVP_AEAD_CTX_init(aead_ctx.get(), EVP_aead_aes_128_gcm_randnonce(),
                                kAESKey, sizeof(kAESKey), 0, nullptr));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, EVP_AEAD_CTX_seal(aead_ctx.get(),
          output, &out_len, sizeof(output), nullptr, 0, kPlaintext, sizeof(kPlaintext), nullptr, 0));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // Call an approved service in a macro.
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_EQ(EVP_AEAD_CTX_seal(aead_ctx.get(),
          output, &out_len, sizeof(output), nullptr, 0, kPlaintext, sizeof(kPlaintext), nullptr, 0), 1));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // Call an approved service and compare expected return value.
  int return_val = 0;
  CALL_SERVICE_AND_CHECK_APPROVED(approved, return_val = EVP_AEAD_CTX_seal(aead_ctx.get(),
          output, &out_len, sizeof(output), nullptr, 0, kPlaintext, sizeof(kPlaintext), nullptr, 0));
  ASSERT_EQ(return_val, 1);
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // Call an approved service wrapped in an if statement.
  return_val = 0;
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
    if(EVP_AEAD_CTX_seal(aead_ctx.get(), output, &out_len, sizeof(output),
         nullptr, 0, kPlaintext, sizeof(kPlaintext), nullptr, 0) == 1)
    {
      return_val = 1;
    }
  );
  ASSERT_EQ(return_val, 1);
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // Fail an approved service on purpose.
  return_val = 0;
  CALL_SERVICE_AND_CHECK_APPROVED(approved, return_val = EVP_AEAD_CTX_seal(aead_ctx.get(),
          output, &out_len, 0, nullptr, 0, kPlaintext, sizeof(kPlaintext), nullptr, 0));
  ASSERT_EQ(return_val, 0);
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);

  // Fail an approved service on purpose while wrapped in an if statement.
  return_val = 0;
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
    if(EVP_AEAD_CTX_seal(aead_ctx.get(), output, &out_len, 0,
        nullptr, 0, kPlaintext, sizeof(kPlaintext), nullptr, 0) == 1)
    {
      return_val = 1;
    }
  );
  ASSERT_EQ(return_val, 0);
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);

  // Call a non-approved service.
  ASSERT_TRUE(EVP_AEAD_CTX_init(aead_ctx.get(), EVP_aead_aes_128_gcm(),
                                kAESKey, sizeof(kAESKey), 0, nullptr));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, EVP_AEAD_CTX_seal(aead_ctx.get(),
          output, &out_len, sizeof(output), nonce, EVP_AEAD_nonce_length(EVP_aead_aes_128_gcm()),
          kPlaintext, sizeof(kPlaintext), nullptr, 0));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
}

TEST(ServiceIndicatorTest, AESCBC) {
  int approved = AWSLC_NOT_APPROVED;
  AES_KEY aes_key;
  uint8_t aes_iv[16];
  uint8_t output[256];
  // AES-CBC Encryption KAT
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  ASSERT_TRUE(AES_set_encrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_cbc_encrypt(kPlaintext, output,
                              sizeof(kPlaintext), &aes_key, aes_iv, AES_ENCRYPT));
  ASSERT_TRUE(check_test(kAESCBCCiphertext, output, sizeof(kAESCBCCiphertext),
                  "AES-CBC Encryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-CBC Decryption KAT
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  ASSERT_TRUE(AES_set_decrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_cbc_encrypt(kAESCBCCiphertext, output,
                        sizeof(kAESCBCCiphertext), &aes_key, aes_iv, AES_DECRYPT));
  ASSERT_TRUE(check_test(kPlaintext, output, sizeof(kPlaintext),
                  "AES-CBC Decryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);
}

TEST(ServiceIndicatorTest, AESGCM) {
  int approved = AWSLC_NOT_APPROVED;
  bssl::ScopedEVP_AEAD_CTX aead_ctx;
  uint8_t encrypt_output[256];
  uint8_t decrypt_output[256];
  size_t out_len;
  size_t out2_len;

  ASSERT_TRUE(EVP_AEAD_CTX_init(aead_ctx.get(), EVP_aead_aes_128_gcm_randnonce(),
                                kAESKey, sizeof(kAESKey), 0, nullptr));

  CALL_SERVICE_AND_CHECK_APPROVED(approved,EVP_AEAD_CTX_seal(aead_ctx.get(),
      encrypt_output, &out_len, sizeof(encrypt_output), nullptr, 0, kPlaintext, sizeof(kPlaintext), nullptr, 0));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  CALL_SERVICE_AND_CHECK_APPROVED(approved,EVP_AEAD_CTX_open(aead_ctx.get(),
      decrypt_output, &out2_len, sizeof(decrypt_output), nullptr, 0, encrypt_output, out_len, nullptr, 0));
  ASSERT_TRUE(check_test(kPlaintext, decrypt_output, sizeof(kPlaintext),
                  "AES-GCM Decryption for Internal IVs"));
  ASSERT_EQ(approved, AWSLC_APPROVED);
}

#else
// Service indicator should not be used without FIPS turned on.
TEST(ServiceIndicatorTest, BasicTest) {
   // Reset and check the initial state and counter.
  int approved = AWSLC_NOT_APPROVED;
  uint64_t before = FIPS_service_indicator_before_call();
  ASSERT_EQ(before, (uint64_t)0);


  // Call an approved service.
  bssl::ScopedEVP_AEAD_CTX aead_ctx;
  uint8_t nonce[EVP_AEAD_MAX_NONCE_LENGTH] = {0};
  uint8_t output[256];
  size_t out_len;
  ASSERT_TRUE(EVP_AEAD_CTX_init(aead_ctx.get(), EVP_aead_aes_128_gcm_randnonce(),
                                kAESKey, sizeof(kAESKey), 0, nullptr));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, EVP_AEAD_CTX_seal(aead_ctx.get(),
          output, &out_len, sizeof(output), nullptr, 0, kPlaintext, sizeof(kPlaintext), nullptr, 0));
  // Macro should return true, to ensure FIPS/Non-FIPS compatibility.
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // Actual approval check should return false during non-FIPS.
  uint64_t after = FIPS_service_indicator_after_call();
  ASSERT_EQ(after, (uint64_t)0);
  ASSERT_FALSE(FIPS_service_indicator_check_approved(before, after));


  // Call a non-approved service.
  ASSERT_TRUE(EVP_AEAD_CTX_init(aead_ctx.get(), EVP_aead_aes_128_gcm(),
                                kAESKey, sizeof(kAESKey), 0, nullptr));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, EVP_AEAD_CTX_seal(aead_ctx.get(),
          output, &out_len, sizeof(output), nonce, EVP_AEAD_nonce_length(EVP_aead_aes_128_gcm()),
          kPlaintext, sizeof(kPlaintext), nullptr, 0));
  ASSERT_EQ(approved, AWSLC_APPROVED);
}
#endif // AWSLC_FIPS


