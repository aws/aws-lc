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
    'B','o','r','i','n','g','C','r','y','p','t','o',' ','K', 'e','y'};
static const uint8_t kPlaintext[64] = {
    'B','o','r','i','n','g','C','r','y','p','t','o','M','o','d','u','l','e',
    ' ','F','I','P','S',' ','K','A','T',' ','E','n','c','r','y','p','t','i',
    'o','n',' ','a','n','d',' ','D','e','c','r','y','p','t','i','o','n',' ',
    'P','l','a','i','n','t','e','x','t','!'};

#if defined(AWSLC_FIPS)
static const uint8_t kAESIV[16] = {0};

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
    0x87, 0x2d, 0x98, 0xc2, 0xcc, 0x31, 0x5b, 0x41, 0xe0, 0xfa, 0x7b,
    0x0a, 0x71, 0xc0, 0x42, 0xbf, 0x4f, 0x61, 0xd0, 0x0d, 0x58, 0x8c,
    0xf7, 0x05, 0xfb, 0x94, 0x89, 0xd3, 0xbc, 0xaa, 0x1a, 0x50, 0x45,
    0x1f, 0xc3, 0x8c, 0xb8, 0x98, 0x86, 0xa3, 0xe3, 0x6c, 0xfc, 0xad,
    0x3a, 0xb5, 0x59, 0x27, 0x7d, 0x21, 0x07, 0xca, 0x4c, 0x1d, 0x55,
    0x34, 0xdd, 0x5a, 0x2d, 0xc4, 0xb4, 0xf5, 0xa8,
#if !defined(BORINGSSL_FIPS_BREAK_AES_CBC)
    0x35
#else
    0x00
#endif
};

TEST(ServiceIndicatorTest, BasicTest) {
  // Reset and check the initial state and counter.
  //ASSERT_TRUE(awslc_fips_service_indicator_reset_state());
  int approved = 0;

  uint64_t counter = awslc_fips_service_indicator_get_counter();
  uint32_t serviceID = awslc_fips_service_indicator_get_serviceID();
  ASSERT_EQ(counter, (uint64_t)0);
  ASSERT_EQ(serviceID, FIPS_APPROVED_NO_STATE);

  // Call an approved service.
  bssl::ScopedEVP_AEAD_CTX aead_ctx;
  uint8_t output[256];
  size_t out_len;
  ASSERT_TRUE(EVP_AEAD_CTX_init(aead_ctx.get(), EVP_aead_aes_128_gcm_randnonce(),
                                kAESKey, sizeof(kAESKey), 0, nullptr));
  IS_FIPS_APPROVED_CALL_SERVICE(approved, EVP_AEAD_CTX_seal(aead_ctx.get(),
          output, &out_len, sizeof(output), nullptr, 0, kPlaintext, sizeof(kPlaintext), nullptr, 0));
  ASSERT_TRUE(approved);

  // Check state and counter after using an approved service.
  counter = awslc_fips_service_indicator_get_counter();
  serviceID = awslc_fips_service_indicator_get_serviceID();
  ASSERT_EQ(counter,(uint64_t)1);
  ASSERT_EQ(serviceID, FIPS_APPROVED_EVP_AES_128_GCM);
}

TEST(ServiceIndicatorTest, AESCBC) {
  int approved = 0;
  uint32_t serviceID = 0;

  AES_KEY aes_key;
  uint8_t aes_iv[16];
  uint8_t output[256];

  // AES-CBC Encryption KAT
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  if (AES_set_encrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key) != 0) {
    fprintf(stderr, "AES_set_encrypt_key failed.\n");
    return;
  }

  IS_FIPS_APPROVED_CALL_SERVICE(approved,AES_cbc_encrypt(kPlaintext, output,
                              sizeof(kPlaintext), &aes_key, aes_iv, AES_ENCRYPT));
  if (!check_test(kAESCBCCiphertext, output, sizeof(kAESCBCCiphertext),
                  "AES-CBC Encryption KAT")) {
    return;
  }
  ASSERT_TRUE(approved);
  serviceID = awslc_fips_service_indicator_get_serviceID();
  ASSERT_EQ(serviceID, FIPS_APPROVED_EVP_AES_128_CBC);

  // AES-CBC Decryption KAT
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  if (AES_set_decrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key) != 0) {
    fprintf(stderr, "AES_set_decrypt_key failed.\n");
    return;
  }

  IS_FIPS_APPROVED_CALL_SERVICE(approved,AES_cbc_encrypt(kAESCBCCiphertext, output,
                        sizeof(kAESCBCCiphertext), &aes_key, aes_iv, AES_DECRYPT));
  if (!check_test(kPlaintext, output, sizeof(kPlaintext),
                  "AES-CBC Decryption KAT")) {
    return;
  }
  ASSERT_TRUE(approved);
  serviceID = awslc_fips_service_indicator_get_serviceID();
  ASSERT_EQ(serviceID, FIPS_APPROVED_EVP_AES_128_CBC);
}

TEST(ServiceIndicatorTest, AESGCM) {
  int approved = 0;
  uint32_t serviceID = 0;

  bssl::ScopedEVP_AEAD_CTX aead_ctx;

  uint8_t encrypt_output[256];
  uint8_t decrypt_output[256];
  size_t out_len;
  size_t out2_len;

  ASSERT_TRUE(EVP_AEAD_CTX_init(aead_ctx.get(), EVP_aead_aes_128_gcm_randnonce(),
                                kAESKey, sizeof(kAESKey), 0, nullptr));

  // AES-GCM Encryption
  IS_FIPS_APPROVED_CALL_SERVICE(approved,EVP_AEAD_CTX_seal(aead_ctx.get(),
      encrypt_output, &out_len, sizeof(encrypt_output), nullptr, 0, kPlaintext, sizeof(kPlaintext), nullptr, 0));
  ASSERT_TRUE(approved);
  serviceID = awslc_fips_service_indicator_get_serviceID();
  ASSERT_EQ(serviceID, FIPS_APPROVED_EVP_AES_128_GCM);
  
  // AES-GCM Decryption
  IS_FIPS_APPROVED_CALL_SERVICE(approved,EVP_AEAD_CTX_open(aead_ctx.get(),
      decrypt_output, &out2_len, sizeof(decrypt_output), nullptr, 0, encrypt_output, out_len, nullptr, 0));
  if (!check_test(kPlaintext, decrypt_output, sizeof(kPlaintext),
                  "AES-GCM Decryption for Internal IVs")) {
    return;
  }
  ASSERT_TRUE(approved);
  serviceID = awslc_fips_service_indicator_get_serviceID();
  ASSERT_EQ(serviceID, FIPS_APPROVED_EVP_AES_128_GCM);
}

#else
// Service indicator should not be used without FIPS turned on.
TEST(ServiceIndicatorTest, BasicTest) {
   // Reset and check the initial state and counter.
  ASSERT_FALSE(awslc_fips_service_indicator_reset_state());
  int approved = 0;
  uint64_t counter = awslc_fips_service_indicator_get_counter();
  uint32_t serviceID = awslc_fips_service_indicator_get_serviceID();
  ASSERT_EQ(counter, (uint64_t)0);
  ASSERT_EQ(serviceID, (uint32_t)0);

  // Call an approved service.
  bssl::ScopedEVP_AEAD_CTX aead_ctx;
  uint8_t encrypt_output[256];
  size_t out_len;
  ASSERT_TRUE(EVP_AEAD_CTX_init(aead_ctx.get(), EVP_aead_aes_128_gcm_randnonce(),
                                kAESKey, sizeof(kAESKey), 0, nullptr));
  IS_FIPS_APPROVED_CALL_SERVICE(approved, EVP_AEAD_CTX_seal(aead_ctx.get(),
         encrypt_output, &out_len, sizeof(encrypt_output), nullptr, 0, kPlaintext, sizeof(kPlaintext), nullptr, 0));
  ASSERT_FALSE(approved);

  // Check state and counter after using an approved service.
  counter = awslc_fips_service_indicator_get_counter();
  serviceID = awslc_fips_service_indicator_get_serviceID();
  ASSERT_EQ(counter,(uint64_t)0);
  ASSERT_EQ(serviceID, (uint32_t)0);
}
#endif // AWSLC_FIPS


