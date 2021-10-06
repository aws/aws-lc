// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0


#include <gtest/gtest.h>

#include <openssl/aead.h>
#include <openssl/aes.h>
#include <openssl/bn.h>
#include <openssl/cipher.h>
#include <openssl/crypto.h>
#include <openssl/des.h>
#include <openssl/dh.h>
#include <openssl/digest.h>
#include <openssl/ec.h>
#include <openssl/ecdsa.h>
#include <openssl/ec_key.h>
#include <openssl/nid.h>
#include <openssl/rsa.h>
#include <openssl/service_indicator.h>
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

static void DoCipher(EVP_CIPHER_CTX *ctx, std::vector<uint8_t> *out,
                     bssl::Span<const uint8_t> in, int expect_approved) {
  int approved = AWSLC_NOT_APPROVED;
  size_t max_out = in.size();
  if (EVP_CIPHER_CTX_encrypting(ctx)) {
    unsigned block_size = EVP_CIPHER_CTX_block_size(ctx);
    max_out += block_size - (max_out % block_size);
  }
  out->resize(max_out);

  size_t total = 0;
  int len;
  EXPECT_TRUE(EVP_CipherUpdate(ctx, out->data(), &len, in.data(), in.size()));
  total += static_cast<size_t>(len);
  // Check if the overall service is approved by checking |EVP_CipherFinal_ex|,
  // which should be the last part of the service.
  CALL_SERVICE_AND_CHECK_APPROVED(approved,EXPECT_TRUE(
                    EVP_CipherFinal_ex(ctx, out->data() + total, &len)));
  total += static_cast<size_t>(len);
  ASSERT_EQ(approved, expect_approved);

  out->resize(total);
}

static void TestOperation(const EVP_CIPHER *cipher, bool encrypt,
                          const std::vector<uint8_t> &key,
                          const std::vector<uint8_t> &plaintext,
                          const std::vector<uint8_t> &ciphertext,
                          int expect_approved) {
  int approved = AWSLC_NOT_APPROVED;
  const std::vector<uint8_t> *in, *out;
  if (encrypt) {
    in = &plaintext;
    out = &ciphertext;
  } else {
    in = &ciphertext;
    out = &plaintext;
  }

  bssl::ScopedEVP_CIPHER_CTX ctx;
  // Test running the EVP_Cipher interfaces one by one directly, and check
  // |EVP_CipherFinal_ex| for approval at the end.
  ASSERT_TRUE(EVP_CipherInit_ex(ctx.get(), cipher, nullptr, nullptr,
                                    nullptr, encrypt ? 1 : 0));
  std::vector<uint8_t> iv( kAESIV,kAESIV + EVP_CIPHER_CTX_iv_length(ctx.get()));
  ASSERT_EQ(iv.size(), EVP_CIPHER_CTX_iv_length(ctx.get()));

  // For each of the ciphers we test, the output size matches the input size.
  ASSERT_EQ(in->size(), out->size());
  ASSERT_TRUE(EVP_CIPHER_CTX_set_key_length(ctx.get(), key.size()));
  ASSERT_TRUE(EVP_CipherInit_ex(ctx.get(), cipher, nullptr, key.data(), iv.data(), encrypt ? 1 : 0));
  ASSERT_TRUE(EVP_CIPHER_CTX_set_padding(ctx.get(), 0));
  std::vector<uint8_t> result;
  DoCipher(ctx.get(), &result, *in, expect_approved);
  ASSERT_EQ(Bytes(*out), Bytes(result));


  // Test using the one-shot |EVP_Cipher| function for approval.
  bssl::ScopedEVP_CIPHER_CTX ctx1;
  uint8_t output[256];
  ASSERT_TRUE(EVP_CipherInit_ex(ctx1.get(), cipher, nullptr, key.data(), iv.data(), encrypt ? 1 : 0));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, EVP_Cipher(ctx1.get(), output,
                                               in->data(), in->size()));
  ASSERT_TRUE(check_test(out->data(), output, in->size(), "EVP_Cipher Encryption KAT"));
}

// AES-OFB is not an approved service, and is only used to test we are not
// validating un-approved services correctly.
static const uint8_t kAESOFBCiphertext[64] = {
    0x49, 0xf5, 0x6a, 0x7d, 0x3e, 0xd7, 0xb2, 0x47, 0x35, 0xca, 0x54,
    0xf5, 0xf1, 0xb8, 0xd1, 0x48, 0x8e, 0x47, 0x09, 0x95, 0xd5, 0xa0,
    0xc6, 0xa3, 0xe4, 0x94, 0xaf, 0xd4, 0x1b, 0x64, 0x25, 0x65, 0x28,
    0x9e, 0x82, 0xba, 0x92, 0xca, 0x75, 0xb3, 0xf3, 0x78, 0x44, 0x87,
    0xd6, 0x11, 0xf9, 0x22, 0xa3, 0xf3, 0xc6, 0x1d, 0x30, 0x00, 0x5b,
    0x77, 0x18, 0x38, 0x39, 0x08, 0x5e, 0x0a, 0x56, 0x6b
};

static const uint8_t kAESECBCiphertext[64] = {
    0xa4, 0xc1, 0x5c, 0x51, 0x2a, 0x2e, 0x2a, 0xda, 0xd9, 0x02, 0x23,
    0xe7, 0xa9, 0x34, 0x9d, 0xd8, 0x15, 0xc5, 0xf5, 0x55, 0x8e, 0xb0,
    0x29, 0x95, 0x48, 0x6c, 0x7f, 0xa9, 0x47, 0x19, 0x0b, 0x54, 0xe5,
    0x0f, 0x05, 0x76, 0xbb, 0xd0, 0x1a, 0x6c, 0xab, 0xe9, 0xfd, 0x5b,
    0xd8, 0x0b, 0x0a, 0xbd, 0x7f, 0xea, 0xda, 0x52, 0x07, 0x65, 0x13,
    0x6c, 0xbe, 0xfc, 0x36, 0x82, 0x4b, 0x6a, 0xc3, 0xd5
};

static const uint8_t kAESCBCCiphertext[64] = {
    0xa4, 0xc1, 0x5c, 0x51, 0x2a, 0x2e, 0x2a, 0xda, 0xd9, 0x02, 0x23,
    0xe7, 0xa9, 0x34, 0x9d, 0xd8, 0x5c, 0xb3, 0x65, 0x54, 0x72, 0xc8,
    0x06, 0xf1, 0x36, 0xc3, 0x97, 0x73, 0x87, 0xca, 0x44, 0x99, 0x21,
    0xb8, 0xdb, 0x93, 0x22, 0x00, 0x89, 0x7c, 0x1c, 0xea, 0x36, 0x23,
    0x18, 0xdb, 0xc1, 0x52, 0x8c, 0x23, 0x66, 0x11, 0x0d, 0xa8, 0xe9,
    0xb8, 0x08, 0x8b, 0xaa, 0x81, 0x47, 0x01, 0xa4, 0x4f
};

static const uint8_t kAESCTRCiphertext[64] = {
    0x49, 0xf5, 0x6a, 0x7d, 0x3e, 0xd7, 0xb2, 0x47, 0x35, 0xca, 0x54,
    0xf5, 0xf1, 0xb8, 0xd1, 0x48, 0xb0, 0x18, 0xc4, 0x5e, 0xeb, 0x42,
    0xfd, 0x10, 0x49, 0x1f, 0x2b, 0x11, 0xe9, 0xb0, 0x07, 0xa4, 0x00,
    0x56, 0xec, 0x25, 0x53, 0x4d, 0x70, 0x98, 0x38, 0x85, 0x5d, 0x54,
    0xab, 0x2c, 0x19, 0x13, 0x6d, 0xf3, 0x0e, 0x6f, 0x48, 0x2f, 0xab,
    0xe1, 0x82, 0xd4, 0x30, 0xa9, 0x16, 0x73, 0x93, 0xc3
};

static const uint8_t kAESCCMCiphertext[68] = {
    0x7a, 0x02, 0x5d, 0x48, 0x02, 0x44, 0x78, 0x7f, 0xb4, 0x71, 0x74,
    0x7b, 0xec, 0x4d, 0x90, 0x29, 0x7b, 0xa7, 0x65, 0xbb, 0x3e, 0x80,
    0x41, 0x7e, 0xab, 0xb4, 0x58, 0x22, 0x4f, 0x86, 0xcd, 0xcc, 0xc2,
    0x12, 0xeb, 0x36, 0x39, 0x89, 0xe3, 0x66, 0x2a, 0xbf, 0xe3, 0x6c,
    0x95, 0x60, 0x13, 0x9e, 0x93, 0xcc, 0xb4, 0x06, 0xbe, 0xaf, 0x3f,
    0xba, 0x13, 0x73, 0x09, 0x92, 0xd1, 0x80, 0x73, 0xb3, 0xc3, 0xa3,
    0xa4, 0x8b
};

static const uint8_t kAESKWCiphertext[72] = {
    0x44, 0xec, 0x7d, 0x92, 0x2c, 0x9f, 0xf3, 0xe8, 0xac, 0xb1, 0xea,
    0x3d, 0x0a, 0xc7, 0x51, 0x27, 0xe8, 0x03, 0x11, 0x78, 0xe5, 0xaf,
    0x8d, 0xb1, 0x70, 0x96, 0x2e, 0xfa, 0x05, 0x48, 0x48, 0x99, 0x1a,
    0x58, 0xcc, 0xfe, 0x11, 0x36, 0x5d, 0x49, 0x98, 0x1e, 0xbb, 0xd6,
    0x0b, 0xf5, 0xb9, 0x64, 0xa4, 0x30, 0x3e, 0x60, 0xf6, 0xc5, 0xff,
    0x82, 0x30, 0x9a, 0xa7, 0x48, 0x82, 0xe2, 0x00, 0xc1, 0xe9, 0xc2,
    0x73, 0x6f, 0xbc, 0x89, 0x66, 0x9d
};

static const uint8_t kAESKWPCiphertext[72] = {
    0x29, 0x5e, 0xb9, 0xea, 0x96, 0xa7, 0xa5, 0xca, 0xfa, 0xeb, 0xda,
    0x78, 0x13, 0xea, 0x83, 0xca, 0x41, 0xdb, 0x4d, 0x36, 0x7d, 0x39,
    0x8a, 0xd6, 0xef, 0xd3, 0xd2, 0x2d, 0x3a, 0xc8, 0x55, 0xc8, 0x73,
    0xd7, 0x79, 0x55, 0xad, 0xc0, 0xce, 0xad, 0x12, 0x54, 0x51, 0xf0,
    0x70, 0x76, 0xff, 0xe7, 0x0c, 0xb2, 0x8e, 0xdd, 0xb6, 0x9a, 0x27,
    0x74, 0x98, 0x28, 0xe0, 0xfa, 0x11, 0xe6, 0x3f, 0x86, 0x93, 0x23,
    0xf8, 0x0d, 0xcb, 0xaf, 0x2b, 0xb7
};

struct EVP_TestVector {
  const EVP_CIPHER *cipher;
  const uint8_t *expected_ciphertext;
  int cipher_text_length;
  bool has_iv;
  int expect_approved;
} nTestVectors[] = {
  { EVP_aes_128_ecb(), kAESECBCiphertext, 64, false, AWSLC_APPROVED },
  { EVP_aes_128_cbc(), kAESCBCCiphertext, 64, true, AWSLC_APPROVED },
  { EVP_aes_128_ctr(), kAESCTRCiphertext, 64, true, AWSLC_APPROVED },
  { EVP_aes_128_ofb(), kAESOFBCiphertext, 64, true, AWSLC_NOT_APPROVED }
};

class EVP_ServiceIndicatorTest : public testing::TestWithParam<EVP_TestVector> {};

INSTANTIATE_TEST_SUITE_P(All, EVP_ServiceIndicatorTest, testing::ValuesIn(nTestVectors));

TEST_P(EVP_ServiceIndicatorTest, EVP_Ciphers) {
  const EVP_TestVector &t = GetParam();

  const EVP_CIPHER *cipher = t.cipher;
  std::vector<uint8_t> key(kAESKey, kAESKey + sizeof(kAESKey));
  std::vector<uint8_t> plaintext(kPlaintext, kPlaintext + sizeof(kPlaintext));
  std::vector<uint8_t> ciphertext(t.expected_ciphertext, t.expected_ciphertext + t.cipher_text_length);

  TestOperation(cipher, true /* encrypt */, key, plaintext, ciphertext, t.expect_approved);
  TestOperation(cipher, false /* decrypt */, key, plaintext, ciphertext, t.expect_approved);
}


TEST(ServiceIndicatorTest, BasicTest) {
  int approved = AWSLC_NOT_APPROVED;

  bssl::ScopedEVP_AEAD_CTX aead_ctx;
  AES_KEY aes_key;
  uint8_t aes_iv[16];
  uint8_t output[256];
  size_t out_len;
  int num = 0;

  // Call an approved service.
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
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  ASSERT_TRUE(AES_set_encrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key) == 0);
  ASSERT_TRUE(EVP_AEAD_CTX_init(aead_ctx.get(), EVP_aead_aes_128_gcm(),
                                kAESKey, sizeof(kAESKey), 0, nullptr));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_ofb128_encrypt(kPlaintext, output,
                                   sizeof(kPlaintext), &aes_key, aes_iv, &num));
  ASSERT_TRUE(check_test(kAESOFBCiphertext, output, sizeof(kAESOFBCiphertext),
                         "AES-OFB Encryption KAT"));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
}

TEST(ServiceIndicatorTest, AESECB) {
  int approved = AWSLC_NOT_APPROVED;

  AES_KEY aes_key;
  uint8_t output[256];

  // AES-ECB Encryption KAT
  ASSERT_EQ(AES_set_encrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key),0);
  // AES_ecb_encrypt encrypts (or decrypts) a single, 16 byte block from in to out.
  for (size_t j = 0; j < sizeof(kPlaintext) / AES_BLOCK_SIZE; j++) {
    CALL_SERVICE_AND_CHECK_APPROVED(approved,
      AES_ecb_encrypt(&kPlaintext[j * AES_BLOCK_SIZE], &output[j * AES_BLOCK_SIZE], &aes_key, AES_ENCRYPT));
    ASSERT_EQ(approved, AWSLC_APPROVED);
  }
  ASSERT_TRUE(check_test(kAESECBCiphertext, output, sizeof(kAESECBCiphertext),
                         "AES-ECB Encryption KAT"));

  // AES-ECB Decryption KAT
  ASSERT_EQ(AES_set_decrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key),0);
  for (size_t j = 0; j < sizeof(kPlaintext) / AES_BLOCK_SIZE; j++) {
    CALL_SERVICE_AND_CHECK_APPROVED(approved,
      AES_ecb_encrypt(&kAESECBCiphertext[j * AES_BLOCK_SIZE], &output[j * AES_BLOCK_SIZE], &aes_key, AES_DECRYPT));
    ASSERT_EQ(approved, AWSLC_APPROVED);
  }
  ASSERT_TRUE(check_test(kPlaintext, output, sizeof(kPlaintext),
                         "AES-ECB Decryption KAT"));
}

TEST(ServiceIndicatorTest, AESCBC) {
  int approved = AWSLC_NOT_APPROVED;
  AES_KEY aes_key;
  uint8_t aes_iv[16];
  uint8_t output[256];
  // AES-CBC Encryption KAT
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  ASSERT_EQ(AES_set_encrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key), 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_cbc_encrypt(kPlaintext, output,
                              sizeof(kPlaintext), &aes_key, aes_iv, AES_ENCRYPT));
  ASSERT_TRUE(check_test(kAESCBCCiphertext, output, sizeof(kAESCBCCiphertext),
                         "AES-CBC Encryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-CBC Decryption KAT
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  ASSERT_EQ(AES_set_decrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key), 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_cbc_encrypt(kAESCBCCiphertext, output,
                        sizeof(kAESCBCCiphertext), &aes_key, aes_iv, AES_DECRYPT));
  ASSERT_TRUE(check_test(kPlaintext, output, sizeof(kPlaintext),
                         "AES-CBC Decryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);
}

TEST(ServiceIndicatorTest, AESCTR) {
  int approved = AWSLC_NOT_APPROVED;

  AES_KEY aes_key;
  uint8_t aes_iv[16];
  uint8_t output[256];
  unsigned num = 0;
  uint8_t ecount_buf[AES_BLOCK_SIZE];

  // AES-CTR Encryption KAT
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  ASSERT_EQ(AES_set_encrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key),0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved,AES_ctr128_encrypt(kPlaintext, output,
                             sizeof(kPlaintext), &aes_key, aes_iv, ecount_buf, &num));
  ASSERT_TRUE(check_test(kAESCTRCiphertext, output, sizeof(kAESCTRCiphertext),
                         "AES-CTR Encryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-CTR Decryption KAT
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  CALL_SERVICE_AND_CHECK_APPROVED(approved,AES_ctr128_encrypt(kAESCTRCiphertext, output,
                         sizeof(kAESCTRCiphertext), &aes_key, aes_iv, ecount_buf, &num));
  ASSERT_TRUE(check_test(kPlaintext, output, sizeof(kPlaintext),
                         "AES-CTR Decryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);
}

TEST(ServiceIndicatorTest, AESGCM) {
  int approved = AWSLC_NOT_APPROVED;
  bssl::ScopedEVP_AEAD_CTX aead_ctx;
  uint8_t nonce[EVP_AEAD_MAX_NONCE_LENGTH] = {0};
  uint8_t encrypt_output[256];
  uint8_t decrypt_output[256];
  size_t out_len;
  size_t out2_len;

  // Call approved internal IV usage of AES-GCM.
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

  // Call non-approved external IV usage of AES-GCM.
  ASSERT_TRUE(EVP_AEAD_CTX_init(aead_ctx.get(), EVP_aead_aes_128_gcm(),
                                kAESKey, sizeof(kAESKey), 0, nullptr));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, EVP_AEAD_CTX_seal(aead_ctx.get(),
      encrypt_output, &out_len, sizeof(encrypt_output), nonce, EVP_AEAD_nonce_length(EVP_aead_aes_128_gcm()),
          kPlaintext, sizeof(kPlaintext), nullptr, 0));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
}

TEST(ServiceIndicatorTest, AESCCM) {
  int approved = AWSLC_NOT_APPROVED;

  bssl::ScopedEVP_AEAD_CTX aead_ctx;
  uint8_t nonce[EVP_AEAD_MAX_NONCE_LENGTH];
  uint8_t output[256];
  size_t out_len;

  OPENSSL_memset(nonce, 0, sizeof(nonce));
  ASSERT_TRUE(EVP_AEAD_CTX_init(aead_ctx.get(), EVP_aead_aes_128_ccm_bluetooth(),
                                kAESKey, sizeof(kAESKey), EVP_AEAD_DEFAULT_TAG_LENGTH, nullptr));

  // AES-CCM Encryption
  CALL_SERVICE_AND_CHECK_APPROVED(approved,EVP_AEAD_CTX_seal(aead_ctx.get(),
       output, &out_len, sizeof(output), nonce, EVP_AEAD_nonce_length(EVP_aead_aes_128_ccm_bluetooth()),
       kPlaintext, sizeof(kPlaintext), nullptr, 0));
  ASSERT_TRUE(check_test(kAESCCMCiphertext, output, out_len, "AES-CCM Encryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-CCM Decryption
  CALL_SERVICE_AND_CHECK_APPROVED(approved,EVP_AEAD_CTX_open(aead_ctx.get(),
       output, &out_len, sizeof(output), nonce, EVP_AEAD_nonce_length(EVP_aead_aes_128_ccm_bluetooth()),
       kAESCCMCiphertext, sizeof(kAESCCMCiphertext), nullptr, 0));
  ASSERT_TRUE(check_test(kPlaintext, output, out_len, "AES-CCM Decryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);
}

TEST(ServiceIndicatorTest, AESKW) {
  int approved = AWSLC_NOT_APPROVED;

  AES_KEY aes_key;
  uint8_t output[256];
  size_t outlen;

  // AES-KW Encryption KAT
  ASSERT_EQ(AES_set_encrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key),0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved,outlen = AES_wrap_key(&aes_key, nullptr,
                                    output, kPlaintext, sizeof(kPlaintext)));
  ASSERT_TRUE(check_test(kAESKWCiphertext, output, outlen, "AES-KW Encryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-KW Decryption KAT
  ASSERT_EQ(AES_set_decrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key),0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved,outlen = AES_unwrap_key(&aes_key, nullptr,
                                    output, kAESKWCiphertext, sizeof(kAESKWCiphertext)));
  ASSERT_TRUE(check_test(kPlaintext, output, outlen, "AES-KW Decryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);
}

TEST(ServiceIndicatorTest, AESKWP) {
  int approved = AWSLC_NOT_APPROVED;

  AES_KEY aes_key;
  uint8_t output[256];
  size_t outlen;
  // AES-KWP Encryption KAT
  memset(output, 0, 256);
  ASSERT_EQ(AES_set_encrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key),0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved,ASSERT_TRUE(AES_wrap_key_padded(&aes_key,
              output, &outlen, sizeof(kPlaintext) + 15, kPlaintext, sizeof(kPlaintext))));
  ASSERT_TRUE(check_test(kAESKWPCiphertext, output, outlen, "AES-KWP Encryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-KWP Decryption KAT
  ASSERT_EQ(AES_set_decrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key),0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(AES_unwrap_key_padded(&aes_key,
             output, &outlen, sizeof(kAESKWPCiphertext), kAESKWPCiphertext, sizeof(kAESKWPCiphertext))));
  ASSERT_TRUE(check_test(kPlaintext, output, outlen, "AES-KWP Decryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);
}

#else
// Service indicator calls should not be used in non-FIPS builds. However, if
// used, the macro |CALL_SERVICE_AND_CHECK_APPROVED| will return
// |AWSLC_APPROVED|, but the direct calls to |FIPS_service_indicator_xxx|
// will not indicate an approved state.
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
  ASSERT_TRUE(FIPS_service_indicator_check_approved(before, after));


  // Call a non-approved service.
  ASSERT_TRUE(EVP_AEAD_CTX_init(aead_ctx.get(), EVP_aead_aes_128_gcm(),
                                kAESKey, sizeof(kAESKey), 0, nullptr));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, EVP_AEAD_CTX_seal(aead_ctx.get(),
          output, &out_len, sizeof(output), nonce, EVP_AEAD_nonce_length(EVP_aead_aes_128_gcm()),
          kPlaintext, sizeof(kPlaintext), nullptr, 0));
  ASSERT_EQ(approved, AWSLC_APPROVED);
}
#endif // AWSLC_FIPS


