// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0


#include <gtest/gtest.h>

#include <openssl/aead.h>
#include <openssl/aes.h>
#include <openssl/bn.h>
#include <openssl/cipher.h>
#include <openssl/cmac.h>
#include <openssl/crypto.h>
#include <openssl/dh.h>
#include <openssl/digest.h>
#include <openssl/ec.h>
#include <openssl/ecdh.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/md4.h>
#include <openssl/md5.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>
#include <openssl/service_indicator.h>
#include <openssl/err.h>

#include "../../test/abi_test.h"
#include "../../test/test_util.h"
#include "../bn/internal.h"
#include "../rand/internal.h"
#include "../tls/internal.h"

namespace awslc {
  template <typename T>
  class TestWithNoErrors : public testing::TestWithParam<T> {
    void TearDown() override {
      ASSERT_EQ(ERR_get_error(), 0u);
    }
  };
}

static const uint8_t kAESKey[16] = {
    'A','W','S','-','L','C','C','r','y','p','t','o',' ','K', 'e','y'};
static const uint8_t kPlaintext[64] = {
    'A','W','S','-','L','C','C','r','y','p','t','o','M','o','d','u','l','e',
    ' ','F','I','P','S',' ','K','A','T',' ','E','n','c','r','y','p','t','i',
    'o','n',' ','a','n','d',' ','D','e','c','r','y','p','t','i','o','n',' ',
    'P','l','a','i','n','t','e','x','t','!'};

#if defined(AWSLC_FIPS)
static const uint8_t kAESKey_192[24] = {
    'A','W','S','-','L','C','C','r','y','p','t','o',' ','1', '9','2', '-','b',
    'i','t',' ','K','e','y'
};

static const uint8_t kAESKey_256[32] = {
    'A','W','S','-','L','C','C','r','y','p','t','o',' ','2', '5','6', '-','b',
    'i','t',' ','L','o','n','g',' ','K','e','y','!','!','!'
};

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

static DH *self_test_dh() {
  DH *dh = DH_get_rfc7919_2048();
  if (!dh) {
    return nullptr;
  }

  BIGNUM *priv = BN_new();
  if (!priv) {
    goto err;
  }

  // kFFDHE2048PrivateKeyData is a 225-bit value. (225 because that's the
  // minimum private key size in
  // https://tools.ietf.org/html/rfc7919#appendix-A.1.)
  static const BN_ULONG kFFDHE2048PrivateKeyData[] = {
      TOBN(0x187be36b, 0xd38a4fa1),
      TOBN(0x0a152f39, 0x6458f3b8),
      TOBN(0x0570187e, 0xc422eeb7),
      TOBN(0x00000001, 0x91173f2a),
  };

  priv->d = (BN_ULONG *)kFFDHE2048PrivateKeyData;
  priv->width = OPENSSL_ARRAY_SIZE(kFFDHE2048PrivateKeyData);
  priv->dmax = OPENSSL_ARRAY_SIZE(kFFDHE2048PrivateKeyData);
  priv->neg = 0;
  priv->flags |= BN_FLG_STATIC_DATA;

  if (!DH_set0_key(dh, nullptr, priv)) {
    goto err;
  }
  return dh;

  err:
  BN_free(priv);
  DH_free(dh);
  return nullptr;
}

static void DoEncryptFinal(EVP_CIPHER_CTX *ctx, std::vector<uint8_t> *out,
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
  ASSERT_TRUE(EVP_CipherUpdate(ctx, out->data(), &len, in.data(), in.size()));
  total += static_cast<size_t>(len);
  // Check if the overall service is approved by checking |EVP_EncryptFinal_ex|
  // or |EVP_DecryptFinal_ex|, which should be the last part of the service.
  if (ctx->encrypt) {
    CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_EncryptFinal_ex(ctx, out->data() + total, &len)));
  } else {
    CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_DecryptFinal_ex(ctx, out->data() + total, &len)));
  }
  total += static_cast<size_t>(len);
  ASSERT_EQ(approved, expect_approved);
  out->resize(total);
}

static void DoCipherFinal(EVP_CIPHER_CTX *ctx, std::vector<uint8_t> *out,
                     bssl::Span<const uint8_t> in, int expect_approved) {
  int approved = AWSLC_NOT_APPROVED;
  size_t max_out = in.size();
  if (EVP_CIPHER_CTX_encrypting(ctx)) {
    unsigned block_size = EVP_CIPHER_CTX_block_size(ctx);
    max_out += block_size - (max_out % block_size);
  }
  out->resize(max_out);

  size_t total = 0;
  int len = 0;
  ASSERT_TRUE(EVP_CipherUpdate(ctx, out->data(), &len, in.data(), in.size()));
  total += static_cast<size_t>(len);
  // Check if the overall service is approved by checking |EVP_CipherFinal_ex|,
  // which should be the last part of the service.
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(
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
  // |EVP_EncryptFinal_ex| and |EVP_DecryptFinal_ex| for approval at the end.
  ASSERT_TRUE(EVP_CipherInit_ex(ctx.get(), cipher, nullptr, nullptr,
                                    nullptr, encrypt ? 1 : 0));
  std::vector<uint8_t> iv(kAESIV, kAESIV + EVP_CIPHER_CTX_iv_length(ctx.get()));
  ASSERT_EQ(iv.size(), EVP_CIPHER_CTX_iv_length(ctx.get()));

  ASSERT_TRUE(EVP_CIPHER_CTX_set_key_length(ctx.get(), key.size()));
  ASSERT_TRUE(EVP_CipherInit_ex(ctx.get(), cipher, nullptr, key.data(), iv.data(), encrypt ? 1 : 0));
  ASSERT_TRUE(EVP_CIPHER_CTX_set_padding(ctx.get(), 0));
  std::vector<uint8_t> encrypt_result;
  DoEncryptFinal(ctx.get(), &encrypt_result, *in, expect_approved);
  ASSERT_EQ(Bytes(*out), Bytes(encrypt_result));

  bssl::ScopedEVP_CIPHER_CTX ctx1;
  // Test running the EVP_Cipher interfaces one by one directly, and check
  // |EVP_CipherFinal_ex| for approval at the end.
  ASSERT_TRUE(EVP_CipherInit_ex(ctx1.get(), cipher, nullptr, nullptr,
                                    nullptr, encrypt ? 1 : 0));
  ASSERT_EQ(iv.size(), EVP_CIPHER_CTX_iv_length(ctx1.get()));

  ASSERT_TRUE(EVP_CIPHER_CTX_set_key_length(ctx1.get(), key.size()));
  ASSERT_TRUE(EVP_CipherInit_ex(ctx1.get(), cipher, nullptr, key.data(), iv.data(), encrypt ? 1 : 0));
  ASSERT_TRUE(EVP_CIPHER_CTX_set_padding(ctx1.get(), 0));
  std::vector<uint8_t> final_result;
  DoCipherFinal(ctx1.get(), &final_result, *in, expect_approved);
  ASSERT_EQ(Bytes(*out), Bytes(final_result));


  // Test using the one-shot |EVP_Cipher| function for approval.
  bssl::ScopedEVP_CIPHER_CTX ctx2;
  uint8_t output[256];
  ASSERT_TRUE(EVP_CipherInit_ex(ctx2.get(), cipher, nullptr, key.data(), iv.data(), encrypt ? 1 : 0));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, EVP_Cipher(ctx2.get(), output,
                                               in->data(), in->size()));
  ASSERT_EQ(approved, expect_approved);
  ASSERT_TRUE(check_test(out->data(), output, in->size(), "EVP_Cipher Encryption KAT"));
}

static const uint8_t KTDES_EDE3_CipherText[64] = {
    0x2a, 0x17, 0x79, 0x5a, 0x9b, 0x1d, 0xd8, 0x72, 0x06, 0xc6, 0xe7,
    0x55, 0x14, 0xaa, 0x7b, 0x2a, 0x6e, 0xfc, 0x71, 0x29, 0xff, 0x9b,
    0x67, 0x73, 0x7c, 0x9e, 0x15, 0x74, 0x80, 0xc8, 0x2f, 0xca, 0x93,
    0xaa, 0x8e, 0xba, 0x2c, 0x48, 0x88, 0x51, 0xc7, 0xa4, 0xf4, 0xe3,
    0x2b, 0x33, 0xe5, 0xa1, 0x58, 0x0a, 0x08, 0x3c, 0xb9, 0xf6, 0xf1,
    0x20, 0x67, 0x02, 0x49, 0xa0, 0x92, 0x18, 0xde, 0x2b
};

static const uint8_t KTDES_EDE3_CBCCipherText[64] = {
    0x2a, 0x17, 0x79, 0x5a, 0x9b, 0x1d, 0xd8, 0x72, 0xbf, 0x3f, 0xfd,
    0xe4, 0x0d, 0x66, 0x33, 0x49, 0x3b, 0x8c, 0xa6, 0xd0, 0x0a, 0x66,
    0xae, 0xf1, 0xd9, 0xa7, 0xd6, 0xfb, 0xa2, 0x39, 0x6f, 0xf6, 0x1b,
    0x8f, 0x67, 0xe1, 0x2b, 0x58, 0x1c, 0xb6, 0xa2, 0xec, 0xb3, 0xc2,
    0xe6, 0xd1, 0xcc, 0x11, 0x05, 0xdd, 0xee, 0x9d, 0x87, 0x95, 0xe9,
    0x58, 0xc7, 0xef, 0xa4, 0x6d, 0x5e, 0xd6, 0x57, 0x01
};

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

static const uint8_t kAESECBCiphertext_192[64] = {
    0x1d, 0xc8, 0xaa, 0xa7, 0x29, 0x01, 0x17, 0x09, 0x72, 0xc6, 0xe9,
    0x63, 0x02, 0x9d, 0xeb, 0x01, 0xeb, 0xc0, 0xda, 0x82, 0x6c, 0x30,
    0x7d, 0x60, 0x1b, 0x3e, 0xc7, 0x7b, 0xe3, 0x18, 0xa2, 0x43, 0x59,
    0x15, 0x4a, 0xe4, 0x8a, 0x84, 0xda, 0x16, 0x90, 0x7b, 0xfa, 0x64,
    0x37, 0x62, 0x19, 0xf1, 0x95, 0x11, 0x61, 0x84, 0xb0, 0x70, 0x49,
    0x72, 0x9f, 0xe7, 0x3a, 0x18, 0x99, 0x01, 0xba, 0xb0
};

static const uint8_t kAESECBCiphertext_256[64] = {
    0x6f, 0x2d, 0x6d, 0x7a, 0xc1, 0x8f, 0x00, 0x9f, 0x2d, 0xcf, 0xba,
    0xe6, 0x4f, 0xdd, 0xe0, 0x09, 0x5b, 0xf3, 0xa4, 0xaf, 0xce, 0x45,
    0x49, 0x6e, 0x28, 0x7b, 0x48, 0x57, 0xb5, 0xf5, 0xd8, 0x05, 0x16,
    0x0f, 0xea, 0x21, 0x0c, 0x39, 0x78, 0xee, 0x9e, 0x57, 0x3c, 0x40,
    0x11, 0x9c, 0xd9, 0x34, 0x97, 0xb9, 0xa6, 0x06, 0x40, 0x60, 0xa2,
    0x0c, 0x01, 0xe3, 0x9c, 0xda, 0x3e, 0xad, 0x99, 0x3d
};

static const uint8_t kAESCBCCiphertext[64] = {
    0xa4, 0xc1, 0x5c, 0x51, 0x2a, 0x2e, 0x2a, 0xda, 0xd9, 0x02, 0x23,
    0xe7, 0xa9, 0x34, 0x9d, 0xd8, 0x5c, 0xb3, 0x65, 0x54, 0x72, 0xc8,
    0x06, 0xf1, 0x36, 0xc3, 0x97, 0x73, 0x87, 0xca, 0x44, 0x99, 0x21,
    0xb8, 0xdb, 0x93, 0x22, 0x00, 0x89, 0x7c, 0x1c, 0xea, 0x36, 0x23,
    0x18, 0xdb, 0xc1, 0x52, 0x8c, 0x23, 0x66, 0x11, 0x0d, 0xa8, 0xe9,
    0xb8, 0x08, 0x8b, 0xaa, 0x81, 0x47, 0x01, 0xa4, 0x4f
};

static const uint8_t kAESCBCCiphertext_192[64] = {
    0x1d, 0xc8, 0xaa, 0xa7, 0x29, 0x01, 0x17, 0x09, 0x72, 0xc6, 0xe9,
    0x63, 0x02, 0x9d, 0xeb, 0x01, 0xb4, 0x48, 0xa8, 0x00, 0x94, 0x46,
    0x7f, 0xe3, 0xc1, 0x24, 0xea, 0x41, 0xa0, 0x2b, 0x47, 0x2f, 0xae,
    0x19, 0xce, 0x0d, 0xfa, 0x90, 0x45, 0x85, 0xce, 0xc4, 0x21, 0x0c,
    0x74, 0x38, 0x13, 0xfd, 0x64, 0xba, 0x58, 0x10, 0x37, 0x53, 0x48,
    0x66, 0x02, 0x76, 0xfb, 0xb1, 0x3a, 0x19, 0xce, 0x61
};

static const uint8_t kAESCBCCiphertext_256[64] = {
    0x6f, 0x2d, 0x6d, 0x7a, 0xc1, 0x8f, 0x00, 0x9f, 0x2d, 0xcf, 0xba,
    0xe6, 0x4f, 0xdd, 0xe0, 0x09, 0x9e, 0xa8, 0x28, 0xdc, 0x27, 0xde,
    0x89, 0x26, 0xc7, 0x94, 0x6a, 0xbf, 0xb6, 0x94, 0x05, 0x08, 0x6c,
    0x39, 0x07, 0x52, 0xfa, 0x7b, 0xca, 0x7d, 0x9b, 0xbf, 0xb2, 0x43,
    0x2b, 0x69, 0xee, 0xc5, 0x68, 0x4c, 0xdd, 0x62, 0xae, 0x8d, 0x7e,
    0x71, 0x0c, 0x8f, 0x11, 0xce, 0x1d, 0x8b, 0xee, 0x94
};

static const uint8_t kAESCTRCiphertext[64] = {
    0x49, 0xf5, 0x6a, 0x7d, 0x3e, 0xd7, 0xb2, 0x47, 0x35, 0xca, 0x54,
    0xf5, 0xf1, 0xb8, 0xd1, 0x48, 0xb0, 0x18, 0xc4, 0x5e, 0xeb, 0x42,
    0xfd, 0x10, 0x49, 0x1f, 0x2b, 0x11, 0xe9, 0xb0, 0x07, 0xa4, 0x00,
    0x56, 0xec, 0x25, 0x53, 0x4d, 0x70, 0x98, 0x38, 0x85, 0x5d, 0x54,
    0xab, 0x2c, 0x19, 0x13, 0x6d, 0xf3, 0x0e, 0x6f, 0x48, 0x2f, 0xab,
    0xe1, 0x82, 0xd4, 0x30, 0xa9, 0x16, 0x73, 0x93, 0xc3
};

static const uint8_t kAESCTRCiphertext_192[64] = {
    0x72, 0x7d, 0xbb, 0xd4, 0x8b, 0x16, 0x8b, 0x19, 0xa4, 0xeb, 0xa6,
    0xfa, 0xa0, 0xd0, 0x2b, 0xbb, 0x9b, 0x1f, 0xbf, 0x4d, 0x67, 0xfb,
    0xea, 0x89, 0x16, 0xd7, 0xa4, 0xb6, 0xbe, 0x1a, 0x78, 0x1c, 0x3d,
    0x44, 0x49, 0xa0, 0xf2, 0xb2, 0xb3, 0x82, 0x0f, 0xdd, 0xac, 0xd6,
    0xea, 0x6e, 0x1f, 0x09, 0x8d, 0xa5, 0xdb, 0x4f, 0x3f, 0x97, 0x90,
    0x26, 0xed, 0xf6, 0xbb, 0x62, 0xb3, 0x6f, 0x52, 0x67
};

static const uint8_t kAESCTRCiphertext_256[64] = {
    0x4a, 0x87, 0x44, 0x09, 0xf4, 0x1d, 0x80, 0x94, 0x51, 0x9a, 0xe4,
    0x89, 0x49, 0xcb, 0x98, 0x0d, 0x27, 0xc5, 0xba, 0x20, 0x00, 0x45,
    0xbb, 0x29, 0x75, 0xc0, 0xb7, 0x23, 0x0d, 0x81, 0x9f, 0x43, 0xaa,
    0x78, 0x89, 0xc0, 0xc4, 0x6d, 0x99, 0x0d, 0xb8, 0x9b, 0xc3, 0x25,
    0xa6, 0xd1, 0x7c, 0x98, 0x3e, 0xff, 0x06, 0x59, 0x41, 0xcf, 0xb2,
    0xd5, 0x2f, 0x95, 0xea, 0x83, 0xb1, 0x42, 0xb8, 0xb2
};

static const uint8_t kAESCFBCiphertext[64] = {
    0x49, 0xf5, 0x6a, 0x7d, 0x3e, 0xd7, 0xb2, 0x47, 0x35, 0xca, 0x54,
    0xf5, 0xf1, 0xb8, 0xd1, 0x48, 0x01, 0xdc, 0xba, 0x43, 0x3a, 0x7b,
    0xbf, 0x84, 0x91, 0x49, 0xc5, 0xc9, 0xd6, 0xcf, 0x6a, 0x2c, 0x3a,
    0x66, 0x99, 0x68, 0xe3, 0xd0, 0x56, 0x05, 0xe7, 0x99, 0x7f, 0xc3,
    0xbc, 0x09, 0x13, 0xa6, 0xf0, 0xde, 0x17, 0xf4, 0x85, 0x9a, 0xee,
    0x29, 0xc3, 0x77, 0xab, 0xc4, 0xf6, 0xdb, 0xae, 0x24
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

static const uint8_t kAESCMACOutput[16] = {
    0xe7, 0x32, 0x43, 0xb4, 0xae, 0x79, 0x08, 0x86, 0xe7, 0x9f, 0x0d,
    0x3f, 0x88, 0x3f, 0x1a, 0xfd
};

// kFFDHE2048PublicValueData is an arbitrary public value, mod
// kFFDHE2048Data. (The private key happens to be 4096.)
static const BN_ULONG kFFDHE2048PublicValueData[] = {
    TOBN(0x187be36b, 0xd38a4fa1), TOBN(0x0a152f39, 0x6458f3b8),
    TOBN(0x0570187e, 0xc422eeb7), TOBN(0x18af7482, 0x91173f2a),
    TOBN(0xe9fdac6a, 0xcff4eaaa), TOBN(0xf6afebb7, 0x6e589d6c),
    TOBN(0xf92f8e9a, 0xb7e33fb0), TOBN(0x70acf2aa, 0x4cf36ddd),
    TOBN(0x561ab426, 0xd07137fd), TOBN(0x5f57d037, 0x430ee91e),
    TOBN(0xe3e768c8, 0x60d10b8a), TOBN(0xb14884d8, 0xa18af8ce),
    TOBN(0xf8a98014, 0xa12b74e4), TOBN(0x748d407c, 0x3437b7a8),
    TOBN(0x627588c4, 0x9875d5a7), TOBN(0xdd24a127, 0x53c8f09d),
    TOBN(0x85a997d5, 0x0cd51aec), TOBN(0x44f0c619, 0xce348458),
    TOBN(0x9b894b24, 0x5f6b69a1), TOBN(0xae1302f2, 0xf6d4777e),
    TOBN(0xe6678eeb, 0x375db18e), TOBN(0x2674e1d6, 0x4fbcbdc8),
    TOBN(0xb297a823, 0x6fa93d28), TOBN(0x6a12fb70, 0x7c8c0510),
    TOBN(0x5c6d1aeb, 0xdb06f65b), TOBN(0xe8c2954e, 0x4c1804ca),
    TOBN(0x06bdeac1, 0xf5500fa7), TOBN(0x6a315604, 0x189cd76b),
    TOBN(0xbae7b0b3, 0x6e362dc0), TOBN(0xa57c73bd, 0xdc70fb82),
    TOBN(0xfaff50d2, 0x9d573457), TOBN(0x352bd399, 0xbe84058e),
};

const uint8_t kDHOutput[2048 / 8] = {
    0x2a, 0xe6, 0xd3, 0xa6, 0x13, 0x58, 0x8e, 0xce, 0x53, 0xaa, 0xf6, 0x5d,
    0x9a, 0xae, 0x02, 0x12, 0xf5, 0x80, 0x3d, 0x06, 0x09, 0x76, 0xac, 0x57,
    0x37, 0x9e, 0xab, 0x38, 0x62, 0x25, 0x05, 0x1d, 0xf3, 0xa9, 0x39, 0x60,
    0xf6, 0xae, 0x90, 0xed, 0x1e, 0xad, 0x6e, 0xe9, 0xe3, 0xba, 0x27, 0xf6,
    0xdb, 0x54, 0xdf, 0xe2, 0xbd, 0xbb, 0x7f, 0xf1, 0x81, 0xac, 0x1a, 0xfa,
    0xdb, 0x87, 0x07, 0x98, 0x76, 0x90, 0x21, 0xf2, 0xae, 0xda, 0x0d, 0x84,
    0x97, 0x64, 0x0b, 0xbf, 0xb8, 0x8d, 0x10, 0x46, 0xe2, 0xd5, 0xca, 0x1b,
    0xbb, 0xe5, 0x37, 0xb2, 0x3b, 0x35, 0xd3, 0x1b, 0x65, 0xea, 0xae, 0xf2,
    0x03, 0xe2, 0xb6, 0xde, 0x22, 0xb7, 0x86, 0x49, 0x79, 0xfe, 0xd7, 0x16,
    0xf7, 0xdc, 0x9c, 0x59, 0xf5, 0xb7, 0x70, 0xc0, 0x53, 0x42, 0x6f, 0xb1,
    0xd2, 0x4e, 0x00, 0x25, 0x4b, 0x2d, 0x5a, 0x9b, 0xd0, 0xe9, 0x27, 0x43,
    0xcc, 0x00, 0x66, 0xea, 0x94, 0x7a, 0x0b, 0xb9, 0x89, 0x0c, 0x5e, 0x94,
    0xb8, 0x3a, 0x78, 0x9c, 0x4d, 0x84, 0xe6, 0x32, 0x2c, 0x38, 0x7c, 0xf7,
    0x43, 0x9c, 0xd8, 0xb8, 0x1c, 0xce, 0x24, 0x91, 0x20, 0x67, 0x7a, 0x54,
    0x1f, 0x7e, 0x86, 0x7f, 0xa1, 0xc1, 0x03, 0x4e, 0x2c, 0x26, 0x71, 0xb2,
    0x06, 0x30, 0xb3, 0x6c, 0x15, 0xcc, 0xac, 0x25, 0xe5, 0x37, 0x3f, 0x24,
    0x8f, 0x2a, 0x89, 0x5e, 0x3d, 0x43, 0x94, 0xc9, 0x36, 0xae, 0x40, 0x00,
    0x6a, 0x0d, 0xb0, 0x6e, 0x8b, 0x2e, 0x70, 0x57, 0xe1, 0x88, 0x53, 0xd6,
    0x06, 0x80, 0x2a, 0x4e, 0x5a, 0xf0, 0x1e, 0xaa, 0xcb, 0xab, 0x06, 0x0e,
    0x27, 0x0f, 0xd9, 0x88, 0xd9, 0x01, 0xe3, 0x07, 0xeb, 0xdf, 0xc3, 0x12,
    0xe3, 0x40, 0x88, 0x7b, 0x5f, 0x59, 0x78, 0x6e, 0x26, 0x20, 0xc3, 0xdf,
    0xc8, 0xe4, 0x5e, 0xb8
};

static const uint8_t kOutput_md4[MD4_DIGEST_LENGTH] = {
    0xab, 0x6b, 0xda, 0x84, 0xc0, 0x6b, 0xd0, 0x1d, 0x19, 0xc0, 0x08,
    0x11, 0x07, 0x8d, 0xce, 0x0e
};

static const uint8_t kOutput_md5[MD5_DIGEST_LENGTH] = {
    0xe9, 0x70, 0xa2, 0xf7, 0x9c, 0x55, 0x57, 0xac, 0x4e, 0x7f, 0x6b,
    0xbc, 0xa3, 0xb9, 0xb7, 0xdb
};

static const uint8_t kOutput_sha1[SHA_DIGEST_LENGTH] = {
    0xaa, 0x18, 0x71, 0x34, 0x00, 0x71, 0x67, 0x9f, 0xa1, 0x6d, 0x20,
    0x82, 0x91, 0x0f, 0x53, 0x0a, 0xcd, 0x6e, 0xa4, 0x34
};

static const uint8_t kOutput_sha224[SHA224_DIGEST_LENGTH] = {
    0x5f, 0x1a, 0x9e, 0x68, 0x4c, 0xb7, 0x42, 0x68, 0xa0, 0x8b, 0x87,
    0xd7, 0x96, 0xb6, 0xcf, 0x1e, 0x4f, 0x85, 0x1c, 0x47, 0xe9, 0x29,
    0xb3, 0xb2, 0x73, 0x72, 0xd2, 0x69
};

static const uint8_t kOutput_sha256[SHA256_DIGEST_LENGTH] = {
    0xe7, 0x63, 0x1c, 0xbb, 0x12, 0xb5, 0xbf, 0x4f, 0x99, 0x05, 0x9d,
    0x40, 0x15, 0x55, 0x34, 0x9c, 0x26, 0x36, 0xd2, 0xfe, 0x6a, 0xd6,
    0x26, 0xb4, 0x9d, 0x33, 0x07, 0xf5, 0xe6, 0x29, 0x13, 0x92
};

static const uint8_t kOutput_sha384[SHA384_DIGEST_LENGTH] = {
    0x15, 0x81, 0x48, 0x8d, 0x95, 0xf2, 0x66, 0x84, 0x65, 0x94, 0x3e,
    0xb9, 0x8c, 0xda, 0x36, 0x30, 0x2a, 0x85, 0xc0, 0xcd, 0xec, 0x38,
    0xa0, 0x1f, 0x72, 0xe2, 0x68, 0xfe, 0x4e, 0xdb, 0x27, 0x8b, 0x50,
    0x15, 0xe0, 0x24, 0xc3, 0x65, 0xd1, 0x66, 0x2a, 0x3e, 0xe7, 0x00,
    0x16, 0x51, 0xf5, 0x18
};

static const uint8_t kOutput_sha512[SHA512_DIGEST_LENGTH] = {
    0x71, 0xcc, 0xec, 0x03, 0xf8, 0x76, 0xf4, 0x0b, 0xf1, 0x1b, 0x89,
    0x27, 0x83, 0xa1, 0x70, 0x02, 0x00, 0x2b, 0xe9, 0x3c, 0x3c, 0x65,
    0x12, 0xb9, 0xa8, 0x8c, 0xc5, 0x9d, 0xae, 0x3c, 0x73, 0x43, 0x76,
    0x4d, 0x98, 0xed, 0xd0, 0xbe, 0xb4, 0xf9, 0x0b, 0x5c, 0x5d, 0x34,
    0x46, 0x30, 0x18, 0xc2, 0x05, 0x88, 0x8a, 0x3c, 0x25, 0xcc, 0x06,
    0xf8, 0x73, 0xb9, 0xe4, 0x18, 0xa8, 0xc2, 0xf0, 0xe5
};

static const uint8_t kOutput_sha512_256[SHA512_256_DIGEST_LENGTH] = {
    0x1a, 0x78, 0x68, 0x6b, 0x69, 0x6d, 0x28, 0x14, 0x6b, 0x37, 0x11,
    0x2d, 0xfb, 0x72, 0x35, 0xfa, 0xc1, 0xc4, 0x5f, 0x5c, 0x49, 0x91,
    0x08, 0x95, 0x0b, 0x0f, 0xc9, 0x88, 0x44, 0x12, 0x01, 0x6a
};

static const uint8_t kHMACOutput_sha1[SHA_DIGEST_LENGTH] = {
    0x2b, 0xcb, 0x0e, 0xe2, 0xa4, 0x66, 0xad, 0x70, 0xa2, 0xb8, 0x8e,
    0xe2, 0x4c, 0x76, 0xf9, 0x1c, 0x28, 0x07, 0x78, 0xeb
};

static const uint8_t kHMACOutput_sha224[SHA224_DIGEST_LENGTH] = {
    0x68, 0x29, 0x44, 0x26, 0x49, 0x3f, 0x02, 0x27, 0x64, 0xd1, 0x29,
    0xa5, 0x59, 0xcd, 0x2f, 0x79, 0xc7, 0xf1, 0xa8, 0xed, 0x77, 0xe2,
    0x0a, 0xc7, 0x75, 0xba, 0x61, 0xb4
};

static const uint8_t kHMACOutput_sha256[SHA256_DIGEST_LENGTH] = {
    0x0d, 0xb3, 0xca, 0x78, 0x9a, 0x03, 0x6d, 0x23, 0x3c, 0x7f, 0x00,
    0x87, 0x9d, 0x9c, 0x49, 0x4c, 0x65, 0x9d, 0x2d, 0xa3, 0x8d, 0x77,
    0x74, 0x68, 0xd9, 0xd9, 0xa8, 0xa2, 0x65, 0xb2, 0x5e, 0x9e
};

static const uint8_t kHMACOutput_sha384[SHA384_DIGEST_LENGTH] = {
    0x3e, 0x76, 0xac, 0x2f, 0x8b, 0x27, 0xea, 0x08, 0xef, 0xa8, 0xa2,
    0xf7, 0x5b, 0xf2, 0x95, 0x0d, 0x71, 0x8f, 0xbf, 0x5f, 0x1e, 0xe6,
    0xef, 0xb6, 0x25, 0x1c, 0xd5, 0x07, 0x05, 0x20, 0x61, 0x9e, 0x71,
    0x8a, 0x02, 0x92, 0xef, 0x59, 0xdf, 0x32, 0x0f, 0x8c, 0xa4, 0x0a,
    0x58, 0x0d, 0x91, 0xd8
};

static const uint8_t kHMACOutput_sha512[SHA512_DIGEST_LENGTH] = {
    0xeb, 0x8f, 0xe6, 0x4f, 0xcb, 0x40, 0x23, 0xbe, 0xfc, 0x64, 0xd6,
    0x99, 0x3d, 0x22, 0x7d, 0x76, 0x1a, 0x97, 0x69, 0x01, 0xed, 0x04,
    0x87, 0x48, 0xb3, 0xbe, 0xda, 0xc7, 0x19, 0xb9, 0xe2, 0x95, 0x6b,
    0x69, 0xe3, 0x9a, 0x2f, 0x27, 0xfc, 0xfd, 0x2f, 0xb5, 0xcb, 0xa6,
    0xa9, 0xb2, 0xcf, 0xe7, 0x22, 0x4f, 0xf2, 0x0a, 0x72, 0xf5, 0x97,
    0x29, 0x3b, 0x4f, 0xd7, 0xbd, 0xfe, 0x76, 0xea, 0x55
};

static const uint8_t kHMACOutput_sha512_256[SHA512_256_DIGEST_LENGTH] = {
    0x2d, 0x7b, 0xe8, 0x12, 0x93, 0xba, 0xc2, 0xb5, 0xc6, 0x73, 0x61,
    0xc1, 0xd0, 0xb8, 0x75, 0xfe, 0x00, 0xd8, 0x3d, 0x7c, 0x31, 0x47,
    0x22, 0x83, 0xdd, 0x7c, 0x3f, 0xb1, 0x97, 0x1e, 0xd3, 0x2c
};

static const uint8_t kDRBGEntropy[48] = {
    'B', 'C', 'M', ' ', 'K', 'n', 'o', 'w', 'n', ' ', 'A', 'n', 's',
    'w', 'e', 'r', ' ', 'T', 'e', 's', 't', ' ', 'D', 'B', 'R', 'G',
    ' ', 'I', 'n', 'i', 't', 'i', 'a', 'l', ' ', 'E', 'n', 't', 'r',
    'o', 'p', 'y', ' ', ' ', ' ', ' ', ' ', ' '
};

static const uint8_t kDRBGPersonalization[18] = {
    'B', 'C', 'M', 'P', 'e', 'r', 's', 'o', 'n', 'a', 'l', 'i', 'z',
    'a', 't', 'i', 'o', 'n'
};

static const uint8_t kDRBGAD[16] = {
    'B', 'C', 'M', ' ', 'D', 'R', 'B', 'G', ' ', 'K', 'A', 'T', ' ',
    'A', 'D', ' '
};

const uint8_t kDRBGOutput[64] = {
    0x1d, 0x63, 0xdf, 0x05, 0x51, 0x49, 0x22, 0x46, 0xcd, 0x9b, 0xc5,
    0xbb, 0xf1, 0x5d, 0x44, 0xae, 0x13, 0x78, 0xb1, 0xe4, 0x7c, 0xf1,
    0x96, 0x33, 0x3d, 0x60, 0xb6, 0x29, 0xd4, 0xbb, 0x6b, 0x44, 0xf9,
    0xef, 0xd9, 0xf4, 0xa2, 0xba, 0x48, 0xea, 0x39, 0x75, 0x59, 0x32,
    0xf7, 0x31, 0x2c, 0x98, 0x14, 0x2b, 0x49, 0xdf, 0x02, 0xb6, 0x5d,
    0x71, 0x09, 0x50, 0xdb, 0x23, 0xdb, 0xe5, 0x22, 0x95
};

static const uint8_t kDRBGEntropy2[48] = {
    'B', 'C', 'M', ' ', 'K', 'n', 'o', 'w', 'n', ' ', 'A', 'n', 's',
    'w', 'e', 'r', ' ', 'T', 'e', 's', 't', ' ', 'D', 'B', 'R', 'G',
    ' ', 'R', 'e', 's', 'e', 'e', 'd', ' ', 'E', 'n', 't', 'r', 'o',
    'p', 'y', ' ', ' ', ' ', ' ', ' ', ' ', ' '
};

static const uint8_t kDRBGReseedOutput[64] = {
    0xa4, 0x77, 0x05, 0xdb, 0x14, 0x11, 0x76, 0x71, 0x42, 0x5b, 0xd8,
    0xd7, 0xa5, 0x4f, 0x8b, 0x39, 0xf2, 0x10, 0x4a, 0x50, 0x5b, 0xa2,
    0xc8, 0xf0, 0xbb, 0x3e, 0xa1, 0xa5, 0x90, 0x7d, 0x54, 0xd9, 0xc6,
    0xb0, 0x96, 0xc0, 0x2b, 0x7e, 0x9b, 0xc9, 0xa1, 0xdd, 0x78, 0x2e,
    0xd5, 0xa8, 0x66, 0x16, 0xbd, 0x18, 0x3c, 0xf2, 0xaa, 0x7a, 0x2b,
    0x37, 0xf9, 0xab, 0x35, 0x64, 0x15, 0x01, 0x3f, 0xc4,
};

static const uint8_t kTLSSecret[32] = {
    0xbf, 0xe4, 0xb7, 0xe0, 0x26, 0x55, 0x5f, 0x6a, 0xdf, 0x5d, 0x27,
    0xd6, 0x89, 0x99, 0x2a, 0xd6, 0xf7, 0x65, 0x66, 0x07, 0x4b, 0x55,
    0x5f, 0x64, 0x55, 0xcd, 0xd5, 0x77, 0xa4, 0xc7, 0x09, 0x61,
};
static const char kTLSLabel[] = "FIPS self test";
static const uint8_t kTLSSeed1[16] = {
    0x8f, 0x0d, 0xe8, 0xb6, 0x90, 0x8f, 0xb1, 0xd2,
    0x6d, 0x51, 0xf4, 0x79, 0x18, 0x63, 0x51, 0x65,
};
static const uint8_t kTLSSeed2[16] = {
    0x7d, 0x24, 0x1a, 0x9d, 0x3c, 0x59, 0xbf, 0x3c,
    0x31, 0x1e, 0x2b, 0x21, 0x41, 0x8d, 0x32, 0x81,
};

static const uint8_t kTLSOutput_mdsha1[32] = {
    0x36, 0xa9, 0x31, 0xb0, 0x43, 0xe3, 0x64, 0x72, 0xb9, 0x47, 0x54,
    0x0d, 0x8a, 0xfc, 0xe3, 0x5c, 0x1c, 0x15, 0x67, 0x7e, 0xa3, 0x5d,
    0xf2, 0x3a, 0x57, 0xfd, 0x50, 0x16, 0xe1, 0xa4, 0xa6, 0x37
};

static const uint8_t kTLSOutput_md[32] = {
    0x79, 0xef, 0x46, 0xc4, 0x35, 0xbc, 0xe5, 0xda, 0xd3, 0x66, 0x91,
    0xdc, 0x86, 0x09, 0x41, 0x66, 0xf2, 0x0c, 0xeb, 0xe6, 0xab, 0x5c,
    0x58, 0xf4, 0x65, 0xce, 0x2f, 0x5f, 0x4b, 0x34, 0x1e, 0xa1
};

static const uint8_t kTLSOutput_sha1[32] = {
    0xbb, 0x0a, 0x73, 0x52, 0xf8, 0x85, 0xd7, 0xbd, 0x12, 0x34, 0x78,
    0x3b, 0x54, 0x4c, 0x75, 0xfe, 0xd7, 0x23, 0x6e, 0x22, 0x3f, 0x42,
    0x34, 0x99, 0x57, 0x6b, 0x14, 0xc4, 0xc8, 0xae, 0x9f, 0x4c
};

static const uint8_t kTLSOutput_sha224[32] = {
    0xdd, 0xaf, 0x6f, 0xaa, 0xd9, 0x2b, 0x3d, 0xb9, 0x46, 0x4c, 0x55,
    0x8a, 0xf7, 0xa6, 0x9b, 0x0b, 0x35, 0xcc, 0x07, 0xa7, 0x55, 0x5b,
    0x5e, 0x39, 0x12, 0xc0, 0xd4, 0x30, 0xdf, 0x0c, 0xdf, 0x6b
};

static const uint8_t kTLSOutput_sha256[32] = {
    0x67, 0x85, 0xde, 0x60, 0xfc, 0x0a, 0x83, 0xe9, 0xa2, 0x2a, 0xb3,
    0xf0, 0x27, 0x0c, 0xba, 0xf7, 0xfa, 0x82, 0x3d, 0x14, 0x77, 0x1d,
    0x86, 0x29, 0x79, 0x39, 0x77, 0x8a, 0xd5, 0x0e, 0x9d, 0x32
};

static const uint8_t kTLSOutput_sha384[32] = {
    0x75, 0x15, 0x3f, 0x44, 0x7a, 0xfd, 0x34, 0xed, 0x2b, 0x67, 0xbc,
    0xd8, 0x57, 0x96, 0xab, 0xff, 0xf4, 0x0c, 0x05, 0x94, 0x02, 0x23,
    0x81, 0xbf, 0x0e, 0xd2, 0xec, 0x7c, 0xe0, 0xa7, 0xc3, 0x7d
};

static const uint8_t kTLSOutput_sha512[32] = {
    0x68, 0xb9, 0xc8, 0x4c, 0xf5, 0x51, 0xfc, 0x7a, 0x1f, 0x6c, 0xe5,
    0x43, 0x73, 0x80, 0x53, 0x7c, 0xae, 0x76, 0x55, 0x67, 0xe0, 0x79,
    0xbf, 0x3a, 0x53, 0x71, 0xb7, 0x9c, 0xb5, 0x03, 0x15, 0x3f
};

static const uint8_t kAESGCMCiphertext_128[64] = {
    0x38, 0x71, 0xcb, 0x61, 0x70, 0x60, 0x13, 0x8b, 0x2f, 0x91, 0x09,
    0x7f, 0x83, 0x20, 0x0f, 0x1f, 0x71, 0xe2, 0x47, 0x46, 0x6f, 0x5f,
    0xa8, 0xad, 0xa8, 0xfc, 0x0a, 0xfd, 0x36, 0x65, 0x84, 0x90, 0x28,
    0x2b, 0xcb, 0x4f, 0x68, 0xae, 0x09, 0xba, 0xae, 0xdd, 0xdb, 0x91,
    0xcc, 0x38, 0xb3, 0xad, 0x10, 0x84, 0xb8, 0x45, 0x36, 0xf3, 0x96,
    0xb4, 0xef, 0xba, 0xda, 0x10, 0xf8, 0x8b, 0xf3, 0xda
};

static const uint8_t kAESGCMCiphertext_192[64] = {
    0x05, 0x63, 0x6e, 0xe4, 0xd1, 0x9f, 0xd0, 0x91, 0x18, 0xc9, 0xf8,
    0xfd, 0xc2, 0x62, 0x09, 0x05, 0x91, 0xb4, 0x92, 0x66, 0x18, 0xe7,
    0x93, 0x6a, 0xc7, 0xde, 0x81, 0x36, 0x93, 0x79, 0x45, 0x34, 0xc0,
    0x6d, 0x14, 0x94, 0x93, 0x39, 0x2b, 0x7f, 0x4f, 0x10, 0x1c, 0xa5,
    0xfe, 0x3b, 0x37, 0xd7, 0x0a, 0x98, 0xd7, 0xb5, 0xe0, 0xdc, 0xe4,
    0x9f, 0x36, 0x40, 0xad, 0x03, 0xbf, 0x53, 0xe0, 0x7c
};

static const uint8_t kAESGCMCiphertext_256[64] = {
    0x92, 0x5f, 0xae, 0x84, 0xe7, 0x40, 0xfa, 0x1e, 0xaf, 0x8f, 0x97,
    0x0e, 0x8e, 0xdd, 0x6a, 0x94, 0x22, 0xee, 0x4f, 0x70, 0x66, 0xbf,
    0xb1, 0x99, 0x05, 0xbd, 0xd0, 0xd7, 0x91, 0x54, 0xaf, 0xe1, 0x52,
    0xc9, 0x4e, 0x55, 0xa5, 0x23, 0x62, 0x8b, 0x23, 0x40, 0x90, 0x56,
    0xe0, 0x68, 0x63, 0xe5, 0x7e, 0x5b, 0xbe, 0x96, 0x7b, 0xc4, 0x16,
    0xf9, 0xbe, 0x18, 0x06, 0x79, 0x8f, 0x99, 0x35, 0xe3
};

struct AEADTestVector {
  const char* name;
  const EVP_AEAD *cipher;
  const uint8_t *key;
  const int key_length;
  const uint8_t *expected_ciphertext;
  const int cipher_text_length;
  const int expect_approved;
  const bool test_repeat_nonce;
} nAEADTestVectors[] = {
    // Internal IV usage of AES-GCM is approved.
    { "AES-GCM 128-bit key internal iv test", EVP_aead_aes_128_gcm_randnonce(),
        kAESKey, 16, nullptr, 0, AWSLC_APPROVED, false },
    { "AES-GCM 256-bit key internal iv test", EVP_aead_aes_256_gcm_randnonce(),
        kAESKey_256, 32, nullptr, 0, AWSLC_APPROVED, false },
    // External IV usage of AES-GCM is not approved unless used within a TLS
    // context.
    {  "Generic AES-GCM 128-bit key external iv test", EVP_aead_aes_128_gcm(),
        kAESKey, 16, kAESGCMCiphertext_128, 64, AWSLC_NOT_APPROVED, false },
    {  "Generic AES-GCM 192-bit key external iv test", EVP_aead_aes_192_gcm(),
        kAESKey_192, 24, kAESGCMCiphertext_192, 64, AWSLC_NOT_APPROVED, false },
    {  "Generic AES-GCM 256-bit key external iv test", EVP_aead_aes_256_gcm(),
        kAESKey_256, 32, kAESGCMCiphertext_256, 64, AWSLC_NOT_APPROVED, false },
    // External IV usage of AEAD AES-GCM APIs specific for TLS is approved.
    {  "TLS1.2 AES-GCM 128-bit key external iv test", EVP_aead_aes_128_gcm_tls12(),
        kAESKey, 16, kAESGCMCiphertext_128, 64, AWSLC_APPROVED, true },
    {  "TLS1.2 AES-GCM 256-bit key external iv test", EVP_aead_aes_256_gcm_tls12(),
        kAESKey_256, 32, kAESGCMCiphertext_256, 64, AWSLC_APPROVED, true },
    {  "TLS1.3 AES-GCM 128-bit key external iv test", EVP_aead_aes_128_gcm_tls13(),
        kAESKey, 16, kAESGCMCiphertext_128, 64, AWSLC_APPROVED, true },
    {  "TLS1.3 AES-GCM 256-bit key external iv test", EVP_aead_aes_256_gcm_tls13(),
        kAESKey_256, 32, kAESGCMCiphertext_256, 64, AWSLC_APPROVED, true },
    // 128 bit keys with 32 bit tag lengths are approved for AES-CCM.
    {  "AES-CCM 128-bit key test", EVP_aead_aes_128_ccm_bluetooth(),
        kAESKey, 16, kAESCCMCiphertext, 64, AWSLC_APPROVED, false },
};

class AEAD_ServiceIndicatorTest : public awslc::TestWithNoErrors<AEADTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, AEAD_ServiceIndicatorTest, testing::ValuesIn(nAEADTestVectors));

TEST_P(AEAD_ServiceIndicatorTest, EVP_AEAD) {
  const AEADTestVector &aeadTestVector = GetParam();

  int approved = AWSLC_NOT_APPROVED;

  bssl::ScopedEVP_AEAD_CTX aead_ctx;
  std::vector<uint8_t> plaintext(kPlaintext, kPlaintext + sizeof(kPlaintext));
  std::vector<uint8_t> nonce(EVP_AEAD_MAX_NONCE_LENGTH, 0);
  std::vector<uint8_t> encrypt_output(256);
  std::vector<uint8_t> decrypt_output(256);
  size_t out_len;

  // Test running the EVP_AEAD_CTX interfaces one by one directly, and check
  // |EVP_AEAD_CTX_seal| and |EVP_AEAD_CTX_open| for approval at the end.
  // |EVP_AEAD_CTX_init| should not be approved because the function does not
  // indicate that a service has been fully completed yet.
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_AEAD_CTX_init(aead_ctx.get(), aeadTestVector.cipher,
                                aeadTestVector.key, aeadTestVector.key_length, 0, nullptr)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_AEAD_CTX_seal(aead_ctx.get(),
      encrypt_output.data(), &out_len, encrypt_output.size(), nonce.data(), EVP_AEAD_nonce_length(aeadTestVector.cipher),
      plaintext.data(), plaintext.size(), nullptr, 0)));
  ASSERT_EQ(approved, aeadTestVector.expect_approved);
  encrypt_output.resize(out_len);
  if(aeadTestVector.expected_ciphertext) {
      ASSERT_TRUE(check_test(aeadTestVector.expected_ciphertext, encrypt_output.data(),
                           aeadTestVector.cipher_text_length, aeadTestVector.name));
  }

  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_AEAD_CTX_open(aead_ctx.get(),
      decrypt_output.data(), &out_len, decrypt_output.size(), nonce.data(), EVP_AEAD_nonce_length(aeadTestVector.cipher),
      encrypt_output.data(), out_len, nullptr, 0)));
  ASSERT_EQ(approved, aeadTestVector.expect_approved);
  decrypt_output.resize(out_len);
  ASSERT_TRUE(check_test(plaintext.data(), decrypt_output.data(), plaintext.size(),
                  aeadTestVector.name));

  // Second call when encrypting using the same nonce for AES-GCM TLS specific
  // functions should fail and return |AWSLC_NOT_APPROVED|.
  if(aeadTestVector.test_repeat_nonce) {
    CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_FALSE(EVP_AEAD_CTX_seal(aead_ctx.get(),
         encrypt_output.data(), &out_len, encrypt_output.size(), nonce.data(), EVP_AEAD_nonce_length(aeadTestVector.cipher),
         kPlaintext, sizeof(kPlaintext), nullptr, 0)));
    ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
    ASSERT_EQ(ERR_GET_REASON(ERR_get_error()), CIPHER_R_INVALID_NONCE);
  }
}

struct CipherTestVector {
  const EVP_CIPHER *cipher;
  const uint8_t *key;
  const int key_length;
  const uint8_t *expected_ciphertext;
  const int cipher_text_length;
  const bool has_iv;
  const int expect_approved;
} nTestVectors[] = {
  { EVP_aes_128_ecb(), kAESKey, 16, kAESECBCiphertext, 64, false, AWSLC_APPROVED },
  { EVP_aes_192_ecb(), kAESKey_192, 24, kAESECBCiphertext_192, 64, false, AWSLC_APPROVED },
  { EVP_aes_256_ecb(), kAESKey_256, 32, kAESECBCiphertext_256, 64, false, AWSLC_APPROVED },
  { EVP_aes_128_cbc(), kAESKey, 16, kAESCBCCiphertext, 64, true, AWSLC_APPROVED },
  { EVP_aes_192_cbc(), kAESKey_192, 24, kAESCBCCiphertext_192, 64, true, AWSLC_APPROVED },
  { EVP_aes_256_cbc(), kAESKey_256, 32, kAESCBCCiphertext_256, 64, true, AWSLC_APPROVED },
  { EVP_aes_128_ctr(), kAESKey, 16, kAESCTRCiphertext, 64, true, AWSLC_APPROVED },
  { EVP_aes_192_ctr(), kAESKey_192, 24, kAESCTRCiphertext_192, 64, true, AWSLC_APPROVED },
  { EVP_aes_256_ctr(), kAESKey_256, 32, kAESCTRCiphertext_256, 64, true, AWSLC_APPROVED },
  { EVP_aes_128_ofb(), kAESKey, 16, kAESOFBCiphertext, 64, true, AWSLC_NOT_APPROVED },
  { EVP_des_ede3(), kAESKey_192, 24, KTDES_EDE3_CipherText, 64, false, AWSLC_NOT_APPROVED },
  { EVP_des_ede3_cbc(), kAESKey_192, 24, KTDES_EDE3_CBCCipherText, 64, false, AWSLC_NOT_APPROVED }
};

class EVP_ServiceIndicatorTest : public awslc::TestWithNoErrors<CipherTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, EVP_ServiceIndicatorTest, testing::ValuesIn(nTestVectors));

TEST_P(EVP_ServiceIndicatorTest, EVP_Ciphers) {
  const CipherTestVector &evpTestVector = GetParam();

  const EVP_CIPHER *cipher = evpTestVector.cipher;
  std::vector<uint8_t> key(evpTestVector.key, evpTestVector.key + evpTestVector.key_length);
  std::vector<uint8_t> plaintext(kPlaintext, kPlaintext + sizeof(kPlaintext));
  std::vector<uint8_t> ciphertext(evpTestVector.expected_ciphertext, evpTestVector.expected_ciphertext + evpTestVector.cipher_text_length);

  TestOperation(cipher, true /* encrypt */, key, plaintext, ciphertext, evpTestVector.expect_approved);
  TestOperation(cipher, false /* decrypt */, key, plaintext, ciphertext, evpTestVector.expect_approved);
}

struct MD {
  // name is the name of the digest test.
  const char* name;
  // length of digest.
  const int length;
  // func is the digest to test.
  const EVP_MD *(*func)();
  // one_shot_func is the convenience one-shot version of the digest.
  uint8_t *(*one_shot_func)(const uint8_t *, size_t, uint8_t *);
};

static const MD md4 = { "KAT for MD4", MD4_DIGEST_LENGTH, &EVP_md4, &MD4 };
static const MD md5 = { "KAT for MD5", MD5_DIGEST_LENGTH, &EVP_md5, &MD5 };
static const MD sha1 = { "KAT for SHA1", SHA_DIGEST_LENGTH, &EVP_sha1, &SHA1 };
static const MD sha224 = { "KAT for SHA224", SHA224_DIGEST_LENGTH, &EVP_sha224, &SHA224 };
static const MD sha256 = { "KAT for SHA256", SHA256_DIGEST_LENGTH, &EVP_sha256, &SHA256 };
static const MD sha384 = { "KAT for SHA384", SHA384_DIGEST_LENGTH, &EVP_sha384, &SHA384 };
static const MD sha512 = { "KAT for SHA512", SHA512_DIGEST_LENGTH, &EVP_sha512, &SHA512 };
static const MD sha512_256 = { "KAT for SHA512-256", SHA512_256_DIGEST_LENGTH, &EVP_sha512_256, &SHA512_256 };

struct DigestTestVector {
  // md is the digest to test.
  const MD &md;
  // expected_digest is the expected digest.
  const uint8_t *expected_digest;
  // expected to be approved or not.
  const int expect_approved;
} kDigestTestVectors[] = {
    { md4, kOutput_md4, AWSLC_NOT_APPROVED },
    { md5, kOutput_md5, AWSLC_NOT_APPROVED },
    { sha1, kOutput_sha1, AWSLC_APPROVED },
    { sha224, kOutput_sha224, AWSLC_APPROVED },
    { sha256, kOutput_sha256, AWSLC_APPROVED },
    { sha384, kOutput_sha384, AWSLC_APPROVED },
    { sha512, kOutput_sha512, AWSLC_APPROVED },
    { sha512_256, kOutput_sha512_256, AWSLC_APPROVED }
};

class EVP_MD_ServiceIndicatorTest : public awslc::TestWithNoErrors<DigestTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, EVP_MD_ServiceIndicatorTest, testing::ValuesIn(kDigestTestVectors));

TEST_P(EVP_MD_ServiceIndicatorTest, EVP_Digests) {
  const DigestTestVector &digestTestVector = GetParam();

  int approved = AWSLC_NOT_APPROVED;
  bssl::ScopedEVP_MD_CTX ctx;
  std::vector<uint8_t> plaintext(kPlaintext, kPlaintext + sizeof(kPlaintext));
  std::vector<uint8_t> digest(digestTestVector.md.length);
  unsigned digest_len;

  // Test running the EVP_Digest interfaces one by one directly, and check
  // |EVP_DigestFinal_ex| for approval at the end. |EVP_DigestInit_ex| and
  // |EVP_DigestUpdate| should not be approved, because the functions do not
  // indicate that a service has been fully completed yet.
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_DigestInit_ex(ctx.get(), digestTestVector.md.func(), nullptr)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_DigestUpdate(ctx.get(), plaintext.data(), plaintext.size())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_DigestFinal_ex(ctx.get(), digest.data(), &digest_len)));
  ASSERT_EQ(approved, digestTestVector.expect_approved);
  ASSERT_TRUE(check_test(digestTestVector.expected_digest, digest.data(), digest_len, digestTestVector.md.name));


  // Test using the one-shot |EVP_Digest| function for approval.
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_Digest(plaintext.data(), plaintext.size(),
                                               digest.data(), &digest_len, digestTestVector.md.func(), nullptr)));
  ASSERT_EQ(approved, digestTestVector.expect_approved);
  ASSERT_TRUE(check_test(digestTestVector.expected_digest, digest.data(), digest_len, digestTestVector.md.name));


  // Test using the one-shot API for approval.
  CALL_SERVICE_AND_CHECK_APPROVED(approved, digestTestVector.md.one_shot_func(plaintext.data(), plaintext.size(), digest.data()));
  ASSERT_EQ(approved, digestTestVector.expect_approved);
  ASSERT_TRUE(check_test(digestTestVector.expected_digest, digest.data(), digestTestVector.md.length, digestTestVector.md.name));
}

struct HMACTestVector {
  // func is the hash function for HMAC to test.
  const EVP_MD *(*func)(void);
  // expected_digest is the expected digest.
  const uint8_t *expected_digest;
  // expected to be approved or not.
  const int expect_approved;
} kHMACTestVectors[] = {
    { EVP_sha1, kHMACOutput_sha1, AWSLC_APPROVED },
    { EVP_sha224, kHMACOutput_sha224, AWSLC_APPROVED },
    { EVP_sha256, kHMACOutput_sha256, AWSLC_APPROVED },
    { EVP_sha384, kHMACOutput_sha384, AWSLC_APPROVED },
    { EVP_sha512, kHMACOutput_sha512, AWSLC_APPROVED },
    { EVP_sha512_256, kHMACOutput_sha512_256, AWSLC_NOT_APPROVED }
};

class HMAC_ServiceIndicatorTest : public awslc::TestWithNoErrors<HMACTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, HMAC_ServiceIndicatorTest, testing::ValuesIn(kHMACTestVectors));

TEST_P(HMAC_ServiceIndicatorTest, HMACTest) {
  const HMACTestVector &hmacTestVector = GetParam();

  int approved = AWSLC_NOT_APPROVED;
  const uint8_t kHMACKey[64] = {0};
  const EVP_MD *digest = hmacTestVector.func();
  std::vector<uint8_t> plaintext(kPlaintext, kPlaintext + sizeof(kPlaintext));
  std::vector<uint8_t> key(kHMACKey, kHMACKey + sizeof(kHMACKey));
  unsigned expected_mac_len = EVP_MD_size(digest);
  std::vector<uint8_t> mac(expected_mac_len);

  // Test running the HMAC interfaces one by one directly, and check
  // |HMAC_Final| for approval at the end. |HMAC_Init_ex| and |HMAC_Update|
  // should not be approved, because the functions do not indicate that a
  // service has been fully completed yet.
  unsigned mac_len;
  bssl::ScopedHMAC_CTX ctx;
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(HMAC_Init_ex(ctx.get(), key.data(), key.size(), digest, nullptr)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(HMAC_Update(ctx.get(), plaintext.data(), plaintext.size())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(HMAC_Final(ctx.get(), mac.data(), &mac_len)));
  ASSERT_EQ(approved, hmacTestVector.expect_approved);
  ASSERT_TRUE(check_test(hmacTestVector.expected_digest, mac.data(), mac_len, "HMAC KAT"));


  // Test using the one-shot API for approval.
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(HMAC(digest, key.data(),
                     key.size(), plaintext.data(), plaintext.size(), mac.data(), &mac_len)));
  ASSERT_EQ(approved, hmacTestVector.expect_approved);
  ASSERT_TRUE(check_test(hmacTestVector.expected_digest, mac.data(), mac_len, "HMAC KAT"));
}

// RSA tests are not parameterized with the |kRSATestVectors| as key
// generation for RSA is time consuming.
TEST(ServiceIndicatorTest, RSAKeyGen) {
 int approved = AWSLC_NOT_APPROVED;
 bssl::UniquePtr<RSA> rsa(RSA_new());
 ASSERT_TRUE(rsa);

 // |RSA_generate_key_fips| may only be used for 2048-, 3072-, and 4096-bit
 // keys.
 for (const size_t bits : {512, 1024, 3071, 4095}) {
   SCOPED_TRACE(bits);

   rsa.reset(RSA_new());
   CALL_SERVICE_AND_CHECK_APPROVED(approved,
        ASSERT_FALSE(RSA_generate_key_fips(rsa.get(), bits, nullptr)));
   ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
 }

 // Test that we can generate keys of the supported lengths:
 for (const size_t bits : {2048, 3072, 4096}) {
   SCOPED_TRACE(bits);

   rsa.reset(RSA_new());
   CALL_SERVICE_AND_CHECK_APPROVED(approved,
             ASSERT_TRUE(RSA_generate_key_fips(rsa.get(), bits, nullptr)));
   ASSERT_EQ(approved, AWSLC_APPROVED);
   ASSERT_EQ(bits, BN_num_bits(rsa->n));
 }

  // Test running the EVP_PKEY_keygen interfaces one by one directly, and check
  // |EVP_PKEY_keygen| for approval at the end. |EVP_PKEY_keygen_init| should
  // not be approved because it does not indicate an entire service has been
  // done.
  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new_id(EVP_PKEY_RSA, nullptr));
  EVP_PKEY *raw = nullptr;
  bssl::UniquePtr<EVP_PKEY> pkey(raw);
  ASSERT_TRUE(ctx);
  // Test unapproved key sizes of RSA.
  for(const size_t bits : {512, 1024, 3071, 4095}) {
    SCOPED_TRACE(bits);
    CALL_SERVICE_AND_CHECK_APPROVED(approved,
            ASSERT_TRUE(EVP_PKEY_keygen_init(ctx.get())));
    ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
    ASSERT_TRUE(EVP_PKEY_CTX_set_rsa_keygen_bits(ctx.get(), bits));
    CALL_SERVICE_AND_CHECK_APPROVED(approved,
            ASSERT_FALSE(EVP_PKEY_keygen(ctx.get(), &raw)));
    ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
    // Prevent memory leakage.
    pkey.reset(raw);
    raw = nullptr;
  }
  // Test approved key sizes of RSA.
  for(const size_t bits : {2048, 3072, 4096}) {
    SCOPED_TRACE(bits);
    CALL_SERVICE_AND_CHECK_APPROVED(approved,
            ASSERT_TRUE(EVP_PKEY_keygen_init(ctx.get())));
    ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
    ASSERT_TRUE(EVP_PKEY_CTX_set_rsa_keygen_bits(ctx.get(), bits));
    CALL_SERVICE_AND_CHECK_APPROVED(approved,
            ASSERT_TRUE(EVP_PKEY_keygen(ctx.get(), &raw)));
    ASSERT_EQ(approved, AWSLC_APPROVED);
    // Prevent memory leakage.
    pkey.reset(raw);
    raw = nullptr;
  }
}

struct RSATestVector {
  // key_size is the input rsa key size.
  const int key_size;
  // md_func is the digest to test.
  const EVP_MD *(*func)();
  // whether to use pss testing or not.
  const bool use_pss;
  // expected to be approved or not for signature generation.
  const int sig_gen_expect_approved;
  // expected to be approved or not for signature verification.
  const int sig_ver_expect_approved;
};
struct RSATestVector kRSATestVectors[] = {
    // RSA test cases that are not approved in any case.
    { 512, &EVP_sha1, false, AWSLC_NOT_APPROVED, AWSLC_NOT_APPROVED },
    { 512, &EVP_sha256, true, AWSLC_NOT_APPROVED, AWSLC_NOT_APPROVED },
    { 1024, &EVP_md5, false, AWSLC_NOT_APPROVED, AWSLC_NOT_APPROVED },
    { 1536, &EVP_sha256, false, AWSLC_NOT_APPROVED, AWSLC_NOT_APPROVED },
    { 1536, &EVP_sha512, true, AWSLC_NOT_APPROVED, AWSLC_NOT_APPROVED },
    { 2048, &EVP_md5, false, AWSLC_NOT_APPROVED, AWSLC_NOT_APPROVED },
    { 3071, &EVP_md5, true, AWSLC_NOT_APPROVED, AWSLC_NOT_APPROVED },
    { 3071, &EVP_sha256, false, AWSLC_NOT_APPROVED, AWSLC_NOT_APPROVED },
    { 3071, &EVP_sha512, true, AWSLC_NOT_APPROVED, AWSLC_NOT_APPROVED },
    { 4096, &EVP_md5, false, AWSLC_NOT_APPROVED, AWSLC_NOT_APPROVED },

    // RSA test cases that are approved.
    { 1024, &EVP_sha1, false, AWSLC_NOT_APPROVED, AWSLC_APPROVED },
    { 1024, &EVP_sha256, false, AWSLC_NOT_APPROVED, AWSLC_APPROVED },
    { 1024, &EVP_sha512, false, AWSLC_NOT_APPROVED, AWSLC_APPROVED },
    { 1024, &EVP_sha1, true, AWSLC_NOT_APPROVED, AWSLC_APPROVED },
    { 1024, &EVP_sha256, true, AWSLC_NOT_APPROVED, AWSLC_APPROVED },
    { 1024, &EVP_sha512, true, AWSLC_NOT_APPROVED, AWSLC_APPROVED },

    { 2048, &EVP_sha1, false, AWSLC_NOT_APPROVED, AWSLC_APPROVED },
    { 2048, &EVP_sha224, false, AWSLC_APPROVED, AWSLC_APPROVED },
    { 2048, &EVP_sha256, false, AWSLC_APPROVED, AWSLC_APPROVED },
    { 2048, &EVP_sha384, false, AWSLC_APPROVED, AWSLC_APPROVED },
    { 2048, &EVP_sha512, false, AWSLC_APPROVED, AWSLC_APPROVED },
    { 2048, &EVP_sha1, true, AWSLC_NOT_APPROVED, AWSLC_APPROVED },
    { 2048, &EVP_sha224, true, AWSLC_APPROVED, AWSLC_APPROVED },
    { 2048, &EVP_sha256, true, AWSLC_APPROVED, AWSLC_APPROVED },
    { 2048, &EVP_sha384, true, AWSLC_APPROVED, AWSLC_APPROVED },
    { 2048, &EVP_sha512, true, AWSLC_APPROVED, AWSLC_APPROVED },

    { 3072, &EVP_sha1, false, AWSLC_NOT_APPROVED, AWSLC_APPROVED },
    { 3072, &EVP_sha224, false, AWSLC_APPROVED, AWSLC_APPROVED },
    { 3072, &EVP_sha256, false, AWSLC_APPROVED, AWSLC_APPROVED },
    { 3072, &EVP_sha384, false, AWSLC_APPROVED, AWSLC_APPROVED },
    { 3072, &EVP_sha512, false, AWSLC_APPROVED, AWSLC_APPROVED },
    { 3072, &EVP_sha1, true, AWSLC_NOT_APPROVED, AWSLC_APPROVED },
    { 3072, &EVP_sha224, true, AWSLC_APPROVED, AWSLC_APPROVED },
    { 3072, &EVP_sha256, true, AWSLC_APPROVED, AWSLC_APPROVED },
    { 3072, &EVP_sha384, true, AWSLC_APPROVED, AWSLC_APPROVED },
    { 3072, &EVP_sha512, true, AWSLC_APPROVED, AWSLC_APPROVED },

    { 4096, &EVP_sha1, false, AWSLC_NOT_APPROVED, AWSLC_APPROVED },
    { 4096, &EVP_sha224, false, AWSLC_APPROVED, AWSLC_APPROVED },
    { 4096, &EVP_sha256, false, AWSLC_APPROVED, AWSLC_APPROVED },
    { 4096, &EVP_sha384, false, AWSLC_APPROVED, AWSLC_APPROVED },
    { 4096, &EVP_sha512, false, AWSLC_APPROVED, AWSLC_APPROVED },
    { 4096, &EVP_sha1, true, AWSLC_NOT_APPROVED, AWSLC_APPROVED },
    { 4096, &EVP_sha224, true, AWSLC_APPROVED, AWSLC_APPROVED },
    { 4096, &EVP_sha256, true, AWSLC_APPROVED, AWSLC_APPROVED },
    { 4096, &EVP_sha384, true, AWSLC_APPROVED, AWSLC_APPROVED },
    { 4096, &EVP_sha512, true, AWSLC_APPROVED, AWSLC_APPROVED },
};

class RSA_ServiceIndicatorTest : public awslc::TestWithNoErrors<RSATestVector> {};

INSTANTIATE_TEST_SUITE_P(All, RSA_ServiceIndicatorTest, testing::ValuesIn(kRSATestVectors));

TEST_P(RSA_ServiceIndicatorTest, RSASigGen) {
  const RSATestVector &rsaTestVector = GetParam();

  int approved = AWSLC_NOT_APPROVED;
  RSA *rsa = RSA_new();
  bssl::UniquePtr<BIGNUM> e(BN_new());
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  bssl::ScopedEVP_MD_CTX md_ctx;
  EVP_PKEY_CTX *pctx;
  ASSERT_TRUE(pkey);
  ASSERT_TRUE(rsa);
  BN_set_word(e.get(), RSA_F4);

  // Generate a generic rsa key.
  ASSERT_TRUE(RSA_generate_key_ex(rsa, rsaTestVector.key_size, e.get(), nullptr));
  if(rsaTestVector.use_pss) {
    ASSERT_TRUE(EVP_PKEY_assign(pkey.get(), EVP_PKEY_RSA_PSS, rsa));
  } else {
    ASSERT_TRUE(EVP_PKEY_assign_RSA(pkey.get(), rsa));
  }

  // Test running the EVP_DigestSign interfaces one by one directly, and check
  // |EVP_DigestSignFinal| for approval at the end. |EVP_DigestSignInit|,
  // |EVP_DigestSignUpdate| should not be approved because they do not indicate
  // an entire service has been done.
  std::vector<uint8_t> final_output;
  size_t sig_len;
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
      ASSERT_TRUE(EVP_DigestSignInit(md_ctx.get(), &pctx, rsaTestVector.func(), nullptr, pkey.get())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  if(rsaTestVector.use_pss) {
    CALL_SERVICE_AND_CHECK_APPROVED(approved,
          ASSERT_TRUE(EVP_PKEY_CTX_set_rsa_padding(pctx, RSA_PKCS1_PSS_PADDING)));
    ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  }
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
      ASSERT_TRUE(EVP_DigestSignUpdate(md_ctx.get(), kPlaintext, sizeof(kPlaintext))));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  // Determine the size of the signature. The first call of |EVP_DigestSignFinal|
  // should not return an approval check because no crypto is being done when
  // |nullptr| is inputted in the |*out_sig| field.
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
      ASSERT_TRUE(EVP_DigestSignFinal(md_ctx.get(), nullptr, &sig_len)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  final_output.resize(sig_len);
  // The second call performs the actual operation.
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
            ASSERT_TRUE(EVP_DigestSignFinal(md_ctx.get(), final_output.data(), &sig_len)));
  ASSERT_EQ(approved, rsaTestVector.sig_gen_expect_approved);


  // Test using the one-shot |EVP_DigestSign| function for approval.
  md_ctx.Reset();
  std::vector<uint8_t> oneshot_output(sig_len);
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
      ASSERT_TRUE(EVP_DigestSignInit(md_ctx.get(), &pctx, rsaTestVector.func(), nullptr, pkey.get())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  if(rsaTestVector.use_pss) {
    CALL_SERVICE_AND_CHECK_APPROVED(approved,
          ASSERT_TRUE(EVP_PKEY_CTX_set_rsa_padding(pctx, RSA_PKCS1_PSS_PADDING)));
    ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  }
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
      ASSERT_TRUE(EVP_DigestSign(md_ctx.get(), oneshot_output.data(), &sig_len,
                                 kPlaintext, sizeof(kPlaintext))));
  ASSERT_EQ(approved, rsaTestVector.sig_gen_expect_approved);
}

TEST_P(RSA_ServiceIndicatorTest, RSASigVer) {
  const RSATestVector &rsaTestVector = GetParam();

  int approved = AWSLC_NOT_APPROVED;

  RSA *rsa = RSA_new();
  bssl::UniquePtr<BIGNUM> e(BN_new());
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  bssl::ScopedEVP_MD_CTX md_ctx;
  EVP_PKEY_CTX *pctx;
  ASSERT_TRUE(pkey);
  ASSERT_TRUE(rsa);
  BN_set_word(e.get(), RSA_F4);

  // Generate a generic rsa key.
  ASSERT_TRUE(RSA_generate_key_ex(rsa, rsaTestVector.key_size, e.get(), nullptr));
  if(rsaTestVector.use_pss) {
    ASSERT_TRUE(EVP_PKEY_assign(pkey.get(), EVP_PKEY_RSA_PSS, rsa));
  } else {
    ASSERT_TRUE(EVP_PKEY_assign_RSA(pkey.get(), rsa));
  }

  std::vector<uint8_t> signature;
  size_t sig_len;
  ASSERT_TRUE(EVP_DigestSignInit(md_ctx.get(), &pctx, rsaTestVector.func(), nullptr, pkey.get()));
  if(rsaTestVector.use_pss) {
    ASSERT_TRUE(EVP_PKEY_CTX_set_rsa_padding(pctx, RSA_PKCS1_PSS_PADDING));
  }
  ASSERT_TRUE(EVP_DigestSign(md_ctx.get(), nullptr, &sig_len, nullptr, 0));
  signature.resize(sig_len);
  ASSERT_TRUE(EVP_DigestSign(md_ctx.get(), signature.data(), &sig_len,
                             kPlaintext, sizeof(kPlaintext)));
  signature.resize(sig_len);

  // Service Indicator approval checks for RSA signature verification.

  // Test running the EVP_DigestVerify interfaces one by one directly, and check
  // |EVP_DigestVerifyFinal| for approval at the end. |EVP_DigestVerifyInit|,
  // |EVP_DigestVerifyUpdate| should not be approved because they do not indicate
  // an entire service has been done.
  md_ctx.Reset();
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
          ASSERT_TRUE(EVP_DigestVerifyInit(md_ctx.get(), &pctx, rsaTestVector.func(), nullptr, pkey.get())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  if(rsaTestVector.use_pss) {
    CALL_SERVICE_AND_CHECK_APPROVED(approved,
          ASSERT_TRUE(EVP_PKEY_CTX_set_rsa_padding(pctx, RSA_PKCS1_PSS_PADDING)));
    ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  }
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
          ASSERT_TRUE(EVP_DigestVerifyUpdate(md_ctx.get(), kPlaintext, sizeof(kPlaintext))));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
          ASSERT_TRUE(EVP_DigestVerifyFinal(md_ctx.get(), signature.data(), signature.size())));
  ASSERT_EQ(approved, rsaTestVector.sig_ver_expect_approved);

  // Test using the one-shot |EVP_DigestVerify| function for approval.
  md_ctx.Reset();
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
          ASSERT_TRUE(EVP_DigestVerifyInit(md_ctx.get(), &pctx, rsaTestVector.func(), nullptr, pkey.get())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  if(rsaTestVector.use_pss) {
    CALL_SERVICE_AND_CHECK_APPROVED(approved,
          ASSERT_TRUE(EVP_PKEY_CTX_set_rsa_padding(pctx, RSA_PKCS1_PSS_PADDING)));
    ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  }
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
          ASSERT_TRUE(EVP_DigestVerify(md_ctx.get(), signature.data(),
                                             signature.size(), kPlaintext,
                                             sizeof(kPlaintext))));
  ASSERT_EQ(approved, rsaTestVector.sig_ver_expect_approved);
}

// Test that |EVP_DigestSignFinal| and |EVP_DigestSignVerify| are approved with
// manually constructing using the context setting functions.
TEST_P(RSA_ServiceIndicatorTest, ManualRSASignVerify) {
  const RSATestVector &rsaTestVector = GetParam();

  int approved = AWSLC_NOT_APPROVED;

  bssl::ScopedEVP_MD_CTX ctx;
  ASSERT_TRUE(EVP_DigestInit(ctx.get(), rsaTestVector.func()));
  ASSERT_TRUE(EVP_DigestUpdate(ctx.get(), kPlaintext, sizeof(kPlaintext)));

  RSA *rsa = RSA_new();
  bssl::UniquePtr<BIGNUM> e(BN_new());
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  BN_set_word(e.get(), RSA_F4);

  // Generate a generic rsa key.
  ASSERT_TRUE(RSA_generate_key_ex(rsa, rsaTestVector.key_size, e.get(), nullptr));
  if(rsaTestVector.use_pss) {
    ASSERT_TRUE(EVP_PKEY_assign(pkey.get(), EVP_PKEY_RSA_PSS, rsa));
  } else {
    ASSERT_TRUE(EVP_PKEY_assign_RSA(pkey.get(), rsa));
  }

  // Manual construction for signing.
  bssl::UniquePtr<EVP_PKEY_CTX> pctx(EVP_PKEY_CTX_new(pkey.get(), nullptr));
  ASSERT_TRUE(EVP_PKEY_sign_init(pctx.get()));
  ASSERT_TRUE(EVP_PKEY_CTX_set_signature_md(pctx.get(), rsaTestVector.func()));
  EVP_MD_CTX_set_pkey_ctx(ctx.get(), pctx.get());
  // Determine the size of the signature.
  size_t sig_len = 0;
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
                ASSERT_TRUE(EVP_DigestSignFinal(ctx.get(), nullptr, &sig_len)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);

  std::vector<uint8_t> sig;
  sig.resize(sig_len);
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
            ASSERT_TRUE(EVP_DigestSignFinal(ctx.get(), sig.data(), &sig_len)));
  ASSERT_EQ(approved, rsaTestVector.sig_gen_expect_approved);
  sig.resize(sig_len);

  // Manual construction for verification.
  ASSERT_TRUE(EVP_PKEY_verify_init(pctx.get()));
  ASSERT_TRUE(EVP_PKEY_CTX_set_signature_md(pctx.get(), rsaTestVector.func()));
  EVP_MD_CTX_set_pkey_ctx(ctx.get(), pctx.get());

  CALL_SERVICE_AND_CHECK_APPROVED(approved,
            ASSERT_TRUE(EVP_DigestVerifyFinal(ctx.get(), sig.data(), sig_len)));
  ASSERT_EQ(approved, rsaTestVector.sig_ver_expect_approved);
}

struct ECDSATestVector {
  // nid is the input curve nid.
  const int nid;
  // md_func is the digest to test.
  const EVP_MD *(*func)();
  // expected to be approved or not for signature generation.
  const int key_check_expect_approved;
  // expected to be approved or not for signature generation.
  const int sig_gen_expect_approved;
  // expected to be approved or not for signature verification.
  const int sig_ver_expect_approved;
};
struct ECDSATestVector kECDSATestVectors[] = {
    // Only the following NIDs for |EC_GROUP| are creatable with
    // |EC_GROUP_new_by_curve_name|.
    { NID_secp224r1, &EVP_sha1, AWSLC_APPROVED, AWSLC_NOT_APPROVED, AWSLC_APPROVED },
    { NID_secp224r1, &EVP_sha224, AWSLC_APPROVED, AWSLC_APPROVED, AWSLC_APPROVED },
    { NID_secp224r1, &EVP_sha256, AWSLC_APPROVED, AWSLC_APPROVED, AWSLC_APPROVED },
    { NID_secp224r1, &EVP_sha384, AWSLC_APPROVED, AWSLC_APPROVED, AWSLC_APPROVED },
    { NID_secp224r1, &EVP_sha512, AWSLC_APPROVED, AWSLC_APPROVED, AWSLC_APPROVED },

    { NID_X9_62_prime256v1, &EVP_sha1, AWSLC_APPROVED, AWSLC_NOT_APPROVED, AWSLC_APPROVED },
    { NID_X9_62_prime256v1, &EVP_sha224, AWSLC_APPROVED, AWSLC_APPROVED, AWSLC_APPROVED },
    { NID_X9_62_prime256v1, &EVP_sha256, AWSLC_APPROVED, AWSLC_APPROVED, AWSLC_APPROVED },
    { NID_X9_62_prime256v1, &EVP_sha384, AWSLC_APPROVED, AWSLC_APPROVED, AWSLC_APPROVED },
    { NID_X9_62_prime256v1, &EVP_sha512, AWSLC_APPROVED, AWSLC_APPROVED, AWSLC_APPROVED },

    { NID_secp384r1, &EVP_sha1, AWSLC_APPROVED, AWSLC_NOT_APPROVED, AWSLC_APPROVED },
    { NID_secp384r1, &EVP_sha224, AWSLC_APPROVED, AWSLC_APPROVED, AWSLC_APPROVED },
    { NID_secp384r1, &EVP_sha256, AWSLC_APPROVED, AWSLC_APPROVED, AWSLC_APPROVED },
    { NID_secp384r1, &EVP_sha384, AWSLC_APPROVED, AWSLC_APPROVED, AWSLC_APPROVED },
    { NID_secp384r1, &EVP_sha512, AWSLC_APPROVED, AWSLC_APPROVED, AWSLC_APPROVED },

    { NID_secp521r1, &EVP_sha1, AWSLC_APPROVED, AWSLC_NOT_APPROVED, AWSLC_APPROVED },
    { NID_secp521r1, &EVP_sha224, AWSLC_APPROVED, AWSLC_APPROVED, AWSLC_APPROVED },
    { NID_secp521r1, &EVP_sha256, AWSLC_APPROVED, AWSLC_APPROVED, AWSLC_APPROVED },
    { NID_secp521r1, &EVP_sha384, AWSLC_APPROVED, AWSLC_APPROVED, AWSLC_APPROVED },
    { NID_secp521r1, &EVP_sha512, AWSLC_APPROVED, AWSLC_APPROVED, AWSLC_APPROVED },
};

class ECDSA_ServiceIndicatorTest : public awslc::TestWithNoErrors<ECDSATestVector> {};

INSTANTIATE_TEST_SUITE_P(All, ECDSA_ServiceIndicatorTest, testing::ValuesIn(kECDSATestVectors));

TEST_P(ECDSA_ServiceIndicatorTest, ECDSAKeyCheck) {
  const ECDSATestVector &ecdsaTestVector = GetParam();

  int approved = AWSLC_NOT_APPROVED;

  // Test service indicator approval for |EC_KEY_generate_key_fips| and
  // |EC_KEY_check_fips|.
  bssl::UniquePtr<EC_KEY> key(EC_KEY_new_by_curve_name(ecdsaTestVector.nid));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EC_KEY_generate_key_fips(key.get())));
  ASSERT_EQ(approved, ecdsaTestVector.key_check_expect_approved);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EC_KEY_check_fips(key.get())));
  ASSERT_EQ(approved, ecdsaTestVector.key_check_expect_approved);
  // Remove reference to private key in generated key and see if
  // |EC_KEY_check_fips| still returns approval for keys with only public keys
  // available.
  bssl::UniquePtr<EC_KEY> key_only_public(EC_KEY_new_by_curve_name(ecdsaTestVector.nid));
  ASSERT_TRUE(EC_KEY_set_public_key(key_only_public.get(), EC_KEY_get0_public_key(key.get())));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EC_KEY_check_fips(key_only_public.get())));
  ASSERT_EQ(approved, ecdsaTestVector.key_check_expect_approved);

  // Test running the EVP_PKEY_keygen interfaces one by one directly, and check
  // |EVP_PKEY_keygen| for approval at the end. |EVP_PKEY_keygen_init| should
  // not be approved because they do not indicate an entire service has been
  // done.
  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new_id(EVP_PKEY_EC, nullptr));
  EVP_PKEY *raw = nullptr;
  ASSERT_TRUE(ctx);
  ASSERT_TRUE(EVP_PKEY_keygen_init(ctx.get()));
  ASSERT_TRUE(EVP_PKEY_CTX_set_ec_paramgen_curve_nid(ctx.get(), ecdsaTestVector.nid));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_PKEY_keygen(ctx.get(), &raw)));
  // Prevent memory leakage.
  bssl::UniquePtr<EVP_PKEY> pkey(raw);
  raw = nullptr;
  ASSERT_EQ(approved, ecdsaTestVector.key_check_expect_approved);
}

TEST_P(ECDSA_ServiceIndicatorTest, ECDSASigGen) {
  const ECDSATestVector &ecdsaTestVector = GetParam();

  int approved = AWSLC_NOT_APPROVED;

  bssl::UniquePtr<EC_GROUP> group(
      EC_GROUP_new_by_curve_name(ecdsaTestVector.nid));
  bssl::UniquePtr<EC_KEY> eckey(EC_KEY_new());
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  bssl::ScopedEVP_MD_CTX md_ctx;
  ASSERT_TRUE(eckey);
  ASSERT_TRUE(EC_KEY_set_group(eckey.get(), group.get()));

  // Generate a generic ec key.
  EC_KEY_generate_key(eckey.get());
  ASSERT_TRUE(EVP_PKEY_set1_EC_KEY(pkey.get(), eckey.get()));

  // Test running the EVP_DigestSign interfaces one by one directly, and check
  // |EVP_DigestSignFinal| for approval at the end. |EVP_DigestSignInit|,
  // |EVP_DigestSignUpdate| should not be approved because they do not indicate
  // an entire service has been done.
  std::vector<uint8_t> final_output;
  size_t sig_len;
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
        ASSERT_TRUE(EVP_DigestSignInit(md_ctx.get(), nullptr, ecdsaTestVector.func(), nullptr, pkey.get())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
        ASSERT_TRUE(EVP_DigestSignUpdate(md_ctx.get(), kPlaintext, sizeof(kPlaintext))));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  // Determine the size of the signature. The first call of |EVP_DigestSignFinal|
  // should not return an approval check because no crypto is being done when
  // |nullptr| is inputted in the |*out_sig| field.
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
    ASSERT_TRUE(EVP_DigestSignFinal(md_ctx.get(), nullptr, &sig_len)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  final_output.resize(sig_len);
  // The second call performs the actual operation.
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
              ASSERT_TRUE(EVP_DigestSignFinal(md_ctx.get(), final_output.data(), &sig_len)));
  ASSERT_EQ(approved, ecdsaTestVector.sig_gen_expect_approved);


  // Test using the one-shot |EVP_DigestSign| function for approval.
  md_ctx.Reset();
  std::vector<uint8_t> oneshot_output;
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
          ASSERT_TRUE(EVP_DigestSignInit(md_ctx.get(), nullptr, ecdsaTestVector.func(), nullptr, pkey.get())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  ASSERT_TRUE(EVP_DigestSignFinal(md_ctx.get(), nullptr, &sig_len));
  oneshot_output.resize(sig_len);
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
                ASSERT_TRUE(EVP_DigestSign(md_ctx.get(), oneshot_output.data(), &sig_len,
                             kPlaintext, sizeof(kPlaintext))));
  ASSERT_EQ(approved, ecdsaTestVector.sig_gen_expect_approved);
}

TEST_P(ECDSA_ServiceIndicatorTest, ECDSASigVer) {
  const ECDSATestVector &ecdsaTestVector = GetParam();

  int approved = AWSLC_NOT_APPROVED;

  bssl::UniquePtr<EC_GROUP> group(
      EC_GROUP_new_by_curve_name(ecdsaTestVector.nid));
  bssl::UniquePtr<EC_KEY> eckey(EC_KEY_new());
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  bssl::ScopedEVP_MD_CTX md_ctx;
  ASSERT_TRUE(eckey);
  ASSERT_TRUE(EC_KEY_set_group(eckey.get(), group.get()));

  // Generate ECDSA signatures for ECDSA verification.
  EC_KEY_generate_key(eckey.get());
  ASSERT_TRUE(EVP_PKEY_set1_EC_KEY(pkey.get(), eckey.get()));
  std::vector<uint8_t> signature;
  size_t sig_len = 0;
  ASSERT_TRUE(EVP_DigestSignInit(md_ctx.get(), nullptr, ecdsaTestVector.func(),
                                 nullptr, pkey.get()));
  ASSERT_TRUE(EVP_DigestSignFinal(md_ctx.get(), nullptr, &sig_len));
  signature.resize(sig_len);
  ASSERT_TRUE(EVP_DigestSign(md_ctx.get(), signature.data(), &sig_len,
                             kPlaintext, sizeof(kPlaintext)));
  signature.resize(sig_len);

  // Service Indicator approval checks for ECDSA signature verification.

  // Test running the EVP_DigestVerify interfaces one by one directly, and check
  // |EVP_DigestVerifyFinal| for approval at the end. |EVP_DigestVerifyInit|,
  // |EVP_DigestVerifyUpdate| should not be approved because they do not indicate
  // an entire service has been done.
  md_ctx.Reset();
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
      ASSERT_TRUE(EVP_DigestVerifyInit(md_ctx.get(), nullptr, ecdsaTestVector.func(), nullptr, pkey.get())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
      ASSERT_TRUE(EVP_DigestVerifyUpdate(md_ctx.get(), kPlaintext, sizeof(kPlaintext))));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
      ASSERT_TRUE(EVP_DigestVerifyFinal(md_ctx.get(), signature.data(), signature.size())));
  ASSERT_EQ(approved, ecdsaTestVector.sig_ver_expect_approved);

  // Test using the one-shot |EVP_DigestVerify| function for approval.
  md_ctx.Reset();
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
            ASSERT_TRUE(EVP_DigestVerifyInit(md_ctx.get(), nullptr, ecdsaTestVector.func(), nullptr, pkey.get())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(
      approved, ASSERT_TRUE(EVP_DigestVerify(md_ctx.get(), signature.data(),
                                             signature.size(), kPlaintext,
                                             sizeof(kPlaintext))));
  ASSERT_EQ(approved, ecdsaTestVector.sig_ver_expect_approved);
}

// Test that |EVP_DigestSignFinal| and |EVP_DigestSignVerify| are approved with
// manually constructing using the context setting functions.
TEST_P(ECDSA_ServiceIndicatorTest, ManualECDSASignVerify) {
  const ECDSATestVector &ecdsaTestVector = GetParam();

  int approved = AWSLC_NOT_APPROVED;

  bssl::ScopedEVP_MD_CTX ctx;
  ASSERT_TRUE(EVP_DigestInit(ctx.get(), ecdsaTestVector.func()));
  ASSERT_TRUE(EVP_DigestUpdate(ctx.get(), kPlaintext, sizeof(kPlaintext)));

  bssl::UniquePtr<EC_GROUP> group(
      EC_GROUP_new_by_curve_name(ecdsaTestVector.nid));
  bssl::UniquePtr<EC_KEY> eckey(EC_KEY_new());
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  bssl::ScopedEVP_MD_CTX md_ctx;
  ASSERT_TRUE(eckey);
  ASSERT_TRUE(EC_KEY_set_group(eckey.get(), group.get()));

  // Generate a generic ec key.
  EC_KEY_generate_key(eckey.get());
  ASSERT_TRUE(EVP_PKEY_set1_EC_KEY(pkey.get(), eckey.get()));

  // Manual construction for signing.
  bssl::UniquePtr<EVP_PKEY_CTX> pctx(EVP_PKEY_CTX_new(pkey.get(), nullptr));
  ASSERT_TRUE(EVP_PKEY_sign_init(pctx.get()));
  ASSERT_TRUE(EVP_PKEY_CTX_set_signature_md(pctx.get(), ecdsaTestVector.func()));
  EVP_MD_CTX_set_pkey_ctx(ctx.get(), pctx.get());
  // Determine the size of the signature.
  size_t sig_len = 0;
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
                ASSERT_TRUE(EVP_DigestSignFinal(ctx.get(), nullptr, &sig_len)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);

  std::vector<uint8_t> sig;
  sig.resize(sig_len);
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
            ASSERT_TRUE(EVP_DigestSignFinal(ctx.get(), sig.data(), &sig_len)));
  ASSERT_EQ(approved, ecdsaTestVector.sig_gen_expect_approved);
  sig.resize(sig_len);

  // Manual construction for verification.
  ASSERT_TRUE(EVP_PKEY_verify_init(pctx.get()));
  ASSERT_TRUE(EVP_PKEY_CTX_set_signature_md(pctx.get(), ecdsaTestVector.func()));
  EVP_MD_CTX_set_pkey_ctx(ctx.get(), pctx.get());

  CALL_SERVICE_AND_CHECK_APPROVED(approved,
            ASSERT_TRUE(EVP_DigestVerifyFinal(ctx.get(), sig.data(), sig_len)));
  ASSERT_EQ(approved, ecdsaTestVector.sig_ver_expect_approved);
}

struct ECDHTestVector {
  // nid is the input curve nid.
  const int nid;
  // md_func is the digest to test.
  const int digest_length;
  // expected to be approved or not.
  const int expect_approved;
};
struct ECDHTestVector kECDHTestVectors[] = {
    // Only the following NIDs for |EC_GROUP| are creatable with
    // |EC_GROUP_new_by_curve_name|.
    // |ECDH_compute_key_fips| fails directly when an invalid hash length is
    // inputted.
    { NID_secp224r1, SHA224_DIGEST_LENGTH, AWSLC_APPROVED },
    { NID_secp224r1, SHA256_DIGEST_LENGTH, AWSLC_APPROVED },
    { NID_secp224r1, SHA384_DIGEST_LENGTH, AWSLC_APPROVED },
    { NID_secp224r1, SHA512_DIGEST_LENGTH, AWSLC_APPROVED },

    { NID_X9_62_prime256v1, SHA224_DIGEST_LENGTH, AWSLC_APPROVED },
    { NID_X9_62_prime256v1, SHA256_DIGEST_LENGTH, AWSLC_APPROVED },
    { NID_X9_62_prime256v1, SHA384_DIGEST_LENGTH, AWSLC_APPROVED },
    { NID_X9_62_prime256v1, SHA512_DIGEST_LENGTH, AWSLC_APPROVED },

    { NID_secp384r1, SHA224_DIGEST_LENGTH, AWSLC_APPROVED },
    { NID_secp384r1, SHA256_DIGEST_LENGTH, AWSLC_APPROVED },
    { NID_secp384r1, SHA384_DIGEST_LENGTH, AWSLC_APPROVED },
    { NID_secp384r1, SHA512_DIGEST_LENGTH, AWSLC_APPROVED },

    { NID_secp521r1, SHA224_DIGEST_LENGTH, AWSLC_APPROVED },
    { NID_secp521r1, SHA256_DIGEST_LENGTH, AWSLC_APPROVED },
    { NID_secp521r1, SHA384_DIGEST_LENGTH, AWSLC_APPROVED },
    { NID_secp521r1, SHA512_DIGEST_LENGTH, AWSLC_APPROVED },
};

class ECDH_ServiceIndicatorTest : public awslc::TestWithNoErrors<ECDHTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, ECDH_ServiceIndicatorTest, testing::ValuesIn(kECDHTestVectors));

TEST_P(ECDH_ServiceIndicatorTest, ECDH) {
  const ECDHTestVector &ecdhTestVector = GetParam();

  int approved = AWSLC_NOT_APPROVED;

  bssl::UniquePtr<EC_GROUP> group(EC_GROUP_new_by_curve_name(ecdhTestVector.nid));
  bssl::UniquePtr<EC_KEY> our_key(EC_KEY_new());
  bssl::UniquePtr<EC_KEY> peer_key(EC_KEY_new());
  bssl::ScopedEVP_MD_CTX md_ctx;
  ASSERT_TRUE(our_key);
  ASSERT_TRUE(peer_key);

  // Generate two generic ec key pairs.
  ASSERT_TRUE(EC_KEY_set_group(our_key.get(), group.get()));
  ASSERT_TRUE(EC_KEY_generate_key(our_key.get()));
  ASSERT_TRUE(EC_KEY_check_key(our_key.get()));

  ASSERT_TRUE(EC_KEY_set_group(peer_key.get(), group.get()));
  ASSERT_TRUE(EC_KEY_generate_key(peer_key.get()));
  ASSERT_TRUE(EC_KEY_check_key(peer_key.get()));

  // Test that |ECDH_compute_key_fips| has service indicator approval as
  // expected.
  std::vector<uint8_t> digest(ecdhTestVector.digest_length);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(ECDH_compute_key_fips(digest.data(),
                              digest.size(), EC_KEY_get0_public_key(peer_key.get()), our_key.get())));
  ASSERT_EQ(approved, ecdhTestVector.expect_approved);

  // Test running the EVP_PKEY_derive interfaces one by one directly, and check
  // |EVP_PKEY_derive| for approval at the end. |EVP_PKEY_derive_init|,
  // |EVP_PKEY_derive_set_peer| should not be approved because they do not indicate
  // an entire service has been done.
  std::vector<uint8_t> derive_output;
  size_t out_len = 0;
  bssl::UniquePtr<EVP_PKEY> our_pkey(EVP_PKEY_new());
  ASSERT_TRUE(EVP_PKEY_set1_EC_KEY(our_pkey.get(), our_key.get()));
  bssl::UniquePtr<EVP_PKEY_CTX> our_ctx(EVP_PKEY_CTX_new(our_pkey.get(), nullptr));
  bssl::UniquePtr<EVP_PKEY> peer_pkey(EVP_PKEY_new());
  ASSERT_TRUE(EVP_PKEY_set1_EC_KEY(peer_pkey.get(), peer_key.get()));

  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_PKEY_derive_init(our_ctx.get())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_PKEY_derive_set_peer(our_ctx.get(), peer_pkey.get())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  // Determine the size of the output key. The first call of |EVP_PKEY_derive|
  // should not return an approval check because no crypto is being done when
  // |nullptr| is inputted in the |*key| field
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_PKEY_derive(our_ctx.get(), nullptr, &out_len)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  derive_output.resize(out_len);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_PKEY_derive(our_ctx.get(), derive_output.data(), &out_len)));
  derive_output.resize(out_len);
  ASSERT_EQ(approved, AWSLC_APPROVED);
}

struct KDFTestVector {
  // func is the hash function for KDF to test.
  const EVP_MD *(*func)();
  const uint8_t *expected_output;
  const int expect_approved;
} kKDFTestVectors[] = {
    { EVP_md5, kTLSOutput_md, AWSLC_APPROVED },
    { EVP_sha1, kTLSOutput_sha1, AWSLC_APPROVED },
    { EVP_md5_sha1, kTLSOutput_mdsha1, AWSLC_APPROVED },
    { EVP_sha224, kTLSOutput_sha224, AWSLC_NOT_APPROVED },
    { EVP_sha256, kTLSOutput_sha256, AWSLC_APPROVED },
    { EVP_sha384, kTLSOutput_sha384, AWSLC_APPROVED },
    { EVP_sha512, kTLSOutput_sha512, AWSLC_APPROVED },
};

class KDF_ServiceIndicatorTest : public awslc::TestWithNoErrors<KDFTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, KDF_ServiceIndicatorTest, testing::ValuesIn(kKDFTestVectors));

TEST_P(KDF_ServiceIndicatorTest, KDF) {
  const KDFTestVector &kdfTestVector = GetParam();

  int approved = AWSLC_NOT_APPROVED;

  std::vector<uint8_t> tls_output(32);
  CALL_SERVICE_AND_CHECK_APPROVED(
      approved, ASSERT_TRUE(CRYPTO_tls1_prf(kdfTestVector.func(),
                                tls_output.data(), tls_output.size(),
                                kTLSSecret, sizeof(kTLSSecret), kTLSLabel,
                                sizeof(kTLSLabel), kTLSSeed1, sizeof(kTLSSeed1),
                                kTLSSeed2, sizeof(kTLSSeed2))));
  ASSERT_TRUE(check_test(kdfTestVector.expected_output, tls_output.data(),
                         tls_output.size(), "TLS KDF KAT"));
  ASSERT_EQ(approved, kdfTestVector.expect_approved);
}

TEST(ServiceIndicatorTest, CMAC) {
  int approved = AWSLC_NOT_APPROVED;

  std::vector<uint8_t> mac(16);
  size_t out_len;
  bssl::UniquePtr<CMAC_CTX> ctx(CMAC_CTX_new());
  ASSERT_TRUE(ctx);

  // Test running the CMAC interfaces one by one directly, and check
  // |CMAC_Final| for approval at the end. |CMAC_Init| and |CMAC_Update|
  // should not be approved, because the functions do not indicate that a
  // service has been fully completed yet.
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(CMAC_Init(ctx.get(), kAESKey, sizeof(kAESKey), EVP_aes_128_cbc(), nullptr)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(CMAC_Update(ctx.get(), kPlaintext, sizeof(kPlaintext))));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(CMAC_Final(ctx.get(), mac.data(), &out_len)));
  ASSERT_EQ(approved, AWSLC_APPROVED);
  ASSERT_TRUE(check_test(kAESCMACOutput, mac.data(), sizeof(kAESCMACOutput), "AES-CMAC KAT"));

  // Test using the one-shot API for approval.
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(AES_CMAC(mac.data(), kAESKey, sizeof(kAESKey),
                                                    kPlaintext, sizeof(kPlaintext))));
  ASSERT_TRUE(check_test(kAESCMACOutput, mac.data(), sizeof(kAESCMACOutput), "AES-CMAC KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);
}

TEST(ServiceIndicatorTest, BasicTest) {
  int approved = AWSLC_NOT_APPROVED;

  bssl::ScopedEVP_AEAD_CTX aead_ctx;
  AES_KEY aes_key;
  uint8_t aes_iv[sizeof(kAESIV)];
  uint8_t output[256];
  size_t out_len;
  int num = 0;
  int counter_before, counter_after;

  ASSERT_TRUE(EVP_AEAD_CTX_init(aead_ctx.get(), EVP_aead_aes_128_gcm_randnonce(),
                                kAESKey, sizeof(kAESKey), 0, nullptr));
  // Because the service indicator gets initialised in |FIPS_service_indicator_update_state|, which
  // is called by all approved services, the self_test run at the beginning would have updated it
  // more than once. The following test ensures that it's not zero and that it gets updated by calling
  // an approved service without calling |FIPS_service_indicator_before_call| first, which can init the counter,
  // but instead calling |FIPS_service_indicator_after_call|
  // This test also ensures that the counter gets incremented once, i.e. it was locked through the internal calls.
  counter_before = FIPS_service_indicator_after_call();
  ASSERT_NE(counter_before, 0);
  EVP_AEAD_CTX_seal(aead_ctx.get(),
                    output, &out_len, sizeof(output), nullptr, 0, kPlaintext, sizeof(kPlaintext), nullptr, 0);
  counter_after = FIPS_service_indicator_after_call();
  ASSERT_EQ(counter_after, counter_before+1);

  // Call an approved service.
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
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_ofb128_encrypt(kPlaintext, output,
                                   sizeof(kPlaintext), &aes_key, aes_iv, &num));
  ASSERT_TRUE(check_test(kAESOFBCiphertext, output, sizeof(kAESOFBCiphertext),
                         "AES-OFB Encryption KAT"));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
}

// Test the SHA interfaces one by one and check that only |*_Final| does the
// approval at the end.
TEST(ServiceIndicatorTest, SHA) {
  int approved = AWSLC_NOT_APPROVED;

  std::vector<uint8_t> plaintext(kPlaintext, kPlaintext + sizeof(kPlaintext));
  std::vector<uint8_t> digest;

  digest.resize(MD4_DIGEST_LENGTH);
  MD4_CTX md4_ctx;
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(MD4_Init(&md4_ctx)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(MD4_Update(&md4_ctx, plaintext.data(), plaintext.size())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(MD4_Final(digest.data(), &md4_ctx)));
  ASSERT_TRUE(check_test(kOutput_md4, digest.data(), sizeof(kOutput_md4), "MD4 Hash KAT"));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);

  digest.resize(MD5_DIGEST_LENGTH);
  MD5_CTX md5_ctx;
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(MD5_Init(&md5_ctx)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(MD5_Update(&md5_ctx, plaintext.data(), plaintext.size())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(MD5_Final(digest.data(), &md5_ctx)));
  ASSERT_TRUE(check_test(kOutput_md5, digest.data(), sizeof(kOutput_md5), "MD5 Hash KAT"));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);

  digest.clear();
  digest.resize(SHA_DIGEST_LENGTH);
  SHA_CTX sha_ctx;
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA1_Init(&sha_ctx)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA1_Update(&sha_ctx, plaintext.data(), plaintext.size())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA1_Final(digest.data(), &sha_ctx)));
  ASSERT_TRUE(check_test(kOutput_sha1, digest.data(), sizeof(kOutput_sha1), "SHA1 Hash KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  digest.clear();
  digest.resize(SHA224_DIGEST_LENGTH);
  SHA256_CTX sha224_ctx;
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA224_Init(&sha224_ctx)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA224_Update(&sha224_ctx, plaintext.data(), plaintext.size())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA224_Final(digest.data(), &sha224_ctx)));
  ASSERT_TRUE(check_test(kOutput_sha224, digest.data(), sizeof(kOutput_sha224), "SHA224 Hash KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  digest.clear();
  digest.resize(SHA256_DIGEST_LENGTH);
  SHA256_CTX sha256_ctx;
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA256_Init(&sha256_ctx)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA256_Update(&sha256_ctx, plaintext.data(), plaintext.size())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA256_Final(digest.data(), &sha256_ctx)));
  ASSERT_TRUE(check_test(kOutput_sha256, digest.data(), sizeof(kOutput_sha256), "SHA256 Hash KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  digest.clear();
  digest.resize(SHA384_DIGEST_LENGTH);
  SHA512_CTX sha384_ctx;
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA384_Init(&sha384_ctx)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA384_Update(&sha384_ctx, plaintext.data(), plaintext.size())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA384_Final(digest.data(), &sha384_ctx)));
  ASSERT_TRUE(check_test(kOutput_sha384, digest.data(), sizeof(kOutput_sha384), "SHA384 Hash KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  digest.clear();
  digest.resize(SHA512_DIGEST_LENGTH);
  SHA512_CTX sha512_ctx;
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA512_Init(&sha512_ctx)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA512_Update(&sha512_ctx, plaintext.data(), plaintext.size())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA512_Final(digest.data(), &sha512_ctx)));
  ASSERT_TRUE(check_test(kOutput_sha512, digest.data(), sizeof(kOutput_sha512), "SHA512 Hash KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  digest.clear();
  digest.resize(SHA512_256_DIGEST_LENGTH);
  SHA512_CTX sha512_256_ctx;
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA512_256_Init(&sha512_256_ctx)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA512_256_Update(&sha512_256_ctx, plaintext.data(), plaintext.size())));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(SHA512_256_Final(digest.data(), &sha512_256_ctx)));
  ASSERT_TRUE(check_test(kOutput_sha512_256, digest.data(), sizeof(kOutput_sha512_256), "SHA512-256 Hash KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);
}

TEST(ServiceIndicatorTest, AESECB) {
  int approved = AWSLC_NOT_APPROVED;

  AES_KEY aes_key;
  uint8_t output[256];

  // AES-ECB Encryption KAT for 128 bit key.
  ASSERT_TRUE(AES_set_encrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key) == 0);
  // AES_ecb_encrypt encrypts (or decrypts) a single, 16 byte block from in to out.
  for (size_t j = 0; j < sizeof(kPlaintext) / AES_BLOCK_SIZE; j++) {
    CALL_SERVICE_AND_CHECK_APPROVED(approved,
      AES_ecb_encrypt(&kPlaintext[j * AES_BLOCK_SIZE], &output[j * AES_BLOCK_SIZE], &aes_key, AES_ENCRYPT));
    ASSERT_EQ(approved, AWSLC_APPROVED);
  }
  ASSERT_TRUE(check_test(kAESECBCiphertext, output, sizeof(kAESECBCiphertext),
                         "AES-ECB Encryption KAT for 128 bit key"));

  // AES-ECB Decryption KAT for 128 bit key.
  ASSERT_TRUE(AES_set_decrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key) == 0);
  for (size_t j = 0; j < sizeof(kPlaintext) / AES_BLOCK_SIZE; j++) {
    CALL_SERVICE_AND_CHECK_APPROVED(approved,
      AES_ecb_encrypt(&kAESECBCiphertext[j * AES_BLOCK_SIZE], &output[j * AES_BLOCK_SIZE], &aes_key, AES_DECRYPT));
    ASSERT_EQ(approved, AWSLC_APPROVED);
  }
  ASSERT_TRUE(check_test(kPlaintext, output, sizeof(kPlaintext),
                         "AES-ECB Decryption KAT for 128 bit key"));

  // AES-ECB Encryption KAT for 192 bit key.
  ASSERT_TRUE(AES_set_encrypt_key(kAESKey_192, 8 * sizeof(kAESKey_192), &aes_key) == 0);
  for (size_t j = 0; j < sizeof(kPlaintext) / AES_BLOCK_SIZE; j++) {
    CALL_SERVICE_AND_CHECK_APPROVED(approved,
      AES_ecb_encrypt(&kPlaintext[j * AES_BLOCK_SIZE], &output[j * AES_BLOCK_SIZE], &aes_key, AES_ENCRYPT));
    ASSERT_EQ(approved, AWSLC_APPROVED);
  }
  ASSERT_TRUE(check_test(kAESECBCiphertext_192, output, sizeof(kAESECBCiphertext_192),
                         "AES-ECB Encryption KAT for 192 bit key"));

  // AES-ECB Decryption KAT for 192 bit key.
  ASSERT_TRUE(AES_set_decrypt_key(kAESKey_192, 8 * sizeof(kAESKey_192), &aes_key) == 0);
  for (size_t j = 0; j < sizeof(kPlaintext) / AES_BLOCK_SIZE; j++) {
    CALL_SERVICE_AND_CHECK_APPROVED(approved,
      AES_ecb_encrypt(&kAESECBCiphertext_192[j * AES_BLOCK_SIZE], &output[j * AES_BLOCK_SIZE], &aes_key, AES_DECRYPT));
    ASSERT_EQ(approved, AWSLC_APPROVED);
  }
  ASSERT_TRUE(check_test(kPlaintext, output, sizeof(kPlaintext),
                         "AES-ECB Decryption KAT for 192 bit key"));

  // AES-ECB Encryption KAT for 256 bit key.
  ASSERT_TRUE(AES_set_encrypt_key(kAESKey_256, 8 * sizeof(kAESKey_256), &aes_key) == 0);
  for (size_t j = 0; j < sizeof(kPlaintext) / AES_BLOCK_SIZE; j++) {
    CALL_SERVICE_AND_CHECK_APPROVED(approved,
      AES_ecb_encrypt(&kPlaintext[j * AES_BLOCK_SIZE], &output[j * AES_BLOCK_SIZE], &aes_key, AES_ENCRYPT));
    ASSERT_EQ(approved, AWSLC_APPROVED);
  }
  ASSERT_TRUE(check_test(kAESECBCiphertext_256, output, sizeof(kAESECBCiphertext_256),
                         "AES-ECB Encryption KAT for 256 bit key"));

  // AES-ECB Decryption KAT for 256 bit key.
  ASSERT_TRUE(AES_set_decrypt_key(kAESKey_256, 8 * sizeof(kAESKey_256), &aes_key) == 0);
  for (size_t j = 0; j < sizeof(kPlaintext) / AES_BLOCK_SIZE; j++) {
    CALL_SERVICE_AND_CHECK_APPROVED(approved,
      AES_ecb_encrypt(&kAESECBCiphertext_256[j * AES_BLOCK_SIZE], &output[j * AES_BLOCK_SIZE], &aes_key, AES_DECRYPT));
    ASSERT_EQ(approved, AWSLC_APPROVED);
  }
  ASSERT_TRUE(check_test(kPlaintext, output, sizeof(kPlaintext),
                         "AES-ECB Decryption KAT for 256 bit key"));
}

TEST(ServiceIndicatorTest, AESCBC) {
  int approved = AWSLC_NOT_APPROVED;
  AES_KEY aes_key;
  uint8_t aes_iv[16];
  uint8_t output[256];
  // AES-CBC Encryption KAT for 128 bit key.
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  ASSERT_TRUE(AES_set_encrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_cbc_encrypt(kPlaintext, output,
                              sizeof(kPlaintext), &aes_key, aes_iv, AES_ENCRYPT));
  ASSERT_TRUE(check_test(kAESCBCCiphertext, output, sizeof(kAESCBCCiphertext),
                         "AES-CBC Encryption KAT for 128 bit key"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-CBC Decryption KAT for 128 bit key.
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  ASSERT_TRUE(AES_set_decrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_cbc_encrypt(kAESCBCCiphertext, output,
                        sizeof(kAESCBCCiphertext), &aes_key, aes_iv, AES_DECRYPT));
  ASSERT_TRUE(check_test(kPlaintext, output, sizeof(kPlaintext),
                         "AES-CBC Decryption KAT for 128 bit key"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-CBC Encryption KAT for 192 bit key.
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  ASSERT_TRUE(AES_set_encrypt_key(kAESKey_192, 8 * sizeof(kAESKey_192), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_cbc_encrypt(kPlaintext, output,
                              sizeof(kPlaintext), &aes_key, aes_iv, AES_ENCRYPT));
  ASSERT_TRUE(check_test(kAESCBCCiphertext_192, output, sizeof(kAESCBCCiphertext_192),
                         "AES-CBC Encryption KAT for 192 bit key"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-CBC Decryption KAT for 192 bit key.
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  ASSERT_TRUE(AES_set_decrypt_key(kAESKey_192, 8 * sizeof(kAESKey_192), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_cbc_encrypt(kAESCBCCiphertext_192, output,
                        sizeof(kAESCBCCiphertext_192), &aes_key, aes_iv, AES_DECRYPT));
  ASSERT_TRUE(check_test(kPlaintext, output, sizeof(kPlaintext),
                         "AES-CBC Decryption KAT for 192 bit key"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-CBC Encryption KAT for 256 bit key.
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  ASSERT_TRUE(AES_set_encrypt_key(kAESKey_256, 8 * sizeof(kAESKey_256), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_cbc_encrypt(kPlaintext, output,
                              sizeof(kPlaintext), &aes_key, aes_iv, AES_ENCRYPT));
  ASSERT_TRUE(check_test(kAESCBCCiphertext_256, output, sizeof(kAESCBCCiphertext_256),
                         "AES-CBC Encryption KAT for 256 bit key"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-CBC Decryption KAT for 256 bit key.
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  ASSERT_TRUE(AES_set_decrypt_key(kAESKey_256, 8 * sizeof(kAESKey_256), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_cbc_encrypt(kAESCBCCiphertext_256, output,
                        sizeof(kAESCBCCiphertext_256), &aes_key, aes_iv, AES_DECRYPT));
  ASSERT_TRUE(check_test(kPlaintext, output, sizeof(kPlaintext),
                         "AES-CBC Decryption KAT for 256 bit key"));
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
  ASSERT_TRUE(AES_set_encrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_ctr128_encrypt(kPlaintext, output,
                             sizeof(kPlaintext), &aes_key, aes_iv, ecount_buf, &num));
  ASSERT_TRUE(check_test(kAESCTRCiphertext, output, sizeof(kAESCTRCiphertext),
                         "AES-CTR Encryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-CTR Decryption KAT
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_ctr128_encrypt(kAESCTRCiphertext, output,
                         sizeof(kAESCTRCiphertext), &aes_key, aes_iv, ecount_buf, &num));
  ASSERT_TRUE(check_test(kPlaintext, output, sizeof(kPlaintext),
                         "AES-CTR Decryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-CTR Encryption KAT for 192 bit key.
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  ASSERT_TRUE(AES_set_encrypt_key(kAESKey_192, 8 * sizeof(kAESKey_192), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_ctr128_encrypt(kPlaintext, output,
                             sizeof(kPlaintext), &aes_key, aes_iv, ecount_buf, &num));
  ASSERT_TRUE(check_test(kAESCTRCiphertext_192, output, sizeof(kAESCTRCiphertext_192),
                         "AES-CTR Encryption KAT for 192 bit key"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-CTR Decryption KAT for 192 bit key.
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_ctr128_encrypt(kAESCTRCiphertext_192, output,
                         sizeof(kAESCTRCiphertext_192), &aes_key, aes_iv, ecount_buf, &num));
  ASSERT_TRUE(check_test(kPlaintext, output, sizeof(kPlaintext),
                         "AES-CTR Decryption KAT for 192 bit key"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-CTR Encryption KAT for 256 bit key.
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  ASSERT_TRUE(AES_set_encrypt_key(kAESKey_256, 8 * sizeof(kAESKey_256), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_ctr128_encrypt(kPlaintext, output,
                             sizeof(kPlaintext), &aes_key, aes_iv, ecount_buf, &num));
  ASSERT_TRUE(check_test(kAESCTRCiphertext_256, output, sizeof(kAESCTRCiphertext_256),
                         "AES-CTR Encryption KAT for 256 bit key"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-CTR Decryption KAT for 256 bit key.
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_ctr128_encrypt(kAESCTRCiphertext_256, output,
                         sizeof(kAESCTRCiphertext_256), &aes_key, aes_iv, ecount_buf, &num));
  ASSERT_TRUE(check_test(kPlaintext, output, sizeof(kPlaintext),
                         "AES-CTR Decryption KAT for 256 bit key"));
  ASSERT_EQ(approved, AWSLC_APPROVED);
}

TEST(ServiceIndicatorTest, AESOFB) {
  int approved = AWSLC_NOT_APPROVED;

  AES_KEY aes_key;
  uint8_t aes_iv[sizeof(kAESIV)];
  uint8_t output[256];
  int num = 0;

  // AES-OFB Encryption KAT
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  ASSERT_TRUE(AES_set_encrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_ofb128_encrypt(kPlaintext, output,
                                   sizeof(kPlaintext), &aes_key, aes_iv, &num));
  ASSERT_TRUE(check_test(kAESOFBCiphertext, output, sizeof(kAESOFBCiphertext),
                         "AES-OFB Encryption KAT"));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);

  // AES-OFB Decryption KAT
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_ofb128_encrypt(kAESOFBCiphertext, output,
                               sizeof(kAESOFBCiphertext), &aes_key, aes_iv, &num));
  ASSERT_TRUE(check_test(kPlaintext, output, sizeof(kPlaintext),
                         "AES-OFB Decryption KAT"));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
}

TEST(ServiceIndicatorTest, AESCFB) {
  int approved = AWSLC_NOT_APPROVED;

  AES_KEY aes_key;
  uint8_t aes_iv[sizeof(kAESIV)];
  uint8_t output[256];
  int num = 0;

  // AES-CFB Encryption KAT
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  ASSERT_TRUE(AES_set_encrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_cfb128_encrypt(kPlaintext, output,
                                   sizeof(kPlaintext), &aes_key, aes_iv, &num, AES_ENCRYPT));
  ASSERT_TRUE(check_test(kAESCFBCiphertext, output, sizeof(kAESCFBCiphertext),
                         "AES-CFB Encryption KAT"));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);

  // AES-CFB Decryption KAT
  memcpy(aes_iv, kAESIV, sizeof(kAESIV));
  CALL_SERVICE_AND_CHECK_APPROVED(approved, AES_cfb128_encrypt(kAESCFBCiphertext, output,
                                 sizeof(kAESCFBCiphertext), &aes_key, aes_iv, &num, AES_DECRYPT));
  ASSERT_TRUE(check_test(kPlaintext, output, sizeof(kPlaintext),
                         "AES-CFB Decryption KAT"));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
}

TEST(ServiceIndicatorTest, AESKW) {
  int approved = AWSLC_NOT_APPROVED;

  AES_KEY aes_key;
  uint8_t output[256];
  size_t outlen;

  // AES-KW Encryption KAT
  ASSERT_TRUE(AES_set_encrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, outlen = AES_wrap_key(&aes_key, nullptr,
                                    output, kPlaintext, sizeof(kPlaintext)));
  ASSERT_EQ(outlen, sizeof(kAESKWCiphertext));
  ASSERT_TRUE(check_test(kAESKWCiphertext, output, outlen, "AES-KW Encryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-KW Decryption KAT
  ASSERT_TRUE(AES_set_decrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved,outlen = AES_unwrap_key(&aes_key, nullptr,
                                    output, kAESKWCiphertext, sizeof(kAESKWCiphertext)));
  ASSERT_EQ(outlen, sizeof(kPlaintext));
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
  ASSERT_TRUE(AES_set_encrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(AES_wrap_key_padded(&aes_key,
              output, &outlen, sizeof(kPlaintext) + 15, kPlaintext, sizeof(kPlaintext))));
  ASSERT_TRUE(check_test(kAESKWPCiphertext, output, outlen, "AES-KWP Encryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);

  // AES-KWP Decryption KAT
  ASSERT_TRUE(AES_set_decrypt_key(kAESKey, 8 * sizeof(kAESKey), &aes_key) == 0);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(AES_unwrap_key_padded(&aes_key,
             output, &outlen, sizeof(kAESKWPCiphertext), kAESKWPCiphertext, sizeof(kAESKWPCiphertext))));
  ASSERT_TRUE(check_test(kPlaintext, output, outlen, "AES-KWP Decryption KAT"));
  ASSERT_EQ(approved, AWSLC_APPROVED);
}

TEST(ServiceIndicatorTest, FFDH) {
  int approved = AWSLC_NOT_APPROVED;

  // |DH_compute_key_padded| should be a non-approved service.
  bssl::UniquePtr<BIGNUM> ffdhe2048_value(BN_new());
  bssl::UniquePtr<DH> dh(self_test_dh());
  ffdhe2048_value.get()->d = (BN_ULONG *)kFFDHE2048PublicValueData;
  ffdhe2048_value.get()->width = OPENSSL_ARRAY_SIZE(kFFDHE2048PublicValueData);
  ffdhe2048_value.get()->dmax = OPENSSL_ARRAY_SIZE(kFFDHE2048PublicValueData);
  ffdhe2048_value.get()->neg = 0;
  ffdhe2048_value.get()->flags |= BN_FLG_STATIC_DATA;

  uint8_t dh_out[sizeof(kDHOutput)];
  ASSERT_EQ(DH_size(dh.get()), static_cast<int>(sizeof(dh_out)));
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
    ASSERT_EQ(DH_compute_key_padded(dh_out, ffdhe2048_value.get(), dh.get()),
                                        static_cast<int>(sizeof(dh_out))));
  ASSERT_TRUE(check_test(kDHOutput, dh_out, sizeof(dh_out), "FFC DH"));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
}

TEST(ServiceIndicatorTest, DRBG) {
  int approved = AWSLC_NOT_APPROVED;
  CTR_DRBG_STATE drbg;
  uint8_t output[256];

  // Test running the DRBG interfaces and check |CTR_DRBG_generate| for approval
  // at the end since it indicates a service is being done. |CTR_DRBG_init| and
  // |CTR_DRBG_reseed| should not be approved, because the functions do not
  // indicate that a service has been fully completed yet.
  // These DRBG functions are not directly accessible for external consumers
  // however.
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(CTR_DRBG_init(&drbg,
                        kDRBGEntropy, kDRBGPersonalization, sizeof(kDRBGPersonalization))));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(CTR_DRBG_generate(&drbg,
                        output, sizeof(kDRBGOutput), kDRBGAD, sizeof(kDRBGAD))));
  ASSERT_EQ(approved, AWSLC_APPROVED);
  ASSERT_TRUE(check_test(kDRBGOutput, output, sizeof(kDRBGOutput),"DBRG Generate KAT"));

  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(CTR_DRBG_reseed(&drbg,
                        kDRBGEntropy2, kDRBGAD, sizeof(kDRBGAD))));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(CTR_DRBG_generate(&drbg,
                        output, sizeof(kDRBGReseedOutput), kDRBGAD, sizeof(kDRBGAD))));
  ASSERT_EQ(approved, AWSLC_APPROVED);
  ASSERT_TRUE(check_test(kDRBGReseedOutput, output, sizeof(kDRBGReseedOutput),"DRBG Reseed KAT"));

  // Test approval of |RAND_bytes|, which is the only way for the consumer to
  // indirectly interact with the DRBG functions.
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(RAND_bytes(output, sizeof(output))));
  ASSERT_EQ(approved, AWSLC_APPROVED);
  CTR_DRBG_clear(&drbg);
}

// Verifies that the awslc_version_string is as expected.
// Since this is running in FIPS mode it should end in FIPS
// Update this when the AWS-LC version number is modified
TEST(ServiceIndicatorTest, AWSLCVersionString) {
  ASSERT_STREQ(awslc_version_string(), "AWS-LC FIPS 1.0.1");
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

  // Approval check should also return true when not in FIPS mode.
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

// Verifies that the awslc_version_string is as expected.
// Since this is not running in FIPS mode it shouldn't end in FIPS
// Update this when the AWS-LC version number is modified
TEST(ServiceIndicatorTest, AWSLCVersionString) {
  ASSERT_STREQ(awslc_version_string(), "AWS-LC 1.0.1");
}
#endif // AWSLC_FIPS
