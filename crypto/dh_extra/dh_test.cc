/* Copyright (C) 1995-1998 Eric Young (eay@cryptsoft.com)
 * All rights reserved.
 *
 * This package is an SSL implementation written
 * by Eric Young (eay@cryptsoft.com).
 * The implementation was written so as to conform with Netscapes SSL.
 *
 * This library is free for commercial and non-commercial use as long as
 * the following conditions are aheared to.  The following conditions
 * apply to all code found in this distribution, be it the RC4, RSA,
 * lhash, DES, etc., code; not just the SSL code.  The SSL documentation
 * included with this distribution is covered by the same copyright terms
 * except that the holder is Tim Hudson (tjh@cryptsoft.com).
 *
 * Copyright remains Eric Young's, and as such any Copyright notices in
 * the code are not to be removed.
 * If this package is used in a product, Eric Young should be given attribution
 * as the author of the parts of the library used.
 * This can be in the form of a textual message at program startup or
 * in documentation (online or textual) provided with the package.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *    "This product includes cryptographic software written by
 *     Eric Young (eay@cryptsoft.com)"
 *    The word 'cryptographic' can be left out if the rouines from the library
 *    being used are not cryptographic related :-).
 * 4. If you include any Windows specific code (or a derivative thereof) from
 *    the apps directory (application code) you must include an acknowledgement:
 *    "This product includes software written by Tim Hudson (tjh@cryptsoft.com)"
 *
 * THIS SOFTWARE IS PROVIDED BY ERIC YOUNG ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * The licence and distribution terms for any publically available version or
 * derivative of this code cannot be changed.  i.e. this code cannot simply be
 * copied and put under another distribution licence
 * [including the GNU Public Licence.] */

#include <openssl/dh.h>

#include <stdio.h>
#include <string.h>

#include <vector>

#include <gtest/gtest.h>

#include <openssl/bn.h>
#include <openssl/bytestring.h>
#include <openssl/crypto.h>
#include <openssl/dh.h>
#include <openssl/err.h>
#include <openssl/mem.h>
#include <openssl/nid.h>

#include "../fipsmodule/dh/internal.h"
#include "../internal.h"
#include "../test/test_util.h"


TEST(DHTest, Basic) {
  bssl::UniquePtr<DH> a(DH_new());
  ASSERT_TRUE(a);
  ASSERT_TRUE(DH_generate_parameters_ex(a.get(), 64, DH_GENERATOR_5, nullptr));

  int check_result;
  ASSERT_TRUE(DH_check(a.get(), &check_result));
  EXPECT_FALSE(check_result & DH_CHECK_P_NOT_PRIME);
  EXPECT_FALSE(check_result & DH_CHECK_P_NOT_SAFE_PRIME);
  EXPECT_FALSE(check_result & DH_CHECK_UNABLE_TO_CHECK_GENERATOR);
  EXPECT_FALSE(check_result & DH_CHECK_NOT_SUITABLE_GENERATOR);

  bssl::UniquePtr<DH> b(DHparams_dup(a.get()));
  ASSERT_TRUE(b);

  ASSERT_TRUE(DH_generate_key(a.get()));
  ASSERT_TRUE(DH_generate_key(b.get()));

  std::vector<uint8_t> key1(DH_size(a.get()));
  int ret = DH_compute_key(key1.data(), DH_get0_pub_key(b.get()), a.get());
  ASSERT_GE(ret, 0);
  key1.resize(ret);

  std::vector<uint8_t> key2(DH_size(b.get()));
  ret = DH_compute_key(key2.data(), DH_get0_pub_key(a.get()), b.get());
  ASSERT_GE(ret, 0);
  key2.resize(ret);

  EXPECT_EQ(Bytes(key1), Bytes(key2));

  // |DH_compute_key|, unlike |DH_compute_key_padded|, removes leading zeros
  // from the output, so the key will not have a fixed length. This test uses a
  // small, 64-bit prime, so check for at least 32 bits of output after removing
  // leading zeros.
  EXPECT_GE(key1.size(), 4u);
}

// The following parameters are taken from RFC 5114, section 2.2. This is not a
// safe prime. Do not use these parameters.
static const uint8_t kRFC5114_2048_224P[] = {
    0xad, 0x10, 0x7e, 0x1e, 0x91, 0x23, 0xa9, 0xd0, 0xd6, 0x60, 0xfa, 0xa7,
    0x95, 0x59, 0xc5, 0x1f, 0xa2, 0x0d, 0x64, 0xe5, 0x68, 0x3b, 0x9f, 0xd1,
    0xb5, 0x4b, 0x15, 0x97, 0xb6, 0x1d, 0x0a, 0x75, 0xe6, 0xfa, 0x14, 0x1d,
    0xf9, 0x5a, 0x56, 0xdb, 0xaf, 0x9a, 0x3c, 0x40, 0x7b, 0xa1, 0xdf, 0x15,
    0xeb, 0x3d, 0x68, 0x8a, 0x30, 0x9c, 0x18, 0x0e, 0x1d, 0xe6, 0xb8, 0x5a,
    0x12, 0x74, 0xa0, 0xa6, 0x6d, 0x3f, 0x81, 0x52, 0xad, 0x6a, 0xc2, 0x12,
    0x90, 0x37, 0xc9, 0xed, 0xef, 0xda, 0x4d, 0xf8, 0xd9, 0x1e, 0x8f, 0xef,
    0x55, 0xb7, 0x39, 0x4b, 0x7a, 0xd5, 0xb7, 0xd0, 0xb6, 0xc1, 0x22, 0x07,
    0xc9, 0xf9, 0x8d, 0x11, 0xed, 0x34, 0xdb, 0xf6, 0xc6, 0xba, 0x0b, 0x2c,
    0x8b, 0xbc, 0x27, 0xbe, 0x6a, 0x00, 0xe0, 0xa0, 0xb9, 0xc4, 0x97, 0x08,
    0xb3, 0xbf, 0x8a, 0x31, 0x70, 0x91, 0x88, 0x36, 0x81, 0x28, 0x61, 0x30,
    0xbc, 0x89, 0x85, 0xdb, 0x16, 0x02, 0xe7, 0x14, 0x41, 0x5d, 0x93, 0x30,
    0x27, 0x82, 0x73, 0xc7, 0xde, 0x31, 0xef, 0xdc, 0x73, 0x10, 0xf7, 0x12,
    0x1f, 0xd5, 0xa0, 0x74, 0x15, 0x98, 0x7d, 0x9a, 0xdc, 0x0a, 0x48, 0x6d,
    0xcd, 0xf9, 0x3a, 0xcc, 0x44, 0x32, 0x83, 0x87, 0x31, 0x5d, 0x75, 0xe1,
    0x98, 0xc6, 0x41, 0xa4, 0x80, 0xcd, 0x86, 0xa1, 0xb9, 0xe5, 0x87, 0xe8,
    0xbe, 0x60, 0xe6, 0x9c, 0xc9, 0x28, 0xb2, 0xb9, 0xc5, 0x21, 0x72, 0xe4,
    0x13, 0x04, 0x2e, 0x9b, 0x23, 0xf1, 0x0b, 0x0e, 0x16, 0xe7, 0x97, 0x63,
    0xc9, 0xb5, 0x3d, 0xcf, 0x4b, 0xa8, 0x0a, 0x29, 0xe3, 0xfb, 0x73, 0xc1,
    0x6b, 0x8e, 0x75, 0xb9, 0x7e, 0xf3, 0x63, 0xe2, 0xff, 0xa3, 0x1f, 0x71,
    0xcf, 0x9d, 0xe5, 0x38, 0x4e, 0x71, 0xb8, 0x1c, 0x0a, 0xc4, 0xdf, 0xfe,
    0x0c, 0x10, 0xe6, 0x4f,
};
static const uint8_t kRFC5114_2048_224G[] = {
    0xac, 0x40, 0x32, 0xef, 0x4f, 0x2d, 0x9a, 0xe3, 0x9d, 0xf3, 0x0b, 0x5c,
    0x8f, 0xfd, 0xac, 0x50, 0x6c, 0xde, 0xbe, 0x7b, 0x89, 0x99, 0x8c, 0xaf,
    0x74, 0x86, 0x6a, 0x08, 0xcf, 0xe4, 0xff, 0xe3, 0xa6, 0x82, 0x4a, 0x4e,
    0x10, 0xb9, 0xa6, 0xf0, 0xdd, 0x92, 0x1f, 0x01, 0xa7, 0x0c, 0x4a, 0xfa,
    0xab, 0x73, 0x9d, 0x77, 0x00, 0xc2, 0x9f, 0x52, 0xc5, 0x7d, 0xb1, 0x7c,
    0x62, 0x0a, 0x86, 0x52, 0xbe, 0x5e, 0x90, 0x01, 0xa8, 0xd6, 0x6a, 0xd7,
    0xc1, 0x76, 0x69, 0x10, 0x19, 0x99, 0x02, 0x4a, 0xf4, 0xd0, 0x27, 0x27,
    0x5a, 0xc1, 0x34, 0x8b, 0xb8, 0xa7, 0x62, 0xd0, 0x52, 0x1b, 0xc9, 0x8a,
    0xe2, 0x47, 0x15, 0x04, 0x22, 0xea, 0x1e, 0xd4, 0x09, 0x93, 0x9d, 0x54,
    0xda, 0x74, 0x60, 0xcd, 0xb5, 0xf6, 0xc6, 0xb2, 0x50, 0x71, 0x7c, 0xbe,
    0xf1, 0x80, 0xeb, 0x34, 0x11, 0x8e, 0x98, 0xd1, 0x19, 0x52, 0x9a, 0x45,
    0xd6, 0xf8, 0x34, 0x56, 0x6e, 0x30, 0x25, 0xe3, 0x16, 0xa3, 0x30, 0xef,
    0xbb, 0x77, 0xa8, 0x6f, 0x0c, 0x1a, 0xb1, 0x5b, 0x05, 0x1a, 0xe3, 0xd4,
    0x28, 0xc8, 0xf8, 0xac, 0xb7, 0x0a, 0x81, 0x37, 0x15, 0x0b, 0x8e, 0xeb,
    0x10, 0xe1, 0x83, 0xed, 0xd1, 0x99, 0x63, 0xdd, 0xd9, 0xe2, 0x63, 0xe4,
    0x77, 0x05, 0x89, 0xef, 0x6a, 0xa2, 0x1e, 0x7f, 0x5f, 0x2f, 0xf3, 0x81,
    0xb5, 0x39, 0xcc, 0xe3, 0x40, 0x9d, 0x13, 0xcd, 0x56, 0x6a, 0xfb, 0xb4,
    0x8d, 0x6c, 0x01, 0x91, 0x81, 0xe1, 0xbc, 0xfe, 0x94, 0xb3, 0x02, 0x69,
    0xed, 0xfe, 0x72, 0xfe, 0x9b, 0x6a, 0xa4, 0xbd, 0x7b, 0x5a, 0x0f, 0x1c,
    0x71, 0xcf, 0xff, 0x4c, 0x19, 0xc4, 0x18, 0xe1, 0xf6, 0xec, 0x01, 0x79,
    0x81, 0xbc, 0x08, 0x7f, 0x2a, 0x70, 0x65, 0xb3, 0x84, 0xb8, 0x90, 0xd3,
    0x19, 0x1f, 0x2b, 0xfa,
};
static const uint8_t kRFC5114_2048_224Q[] = {
    0x80, 0x1c, 0x0d, 0x34, 0xc5, 0x8d, 0x93, 0xfe, 0x99, 0x71,
    0x77, 0x10, 0x1f, 0x80, 0x53, 0x5a, 0x47, 0x38, 0xce, 0xbc,
    0xbf, 0x38, 0x9a, 0x99, 0xb3, 0x63, 0x71, 0xeb,
};

// kRFC5114_2048_224BadY is a bad y-coordinate for RFC 5114's 2048-bit MODP
// Group with 224-bit Prime Order Subgroup (section 2.2).
static const uint8_t kRFC5114_2048_224BadY[] = {
    0x45, 0x32, 0x5f, 0x51, 0x07, 0xe5, 0xdf, 0x1c, 0xd6, 0x02, 0x82, 0xb3,
    0x32, 0x8f, 0xa4, 0x0f, 0x87, 0xb8, 0x41, 0xfe, 0xb9, 0x35, 0xde, 0xad,
    0xc6, 0x26, 0x85, 0xb4, 0xff, 0x94, 0x8c, 0x12, 0x4c, 0xbf, 0x5b, 0x20,
    0xc4, 0x46, 0xa3, 0x26, 0xeb, 0xa4, 0x25, 0xb7, 0x68, 0x8e, 0xcc, 0x67,
    0xba, 0xea, 0x58, 0xd0, 0xf2, 0xe9, 0xd2, 0x24, 0x72, 0x60, 0xda, 0x88,
    0x18, 0x9c, 0xe0, 0x31, 0x6a, 0xad, 0x50, 0x6d, 0x94, 0x35, 0x8b, 0x83,
    0x4a, 0x6e, 0xfa, 0x48, 0x73, 0x0f, 0x83, 0x87, 0xff, 0x6b, 0x66, 0x1f,
    0xa8, 0x82, 0xc6, 0x01, 0xe5, 0x80, 0xb5, 0xb0, 0x52, 0xd0, 0xe9, 0xd8,
    0x72, 0xf9, 0x7d, 0x5b, 0x8b, 0xa5, 0x4c, 0xa5, 0x25, 0x95, 0x74, 0xe2,
    0x7a, 0x61, 0x4e, 0xa7, 0x8f, 0x12, 0xe2, 0xd2, 0x9d, 0x8c, 0x02, 0x70,
    0x34, 0x44, 0x32, 0xc7, 0xb2, 0xf3, 0xb9, 0xfe, 0x17, 0x2b, 0xd6, 0x1f,
    0x8b, 0x7e, 0x4a, 0xfa, 0xa3, 0xb5, 0x3e, 0x7a, 0x81, 0x9a, 0x33, 0x66,
    0x62, 0xa4, 0x50, 0x18, 0x3e, 0xa2, 0x5f, 0x00, 0x07, 0xd8, 0x9b, 0x22,
    0xe4, 0xec, 0x84, 0xd5, 0xeb, 0x5a, 0xf3, 0x2a, 0x31, 0x23, 0xd8, 0x44,
    0x22, 0x2a, 0x8b, 0x37, 0x44, 0xcc, 0xc6, 0x87, 0x4b, 0xbe, 0x50, 0x9d,
    0x4a, 0xc4, 0x8e, 0x45, 0xcf, 0x72, 0x4d, 0xc0, 0x89, 0xb3, 0x72, 0xed,
    0x33, 0x2c, 0xbc, 0x7f, 0x16, 0x39, 0x3b, 0xeb, 0xd2, 0xdd, 0xa8, 0x01,
    0x73, 0x84, 0x62, 0xb9, 0x29, 0xd2, 0xc9, 0x51, 0x32, 0x9e, 0x7a, 0x6a,
    0xcf, 0xc1, 0x0a, 0xdb, 0x0e, 0xe0, 0x62, 0x77, 0x6f, 0x59, 0x62, 0x72,
    0x5a, 0x69, 0xa6, 0x5b, 0x70, 0xca, 0x65, 0xc4, 0x95, 0x6f, 0x9a, 0xc2,
    0xdf, 0x72, 0x6d, 0xb1, 0x1e, 0x54, 0x7b, 0x51, 0xb4, 0xef, 0x7f, 0x89,
    0x93, 0x74, 0x89, 0x59,
};

TEST(DHTest, BadY) {
  bssl::UniquePtr<DH> dh(DH_new());
  ASSERT_TRUE(dh);
  dh->p = BN_bin2bn(kRFC5114_2048_224P, sizeof(kRFC5114_2048_224P), nullptr);
  dh->g = BN_bin2bn(kRFC5114_2048_224G, sizeof(kRFC5114_2048_224G), nullptr);
  dh->q = BN_bin2bn(kRFC5114_2048_224Q, sizeof(kRFC5114_2048_224Q), nullptr);
  ASSERT_TRUE(dh->p);
  ASSERT_TRUE(dh->g);
  ASSERT_TRUE(dh->q);

  bssl::UniquePtr<BIGNUM> pub_key(
      BN_bin2bn(kRFC5114_2048_224BadY, sizeof(kRFC5114_2048_224BadY), nullptr));
  ASSERT_TRUE(pub_key);
  ASSERT_TRUE(DH_generate_key(dh.get()));

  int flags;
  ASSERT_TRUE(DH_check_pub_key(dh.get(), pub_key.get(), &flags));
  EXPECT_TRUE(flags & DH_CHECK_PUBKEY_INVALID)
      << "DH_check_pub_key did not reject the key";

  std::vector<uint8_t> result(DH_size(dh.get()));
  EXPECT_LT(DH_compute_key(result.data(), pub_key.get(), dh.get()), 0)
      << "DH_compute_key unexpectedly succeeded";
  ERR_clear_error();
}

static bool BIGNUMEqualsHex(const BIGNUM *bn, const char *hex) {
  BIGNUM *hex_bn = NULL;
  if (!BN_hex2bn(&hex_bn, hex)) {
    return false;
  }
  bssl::UniquePtr<BIGNUM> free_hex_bn(hex_bn);
  return BN_cmp(bn, hex_bn) == 0;
}

TEST(DHTest, ASN1) {
  // kParams are a set of Diffie-Hellman parameters generated with
  // openssl dhparam 256
  static const uint8_t kParams[] = {
      0x30, 0x26, 0x02, 0x21, 0x00, 0xd7, 0x20, 0x34, 0xa3, 0x27,
      0x4f, 0xdf, 0xbf, 0x04, 0xfd, 0x24, 0x68, 0x25, 0xb6, 0x56,
      0xd8, 0xab, 0x2a, 0x41, 0x2d, 0x74, 0x0a, 0x52, 0x08, 0x7c,
      0x40, 0x71, 0x4e, 0xd2, 0x57, 0x93, 0x13, 0x02, 0x01, 0x02,
  };

  CBS cbs;
  CBS_init(&cbs, kParams, sizeof(kParams));
  bssl::UniquePtr<DH> dh(DH_parse_parameters(&cbs));
  ASSERT_TRUE(dh);
  EXPECT_EQ(CBS_len(&cbs), 0u);
  EXPECT_TRUE(BIGNUMEqualsHex(
      DH_get0_p(dh.get()),
      "d72034a3274fdfbf04fd246825b656d8ab2a412d740a52087c40714ed2579313"));
  EXPECT_TRUE(BIGNUMEqualsHex(DH_get0_g(dh.get()), "2"));
  EXPECT_EQ(dh->priv_length, 0u);

  bssl::ScopedCBB cbb;
  uint8_t *der;
  size_t der_len;
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(DH_marshal_parameters(cbb.get(), dh.get()));
  ASSERT_TRUE(CBB_finish(cbb.get(), &der, &der_len));
  bssl::UniquePtr<uint8_t> free_der(der);
  EXPECT_EQ(Bytes(kParams), Bytes(der, der_len));

  // kParamsDSA are a set of Diffie-Hellman parameters generated with
  // openssl dhparam 256 -dsaparam
  static const uint8_t kParamsDSA[] = {
      0x30, 0x81, 0x89, 0x02, 0x41, 0x00, 0x93, 0xf3, 0xc1, 0x18, 0x01, 0xe6,
      0x62, 0xb6, 0xd1, 0x46, 0x9a, 0x2c, 0x72, 0xea, 0x31, 0xd9, 0x18, 0x10,
      0x30, 0x28, 0x63, 0xe2, 0x34, 0x7d, 0x80, 0xca, 0xee, 0x82, 0x2b, 0x19,
      0x3c, 0x19, 0xbb, 0x42, 0x83, 0x02, 0x70, 0xdd, 0xdb, 0x8c, 0x03, 0xab,
      0xe9, 0x9c, 0xc4, 0x00, 0x4d, 0x70, 0x5f, 0x52, 0x03, 0x31, 0x2c, 0xa4,
      0x67, 0x34, 0x51, 0x95, 0x2a, 0xac, 0x11, 0xe2, 0x6a, 0x55, 0x02, 0x40,
      0x44, 0xc8, 0x10, 0x53, 0x44, 0x32, 0x31, 0x63, 0xd8, 0xd1, 0x8c, 0x75,
      0xc8, 0x98, 0x53, 0x3b, 0x5b, 0x4a, 0x2a, 0x0a, 0x09, 0xe7, 0xd0, 0x3c,
      0x53, 0x72, 0xa8, 0x6b, 0x70, 0x41, 0x9c, 0x26, 0x71, 0x44, 0xfc, 0x7f,
      0x08, 0x75, 0xe1, 0x02, 0xab, 0x74, 0x41, 0xe8, 0x2a, 0x3d, 0x3c, 0x26,
      0x33, 0x09, 0xe4, 0x8b, 0xb4, 0x41, 0xec, 0xa6, 0xa8, 0xba, 0x1a, 0x07,
      0x8a, 0x77, 0xf5, 0x5f, 0x02, 0x02, 0x00, 0xa0,
  };

  CBS_init(&cbs, kParamsDSA, sizeof(kParamsDSA));
  dh.reset(DH_parse_parameters(&cbs));
  ASSERT_TRUE(dh);
  EXPECT_EQ(CBS_len(&cbs), 0u);
  EXPECT_TRUE(
      BIGNUMEqualsHex(DH_get0_p(dh.get()),
                      "93f3c11801e662b6d1469a2c72ea31d91810302863e2347d80caee8"
                      "22b193c19bb42830270dddb8c03abe99cc4004d705f5203312ca467"
                      "3451952aac11e26a55"));
  EXPECT_TRUE(
      BIGNUMEqualsHex(DH_get0_g(dh.get()),
                      "44c8105344323163d8d18c75c898533b5b4a2a0a09e7d03c5372a86"
                      "b70419c267144fc7f0875e102ab7441e82a3d3c263309e48bb441ec"
                      "a6a8ba1a078a77f55f"));
  EXPECT_EQ(dh->priv_length, 160u);

  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(DH_marshal_parameters(cbb.get(), dh.get()));
  ASSERT_TRUE(CBB_finish(cbb.get(), &der, &der_len));
  bssl::UniquePtr<uint8_t> free_der2(der);
  EXPECT_EQ(Bytes(kParamsDSA), Bytes(der, der_len));
}

static void check_bn_matches_bytes(std::vector<uint8_t> bytes, const BIGNUM*bn) {
  uint8_t buffer[4096];
  ASSERT_EQ(BN_bn2bin(bn, buffer), bytes.size());
  EXPECT_EQ(Bytes(buffer, bytes.size()), Bytes(bytes));
}

static std::vector<uint8_t> rfc_string_to_bytes(const char *str) {
  std::string string(str);
  string.erase(std::remove_if(string.begin(),string.end(), ::isspace),string.end());
  return HexToBytes(string.c_str());

}

TEST(DHTest, RFC3526) {
  bssl::UniquePtr<BIGNUM> bn(BN_get_rfc3526_prime_1536(nullptr));
  ASSERT_TRUE(bn);

  // Taken from section 2
  std::vector<uint8_t> kPrime1536 = rfc_string_to_bytes(
    "FFFFFFFF FFFFFFFF C90FDAA2 2168C234 C4C6628B 80DC1CD1"
    "29024E08 8A67CC74 020BBEA6 3B139B22 514A0879 8E3404DD"
    "EF9519B3 CD3A431B 302B0A6D F25F1437 4FE1356D 6D51C245"
    "E485B576 625E7EC6 F44C42E9 A637ED6B 0BFF5CB6 F406B7ED"
    "EE386BFB 5A899FA5 AE9F2411 7C4B1FE6 49286651 ECE45B3D"
    "C2007CB8 A163BF05 98DA4836 1C55D39A 69163FA8 FD24CF5F"
    "83655D23 DCA3AD96 1C62F356 208552BB 9ED52907 7096966D"
    "670C354E 4ABC9804 F1746C08 CA237327 FFFFFFFF FFFFFFFF");
  check_bn_matches_bytes(kPrime1536, bn.get());
}


TEST(DHTest, RFC7919) {
  // Primes taken from Appendix 1 and 3 of RFC 7919
  struct testInput{
    int nid;
    std::vector<uint8_t> p;
    std::vector<uint8_t> q;
  };
  testInput testInputs[] = {
      {NID_ffdhe2048,
           rfc_string_to_bytes(
              "FFFFFFFF FFFFFFFF ADF85458 A2BB4A9A AFDC5620 273D3CF1"
              "D8B9C583 CE2D3695 A9E13641 146433FB CC939DCE 249B3EF9"
              "7D2FE363 630C75D8 F681B202 AEC4617A D3DF1ED5 D5FD6561"
              "2433F51F 5F066ED0 85636555 3DED1AF3 B557135E 7F57C935"
              "984F0C70 E0E68B77 E2A689DA F3EFE872 1DF158A1 36ADE735"
              "30ACCA4F 483A797A BC0AB182 B324FB61 D108A94B B2C8E3FB"
              "B96ADAB7 60D7F468 1D4F42A3 DE394DF4 AE56EDE7 6372BB19"
              "0B07A7C8 EE0A6D70 9E02FCE1 CDF7E2EC C03404CD 28342F61"
              "9172FE9C E98583FF 8E4F1232 EEF28183 C3FE3B1B 4C6FAD73"
              "3BB5FCBC 2EC22005 C58EF183 7D1683B2 C6F34A26 C1B2EFFA"
              "886B4238 61285C97 FFFFFFFF FFFFFFFF"),
           rfc_string_to_bytes(
              "7FFFFFFF FFFFFFFF D6FC2A2C 515DA54D 57EE2B10 139E9E78"
              "EC5CE2C1 E7169B4A D4F09B20 8A3219FD E649CEE7 124D9F7C"
              "BE97F1B1 B1863AEC 7B40D901 576230BD 69EF8F6A EAFEB2B0"
              "9219FA8F AF833768 42B1B2AA 9EF68D79 DAAB89AF 3FABE49A"
              "CC278638 707345BB F15344ED 79F7F439 0EF8AC50 9B56F39A"
              "98566527 A41D3CBD 5E0558C1 59927DB0 E88454A5 D96471FD"
              "DCB56D5B B06BFA34 0EA7A151 EF1CA6FA 572B76F3 B1B95D8C"
              "8583D3E4 770536B8 4F017E70 E6FBF176 601A0266 941A17B0"
              "C8B97F4E 74C2C1FF C7278919 777940C1 E1FF1D8D A637D6B9"
              "9DDAFE5E 17611002 E2C778C1 BE8B41D9 6379A513 60D977FD"
              "4435A11C 30942E4B FFFFFFFF FFFFFFFF")},
      {NID_ffdhe4096,
           rfc_string_to_bytes(
                "FFFFFFFF FFFFFFFF ADF85458 A2BB4A9A AFDC5620 273D3CF1"
                "D8B9C583 CE2D3695 A9E13641 146433FB CC939DCE 249B3EF9"
                "7D2FE363 630C75D8 F681B202 AEC4617A D3DF1ED5 D5FD6561"
                "2433F51F 5F066ED0 85636555 3DED1AF3 B557135E 7F57C935"
                "984F0C70 E0E68B77 E2A689DA F3EFE872 1DF158A1 36ADE735"
                "30ACCA4F 483A797A BC0AB182 B324FB61 D108A94B B2C8E3FB"
                "B96ADAB7 60D7F468 1D4F42A3 DE394DF4 AE56EDE7 6372BB19"
                "0B07A7C8 EE0A6D70 9E02FCE1 CDF7E2EC C03404CD 28342F61"
                "9172FE9C E98583FF 8E4F1232 EEF28183 C3FE3B1B 4C6FAD73"
                "3BB5FCBC 2EC22005 C58EF183 7D1683B2 C6F34A26 C1B2EFFA"
                "886B4238 611FCFDC DE355B3B 6519035B BC34F4DE F99C0238"
                "61B46FC9 D6E6C907 7AD91D26 91F7F7EE 598CB0FA C186D91C"
                "AEFE1309 85139270 B4130C93 BC437944 F4FD4452 E2D74DD3"
                "64F2E21E 71F54BFF 5CAE82AB 9C9DF69E E86D2BC5 22363A0D"
                "ABC52197 9B0DEADA 1DBF9A42 D5C4484E 0ABCD06B FA53DDEF"
                "3C1B20EE 3FD59D7C 25E41D2B 669E1EF1 6E6F52C3 164DF4FB"
                "7930E9E4 E58857B6 AC7D5F42 D69F6D18 7763CF1D 55034004"
                "87F55BA5 7E31CC7A 7135C886 EFB4318A ED6A1E01 2D9E6832"
                "A907600A 918130C4 6DC778F9 71AD0038 092999A3 33CB8B7A"
                "1A1DB93D 7140003C 2A4ECEA9 F98D0ACC 0A8291CD CEC97DCF"
                "8EC9B55A 7F88A46B 4DB5A851 F44182E1 C68A007E 5E655F6A"
                "FFFFFFFF FFFFFFFF"),
           rfc_string_to_bytes(
                "7FFFFFFF FFFFFFFF D6FC2A2C 515DA54D 57EE2B10 139E9E78"
                "EC5CE2C1 E7169B4A D4F09B20 8A3219FD E649CEE7 124D9F7C"
                "BE97F1B1 B1863AEC 7B40D901 576230BD 69EF8F6A EAFEB2B0"
                "9219FA8F AF833768 42B1B2AA 9EF68D79 DAAB89AF 3FABE49A"
                "CC278638 707345BB F15344ED 79F7F439 0EF8AC50 9B56F39A"
                "98566527 A41D3CBD 5E0558C1 59927DB0 E88454A5 D96471FD"
                "DCB56D5B B06BFA34 0EA7A151 EF1CA6FA 572B76F3 B1B95D8C"
                "8583D3E4 770536B8 4F017E70 E6FBF176 601A0266 941A17B0"
                "C8B97F4E 74C2C1FF C7278919 777940C1 E1FF1D8D A637D6B9"
                "9DDAFE5E 17611002 E2C778C1 BE8B41D9 6379A513 60D977FD"
                "4435A11C 308FE7EE 6F1AAD9D B28C81AD DE1A7A6F 7CCE011C"
                "30DA37E4 EB736483 BD6C8E93 48FBFBF7 2CC6587D 60C36C8E"
                "577F0984 C289C938 5A098649 DE21BCA2 7A7EA229 716BA6E9"
                "B279710F 38FAA5FF AE574155 CE4EFB4F 743695E2 911B1D06"
                "D5E290CB CD86F56D 0EDFCD21 6AE22427 055E6835 FD29EEF7"
                "9E0D9077 1FEACEBE 12F20E95 B34F0F78 B737A961 8B26FA7D"
                "BC9874F2 72C42BDB 563EAFA1 6B4FB68C 3BB1E78E AA81A002"
                "43FAADD2 BF18E63D 389AE443 77DA18C5 76B50F00 96CF3419"
                "5483B005 48C09862 36E3BC7C B8D6801C 0494CCD1 99E5C5BD"
                "0D0EDC9E B8A0001E 15276754 FCC68566 054148E6 E764BEE7"
                "C764DAAD 3FC45235 A6DAD428 FA20C170 E345003F 2F32AFB5"
                "7FFFFFFF FFFFFFFF")}
  };
  for (const testInput &test : testInputs ) {
    bssl::UniquePtr<DH> dh(DH_new_by_nid(test.nid));
    ASSERT_TRUE(dh);
    check_bn_matches_bytes(test.p, DH_get0_p(dh.get()));
    check_bn_matches_bytes(test.q, DH_get0_q(dh.get()));
  }
}

TEST(DHExpectedTestnputTest, CalculateSharedSecretMatches) {
  // KAT calculated with the following sage math code:
  // prime=int("0x[prime for 2048 or 4096]", 16) R=Integers(prime) g = R(2)
  // client_sk = int("0xABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890", 16) client_pk = g^client_sk
  // server_sk = int("0xAABBCCDDEEFF11223344556677889900AABBCCDDEEFF11223344556677889900", 16) shared_secret = client_pk^server_sk
  // print("client_pk", format(int(client_pk), '#x'))
  // print("server_sk", format(server_sk, '#x'))
  // print("expected_ss", format(int(shared_secret), '#x'))
  struct testInput {
    int nid;
    std::vector<uint8_t> client_pk;
    std::vector<uint8_t> server_sk;
    std::vector<uint8_t> expected_ss;
  };
  testInput testInputs[] = {
      {NID_ffdhe2048,
       HexToBytes(
          "50f2d9e890e290c60618a15fb314b71f9b24f4942db80ef29d1de007b5fc7a89"
          "2f80d15b4b22a131e505beebc98d27d96eaade29d293b035f8b38b64d8927b16"
          "ff3aebb887e14c56f889f5bf9fc248a2bf7e575fcc112c53f01048fa5127459c"
          "e06ca98cd961a3a3aa075688da64c4983ee44668fdef1dcabc7791e4906f9301"
          "eb0189b35c768c9c5b8e819f78c998a631ff9ded899080c4fb3cbd264689059e"
          "6d8adca7df629fde5c2c73aeef7c39b464ebe833689e6dd85e08dbfaad89bbf9"
          "140d15b5b2b31ec9b046a891fde9503234bf1c7818ec44ce00c103787e971b23"
          "b7214a93cdf98b4f1920ec1f55ddb4507b5e80301d068ab76ec3df34d440089a"),
       HexToBytes(
          "aabbccddeeff11223344556677889900aabbccddeeff11223344556677889900"),
       HexToBytes(
          "897396da313e171565c15595197c521862358a5071db94b50ac24952b5619c94"
          "3e4fffdb56dcfcfae886709038553b1ec7e4b6f165454ff09250662f4ea65cd9"
          "86b0040de370637e053495ba08cf649e6e53a5fcc58334496061f2cc8a375d32"
          "293cd2979283bedd08a2eb9a53a0f106fa29c6775b4d45cdf6b8516afb41ebfa"
          "3a487510d8f3c4d337a0af880271ebfa28b5551286cb3c3b2cb6a2cc35116816"
          "5e0a3a1f930bc547149fd6dfe1dc7ad7945dd74a38d46a6bc7658ac953b43770"
          "b5d9212737a3cef574796c50aaa4168f07ddabccf5d12d8f87808e526cf68e15"
          "224b8eb822048df910fe36a84a752177dbfce76a90f1ae864543e721d7885ad7")},
      {NID_ffdhe4096,
       HexToBytes(
          "525b74f0c4c3d942cd65f924cebd4f76a1ec2c866d48462e1c468f75070b18bc"
          "d6f4ce8d874895d6a9d2ad55781fcc1406b61526d1667954674cf6bb2d873ad4"
          "1128bb3f9412be3f452582bb9ea6091a39b05cd877a7774e52e44e9066a96cf2"
          "f6829f96e6e26a892cca132ae31dc771b333f4f0e011a9c9c83b245865b24ff9"
          "f6bda4adcdee17195518c58d6821f2819498631ab83a8a99e7f33bdd98d2821b"
          "e01dbd8d83dcbee7d1302597354bef404f2f17cac5febfe7cc6c5860faa39ceb"
          "236eceddf59c7d463071d2715612ed78c35d6e3783da3042862068cf206a08fe"
          "ce83f60572db55c60f6f6811f359b6f1d504e33d3054c0fe083dc7e73030ed42"
          "7f079ce60324e71e81fed25c11d2dc853a9fa9f2f64c33f92618d01b8b9bdde6"
          "2792fbc353aeb97f370f0ef85bbbd0eccbfd7104f6c4e77c7b26ff380aedb4e4"
          "f974706aa9b4c8eeb924c72d233aa90b8d0376f540ff4af63fa4a7baf47b035f"
          "f2a1564080e2c31bfc4fad3834d021858e26e4710db3e37144332b909f3340a8"
          "805b66a7cf042c37797bd46f784793e49cb16e3728e1fc6c98986d21027303ef"
          "898d32caf0131c323518ced384a9b7ae0c45c15edcb054dfe7044af3ec616ce8"
          "e5870ea2bef5aa40f4e65721d724ec68774638b13350abbb1f2ac22b0852c6e3"
          "4ab2608390ec3b971021c0c20e18e2cbcc89b1eea1c2ecb1db6eeaf4195ec7f2"),
       HexToBytes(
          "aabbccddeeff11223344556677889900aabbccddeeff11223344556677889900"),
       HexToBytes(
          "ba7d5bb3682473327e80c07bcfd58a6af9bf0fa4662288291feb847cc8121ca6"
          "12ff09bc9d46e3a76f44bad0006e1babdafef5091aed25e53037a9077af93bc5"
          "76910dbc3e6d345174b36dbec2ab92e0744dc4f5d1d25596b9aa53bc10c22dfe"
          "fec93c178b8ffd4388c07ffa9ad8a7f22c274066c92f8063b1665609aa224039"
          "aff15fb5ac07b21f9c81aace529ad5c29688d6940996b5e3a47de1b8cd3b212a"
          "3e534677df246375679cc014a77c3cc4e14aaa5eb4fc4d0f8a542a0e833a16f4"
          "dc5c46f11c5ffe14152b9c7f9e504ae01ff84db158b9e48e9fbc46b99190cad2"
          "e22113797dc7c81ad7c86bcd5e75405226459bb54b26fae179378e377ce5618e"
          "65f04d2213e1991cefe991ec43272b6c7d93b51e2ccc3bf64486efd1e5c73b3b"
          "f9344271ab9fbc43af41232ae7524c8213433ef39c64481e9cd06b9f9dc34226"
          "85dfb2d69b8dc1af0f44d6f52d1d857ec28d93f459a23386ecfe5d97130e201d"
          "90f159ff5995bbf766ceb38594b7a3192c99432e007b99f1ea7a828d15a1cba6"
          "d86cd020ff64b1774cd35e33e3696a98574cedb64534f8ca88e2690709718d66"
          "f4b88d759689819cde545d202b641b0529a02d588ff4c6b832c3f5a3d9bec9ec"
          "ce0fb9af978b76bf93eba919c5bef844b4b1e2bff3d3758b577c70fa78d89a1d"
          "d5a1864a2d3795c3668562c67aa77265f38812f001d28b25f7965109481ec2c7")
      }
  };
  for (const testInput &test : testInputs ){
    bssl::UniquePtr<BIGNUM> client_public(BN_bin2bn(test.client_pk.data(), test.client_pk.size(), nullptr));
    EXPECT_TRUE(client_public);

    bssl::UniquePtr<BIGNUM> server_secret(BN_bin2bn(test.server_sk.data(), test.server_sk.size(), nullptr));
    EXPECT_TRUE(server_secret);

    bssl::UniquePtr<DH> ffdhe2048_dh(DH_new_by_nid(test.nid));
    EXPECT_TRUE(DH_set0_key(ffdhe2048_dh.get(), nullptr, server_secret.release()));
    uint8_t buffer[4096];
    int size = DH_compute_key(buffer, client_public.get(), ffdhe2048_dh.get());
    EXPECT_TRUE(size > 0 && size < 4096);

    EXPECT_EQ(Bytes(buffer, size), Bytes(test.expected_ss));
  }
}

TEST(DHTest, LeadingZeros) {
  bssl::UniquePtr<BIGNUM> p(BN_get_rfc3526_prime_1536(nullptr));
  ASSERT_TRUE(p);
  bssl::UniquePtr<BIGNUM> g(BN_new());
  ASSERT_TRUE(g);
  ASSERT_TRUE(BN_set_word(g.get(), 2));

  bssl::UniquePtr<DH> dh(DH_new());
  ASSERT_TRUE(dh);
  ASSERT_TRUE(DH_set0_pqg(dh.get(), p.get(), /*q=*/nullptr, g.get()));
  p.release();
  g.release();

  // These values are far too small to be reasonable Diffie-Hellman keys, but
  // they are an easy way to get a shared secret with leading zeros.
  bssl::UniquePtr<BIGNUM> priv_key(BN_new()), peer_key(BN_new());
  ASSERT_TRUE(priv_key);
  ASSERT_TRUE(BN_set_word(priv_key.get(), 2));
  ASSERT_TRUE(peer_key);
  ASSERT_TRUE(BN_set_word(peer_key.get(), 3));
  ASSERT_TRUE(DH_set0_key(dh.get(), /*pub_key=*/nullptr, priv_key.get()));
  priv_key.release();

  uint8_t padded[192] = {0};
  padded[191] = 9;
  static const uint8_t kTruncated[] = {9};
  EXPECT_EQ(int(sizeof(padded)), DH_size(dh.get()));

  std::vector<uint8_t> buf(DH_size(dh.get()));
  int len = DH_compute_key(buf.data(), peer_key.get(), dh.get());
  ASSERT_GT(len, 0);
  EXPECT_EQ(Bytes(buf.data(), len), Bytes(kTruncated));

  len = DH_compute_key_padded(buf.data(), peer_key.get(), dh.get());
  ASSERT_GT(len, 0);
  EXPECT_EQ(Bytes(buf.data(), len), Bytes(padded));
}

TEST(DHTest, Overwrite) {
  // Generate a DH key with the 1536-bit MODP group.
  bssl::UniquePtr<BIGNUM> p(BN_get_rfc3526_prime_1536(nullptr));
  ASSERT_TRUE(p);
  bssl::UniquePtr<BIGNUM> g(BN_new());
  ASSERT_TRUE(g);
  ASSERT_TRUE(BN_set_word(g.get(), 2));

  bssl::UniquePtr<DH> key1(DH_new());
  ASSERT_TRUE(key1);
  ASSERT_TRUE(DH_set0_pqg(key1.get(), p.get(), /*q=*/nullptr, g.get()));
  p.release();
  g.release();
  ASSERT_TRUE(DH_generate_key(key1.get()));

  bssl::UniquePtr<BIGNUM> peer_key(BN_new());
  ASSERT_TRUE(peer_key);
  ASSERT_TRUE(BN_set_word(peer_key.get(), 42));

  // Use the key to fill in cached values.
  std::vector<uint8_t> buf1(DH_size(key1.get()));
  ASSERT_GT(DH_compute_key_padded(buf1.data(), peer_key.get(), key1.get()), 0);

  // Generate a different key with a different group.
  p.reset(BN_get_rfc3526_prime_2048(nullptr));
  ASSERT_TRUE(p);
  g.reset(BN_new());
  ASSERT_TRUE(g);
  ASSERT_TRUE(BN_set_word(g.get(), 2));

  bssl::UniquePtr<DH> key2(DH_new());
  ASSERT_TRUE(key2);
  ASSERT_TRUE(DH_set0_pqg(key2.get(), p.get(), /*q=*/nullptr, g.get()));
  p.release();
  g.release();
  ASSERT_TRUE(DH_generate_key(key2.get()));

  // Overwrite |key1|'s contents with |key2|.
  p.reset(BN_dup(DH_get0_p(key2.get())));
  ASSERT_TRUE(p);
  g.reset(BN_dup(DH_get0_g(key2.get())));
  ASSERT_TRUE(g);
  bssl::UniquePtr<BIGNUM> pub(BN_dup(DH_get0_pub_key(key2.get())));
  ASSERT_TRUE(pub);
  bssl::UniquePtr<BIGNUM> priv(BN_dup(DH_get0_priv_key(key2.get())));
  ASSERT_TRUE(priv);
  ASSERT_TRUE(DH_set0_pqg(key1.get(), p.get(), /*q=*/nullptr, g.get()));
  p.release();
  g.release();
  ASSERT_TRUE(DH_set0_key(key1.get(), pub.get(), priv.get()));
  pub.release();
  priv.release();

  // Verify that |key1| and |key2| behave equivalently.
  buf1.resize(DH_size(key1.get()));
  ASSERT_GT(DH_compute_key_padded(buf1.data(), peer_key.get(), key1.get()), 0);
  std::vector<uint8_t> buf2(DH_size(key2.get()));
  ASSERT_GT(DH_compute_key_padded(buf2.data(), peer_key.get(), key2.get()), 0);
  EXPECT_EQ(Bytes(buf1), Bytes(buf2));
}
