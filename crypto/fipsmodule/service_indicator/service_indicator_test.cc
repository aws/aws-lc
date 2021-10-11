// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/crypto.h>
#include <openssl/service_indicator.h>

#include <gtest/gtest.h>

#include <openssl/aead.h>
#include <openssl/aes.h>
#include <openssl/bn.h>
#include <openssl/cipher.h>
#include <openssl/cmac.h>
#include <openssl/digest.h>
#include <openssl/ec.h>
#include <openssl/ec_key.h>
#include <openssl/ecdh.h>
#include <openssl/ecdsa.h>
#include <openssl/hmac.h>
#include <openssl/md5.h>
#include <openssl/nid.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>
#include <openssl/sha.h>

#include "../../test/abi_test.h"
#include "../../test/file_test.h"
#include "../../test/test_util.h"
#include "../rand/internal.h"
#include "../tls/internal.h"

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

static const uint8_t kAESCMACOutput[16] = {
    0xe7, 0x32, 0x43, 0xb4, 0xae, 0x79, 0x08, 0x86, 0xe7, 0x9f, 0x0d,
    0x3f, 0x88, 0x3f, 0x1a, 0xfd
};

static const uint8_t kOutput_md5[MD5_DIGEST_LENGTH] = {
    0xc8, 0xbe, 0xdc, 0x96, 0xbe, 0xb0, 0xd6, 0x7b, 0x96, 0x7d, 0x3b,
    0xd4, 0x24, 0x29, 0x30, 0xde
};

static const uint8_t kOutput_sha1[SHA_DIGEST_LENGTH] = {
    0x5b, 0xed, 0x47, 0xcc, 0xc8, 0x8d, 0x6a, 0xf8, 0x91, 0xc1, 0x85,
    0x84, 0xe9, 0xd1, 0x31, 0xe6, 0x3e, 0x62, 0x61, 0xd9
};

static const uint8_t kOutput_sha224[SHA224_DIGEST_LENGTH] = {
    0xef, 0xad, 0x36, 0x20, 0xc6, 0x16, 0x17, 0x24, 0x49, 0x80, 0x53,
    0x7a, 0x46, 0x5b, 0xed, 0xde, 0x59, 0x9d, 0xa9, 0x19, 0xb0, 0xb8,
    0x1f, 0xbe, 0x4b, 0xa7, 0xc0, 0xea
};

static const uint8_t kOutput_sha256[SHA256_DIGEST_LENGTH] = {
    0x03, 0x19, 0x41, 0x4c, 0x62, 0x51, 0x83, 0xe5, 0x2b, 0x73, 0xf0,
    0x55, 0x51, 0x5e, 0x8e, 0x7d, 0x6f, 0x3a, 0x91, 0xf1, 0xac, 0xe0,
    0x7b, 0xb2, 0xac, 0x13, 0x65, 0x18, 0x55, 0x2c, 0x98, 0x0f
};

static const uint8_t kOutput_sha384[SHA384_DIGEST_LENGTH] = {
    0x0b, 0xbf, 0xc2, 0x06, 0x7a, 0x1e, 0xeb, 0x4a, 0x11, 0x57, 0x41,
    0x20, 0x7b, 0xfb, 0xf7, 0x2c, 0x22, 0x6b, 0x96, 0xcb, 0xc6, 0x00,
    0x81, 0xe3, 0x19, 0xf2, 0x0e, 0xcc, 0xb9, 0x5d, 0xee, 0x71, 0xda,
    0x34, 0x10, 0xae, 0x02, 0x64, 0x31, 0x07, 0x13, 0xff, 0x47, 0xf2,
    0xdf, 0xb0, 0x05, 0x03
};

static const uint8_t kOutput_sha512[SHA512_DIGEST_LENGTH] = {
    0x9d, 0xa3, 0xfa, 0xaf, 0xae, 0x0a, 0xf4, 0xe4, 0x2e, 0x68, 0xcb,
    0x7c, 0x65, 0x04, 0x76, 0x26, 0x91, 0x2a, 0x52, 0xb6, 0xb0, 0xa9,
    0x40, 0xa7, 0xf7, 0xcb, 0xc8, 0x8d, 0x4b, 0x55, 0x1b, 0x44, 0xe2,
    0x13, 0xcb, 0x6a, 0x28, 0x89, 0xa3, 0x15, 0x94, 0xc6, 0xbb, 0xcb,
    0x5d, 0xf5, 0xb3, 0x4f, 0x47, 0x8f, 0x1a, 0x44, 0x39, 0x51, 0xd2,
    0x63, 0xb1, 0x0c, 0xe1, 0x2c, 0x8d, 0x07, 0x08, 0x2f
};

static const uint8_t kOutput_sha512_256[SHA512_256_DIGEST_LENGTH] = {
    0x4f, 0x8a, 0x34, 0x49, 0xfd, 0xc8, 0x42, 0xb7, 0xc1, 0x2b, 0x6d,
    0x2a, 0x89, 0xb8, 0x10, 0x73, 0xde, 0x4a, 0x33, 0x7d, 0x3c, 0x8c,
    0xa5, 0xff, 0xee, 0xc9, 0xbb, 0x92, 0x3d, 0x47, 0x60, 0x34
};

static const uint8_t kHMACOutput_sha1[SHA_DIGEST_LENGTH] = {
    0x22, 0xbe, 0xf1, 0x4e, 0x72, 0xec, 0xfd, 0x34, 0xd9, 0x57, 0xec,
    0xf6, 0x08, 0xeb, 0x37, 0xff, 0xf9, 0x3b, 0x9f, 0xf3
};

static const uint8_t kHMACOutput_sha224[SHA224_DIGEST_LENGTH] = {
    0x5f, 0x85, 0xbd, 0xb9, 0xf9, 0x00, 0xdf, 0x81, 0xef, 0x65, 0xd3,
    0x8e, 0x7a, 0xb6, 0xd8, 0x5b, 0xf9, 0xd8, 0x62, 0x1c, 0xc5, 0x11,
    0x68, 0xb4, 0xf4, 0xd8, 0x57, 0x46
};

static const uint8_t kHMACOutput_sha256[SHA256_DIGEST_LENGTH] = {
    0x4b, 0xe9, 0x34, 0xa9, 0x37, 0x53, 0x2a, 0xb1, 0x63, 0x5d, 0x8c,
    0x22, 0x9a, 0x02, 0x37, 0x44, 0x75, 0xe1, 0x21, 0x9e, 0xf1, 0xe3,
    0x2c, 0xd0, 0x7d, 0x79, 0x03, 0x87, 0xd9, 0x69, 0x36, 0xb5
};

static const uint8_t kHMACOutput_sha384[SHA384_DIGEST_LENGTH] = {
    0x26, 0x5f, 0x4e, 0x13, 0x99, 0x04, 0xa1, 0xf4, 0xd2, 0x01, 0xd9,
    0xba, 0xe0, 0xe6, 0xa2, 0xbd, 0x50, 0x76, 0x2b, 0xc3, 0x90, 0x11,
    0x50, 0xe7, 0x26, 0xdf, 0x39, 0xf9, 0xd6, 0x8f, 0x83, 0xa5, 0xe6,
    0x8c, 0x16, 0x77, 0xbf, 0xfc, 0x77, 0x66, 0x9a, 0xe5, 0xa0, 0xb7,
    0xfe, 0xfb, 0x09, 0x5e
};

static const uint8_t kHMACOutput_sha512[SHA512_DIGEST_LENGTH] = {
    0x70, 0xf3, 0xf2, 0x82, 0xba, 0xc8, 0x14, 0xe4, 0x00, 0x9b, 0x72,
    0x8a, 0xe6, 0x07, 0xc8, 0xaf, 0x4f, 0x23, 0x0a, 0x5b, 0x16, 0xa8,
    0x9b, 0x68, 0x4f, 0x75, 0x21, 0xac, 0xb4, 0x20, 0x3d, 0x97, 0x77,
    0x21, 0x00, 0x74, 0xfa, 0xb2, 0x79, 0x28, 0x47, 0x8c, 0xa6, 0x11,
    0x85, 0xa5, 0x1e, 0x2f, 0x4a, 0x25, 0xd4, 0xf8, 0x13, 0x64, 0xd1,
    0x30, 0xd8, 0x45, 0x2c, 0x87, 0x44, 0x62, 0xc5, 0xe3
};

static const uint8_t kHMACOutput_sha512_256[SHA512_256_DIGEST_LENGTH] = {
    0xaa, 0xd0, 0x57, 0x0c, 0x98, 0x45, 0x74, 0x6b, 0x39, 0x1e, 0x07,
    0x55, 0x23, 0x08, 0xab, 0x79, 0xad, 0xe5, 0x8b, 0x48, 0xc2, 0x0c,
    0x1a, 0x37, 0x91, 0xe4, 0x8b, 0xc0, 0x9c, 0xce, 0x2c, 0x24
};

static const uint8_t kECDHPrivateKey[] = {
    0x83, 0x46, 0xa6, 0x0f, 0xc6, 0xf2, 0x93, 0xca, 0x5a, 0x0d, 0x2a,
    0xf6, 0x8b, 0xa7, 0x1d, 0x1d, 0xd3, 0x89, 0xe5, 0xe4, 0x08, 0x37,
    0x94, 0x2d, 0xf3, 0xe4, 0x3c, 0xbd
};

static const uint8_t kECDH_X[] = {
    0x8d, 0xe2, 0xe2, 0x6a, 0xdf, 0x72, 0xc5, 0x82, 0xd6, 0x56, 0x8e,
    0xf6, 0x38, 0xc4, 0xfd, 0x59, 0xb1, 0x8d, 0xa1, 0x71, 0xbd, 0xf5,
    0x01, 0xf1, 0xd9, 0x29, 0xe0, 0x48
};

static const uint8_t kECDH_Y[] = {
    0x4a, 0x68, 0xa1, 0xc2, 0xb0, 0xfb, 0x22, 0x93, 0x0d, 0x12, 0x05,
    0x55, 0xc1, 0xec, 0xe5, 0x0e, 0xa9, 0x8d, 0xea, 0x84, 0x07, 0xf7,
    0x1b, 0xe3, 0x6e, 0xfa, 0xc0, 0xde
};

static const uint8_t kECDH_PeerX[] = {
    0xaf, 0x33, 0xcd, 0x06, 0x29, 0xbc, 0x7e, 0x99, 0x63, 0x20, 0xa3,
    0xf4, 0x03, 0x68, 0xf7, 0x4d, 0xe8, 0x70, 0x4f, 0xa3, 0x7b, 0x8f,
    0xab, 0x69, 0xab, 0xaa, 0xe2, 0x80
};

static const uint8_t kECDH_PeerY[] = {
    0x88, 0x20, 0x92, 0xcc, 0xbb, 0xa7, 0x93, 0x0f, 0x41, 0x9a, 0x8a,
    0x4f, 0x9b, 0xb1, 0x69, 0x78, 0xbb, 0xc3, 0x83, 0x87, 0x29, 0x99,
    0x25, 0x59, 0xa6, 0xf2, 0xe2, 0xd7
};

static const uint8_t kECDH_Z[] = {
    0x7d, 0x96, 0xf9, 0xa3, 0xbd, 0x3c, 0x05, 0xcf, 0x5c, 0xc3, 0x7f,
    0xeb, 0x8b, 0x9d, 0x52, 0x09, 0xd5, 0xc2, 0x59, 0x74, 0x64, 0xde,
    0xc3, 0xe9, 0x98, 0x37, 0x43, 0xe8
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

static const uint8_t kTLSOutput_sha256[32] = {
    0x67, 0x85, 0xde, 0x60, 0xfc, 0x0a, 0x83, 0xe9, 0xa2, 0x2a, 0xb3,
    0xf0, 0x27, 0x0c, 0xba, 0xf7, 0xfa, 0x82, 0x3d, 0x14, 0x77, 0x1d,
    0x86, 0x29, 0x79, 0x39, 0x77, 0x8a, 0xd5, 0x0e, 0x9d, 0x32
};

static const uint8_t kTLSOutput_mdsha1[32] = {
    0x36, 0xa9, 0x31, 0xb0, 0x43, 0xe3, 0x64, 0x72, 0xb9, 0x47, 0x54,
    0x0d, 0x8a, 0xfc, 0xe3, 0x5c, 0x1c, 0x15, 0x67, 0x7e, 0xa3, 0x5d,
    0xf2, 0x3a, 0x57, 0xfd, 0x50, 0x16, 0xe1, 0xa4, 0xa6, 0x37
};

struct MD {
  // name is the name of the digest test.
  const char* name;
  // length of digest.
  const int length;
  // func is the digest to test.
  const EVP_MD *(*func)(void);
  // one_shot_func is the convenience one-shot version of the digest.
  uint8_t *(*one_shot_func)(const uint8_t *, size_t, uint8_t *);
};

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
  // input is a NUL-terminated string to hash.
  const uint8_t *input;
  // expected_digest is the expected digest.
  const uint8_t *expected_digest;
  // expected to be approved or not.
  const int expect_approved;
} kDigestTestVectors[] = {
    { md5, kPlaintext, kOutput_md5, AWSLC_NOT_APPROVED },
    { sha1, kPlaintext, kOutput_sha1, AWSLC_APPROVED },
    { sha224, kPlaintext, kOutput_sha224, AWSLC_APPROVED },
    { sha256, kPlaintext, kOutput_sha256, AWSLC_APPROVED },
    { sha384, kPlaintext, kOutput_sha384, AWSLC_APPROVED },
    { sha512, kPlaintext, kOutput_sha512, AWSLC_APPROVED },
    { sha512_256, kPlaintext, kOutput_sha512_256, AWSLC_APPROVED }
};

class EVP_MD_ServiceIndicatorTest : public testing::TestWithParam<DigestTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, EVP_MD_ServiceIndicatorTest, testing::ValuesIn(kDigestTestVectors));

TEST_P(EVP_MD_ServiceIndicatorTest, EVP_Ciphers) {
  const DigestTestVector &digestTestVector = GetParam();

  int approved = AWSLC_NOT_APPROVED;
  bssl::ScopedEVP_MD_CTX ctx;
  std::vector<uint8_t> digest(digestTestVector.md.length);
  unsigned digest_len;

  // Test running the EVP_Digest interfaces one by one directly, and check
  // |EVP_DigestFinal_ex| for approval at the end. |EVP_DigestInit_ex| and
  // |EVP_DigestUpdate| should not be approved, because the functions do not
  // indicate that a service has been fully completed yet.
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_DigestInit_ex(ctx.get(), digestTestVector.md.func(), nullptr)));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_DigestUpdate(ctx.get(), digestTestVector.input, sizeof(digestTestVector.input))));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_DigestFinal_ex(ctx.get(), digest.data(), &digest_len)));
  ASSERT_EQ(approved, digestTestVector.expect_approved);
  ASSERT_TRUE(check_test(digestTestVector.expected_digest, digest.data(), digest_len, digestTestVector.md.name));


  // Test using the one-shot |EVP_Digest| function for approval.
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(EVP_Digest(digestTestVector.input, sizeof(digestTestVector.input),
                                               digest.data(), &digest_len, digestTestVector.md.func(), nullptr)));
  ASSERT_EQ(approved, digestTestVector.expect_approved);
  ASSERT_TRUE(check_test(digestTestVector.expected_digest, digest.data(), digest_len, digestTestVector.md.name));


  // Test using the one-shot API for approval.
  CALL_SERVICE_AND_CHECK_APPROVED(approved, digestTestVector.md.one_shot_func(digestTestVector.input, sizeof(digestTestVector.input), digest.data()));
  ASSERT_EQ(approved, digestTestVector.expect_approved);
  ASSERT_TRUE(check_test(digestTestVector.expected_digest, digest.data(), digestTestVector.md.length, digestTestVector.md.name));
}

struct HMACTestVector {
  // func is the hash function for HMAC to test.
  const EVP_MD *(*func)(void);
  // input is a NUL-terminated string to hash.
  const uint8_t *input;
  // expected_digest is the expected digest.
  const uint8_t *expected_digest;
  // expected to be approved or not.
  const int expect_approved;
} kHMACTestVectors[] = {
    { EVP_sha1, kPlaintext, kHMACOutput_sha1, AWSLC_APPROVED },
    { EVP_sha224, kPlaintext, kHMACOutput_sha224, AWSLC_APPROVED },
    { EVP_sha256, kPlaintext, kHMACOutput_sha256, AWSLC_APPROVED },
    { EVP_sha384, kPlaintext, kHMACOutput_sha384, AWSLC_APPROVED },
    { EVP_sha512, kPlaintext, kHMACOutput_sha512, AWSLC_APPROVED },
    { EVP_sha512_256, kPlaintext, kHMACOutput_sha512_256, AWSLC_NOT_APPROVED }
};

class HMAC_ServiceIndicatorTest : public testing::TestWithParam<HMACTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, HMAC_ServiceIndicatorTest, testing::ValuesIn(kHMACTestVectors));

TEST_P(HMAC_ServiceIndicatorTest, HMACTest) {
  const HMACTestVector &hmacTestVector = GetParam();

  int approved = AWSLC_NOT_APPROVED;
  const uint8_t kHMACKey[64] = {0};
  const EVP_MD *digest = hmacTestVector.func();
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
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(HMAC_Update(ctx.get(), hmacTestVector.input, sizeof(hmacTestVector.input))));
  ASSERT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(HMAC_Final(ctx.get(), mac.data(), &mac_len)));
  ASSERT_EQ(approved, hmacTestVector.expect_approved);
  ASSERT_TRUE(check_test(hmacTestVector.expected_digest, mac.data(), mac_len, "HMAC KAT"));


  // Test using the one-shot API for approval.
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(HMAC(digest, key.data(),
                     key.size(), hmacTestVector.input, sizeof(hmacTestVector.input), mac.data(), &mac_len)));
  ASSERT_EQ(approved, hmacTestVector.expect_approved);
  ASSERT_TRUE(check_test(hmacTestVector.expected_digest, mac.data(), mac_len, "HMAC KAT"));
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

TEST(ServiceIndicatorTest, ECDH) {
  int approved = AWSLC_NOT_APPROVED;

  bssl::UniquePtr<EC_GROUP> group(EC_GROUP_new_by_curve_name(NID_secp224r1));
  ASSERT_TRUE(group);
  bssl::UniquePtr<BIGNUM> priv_key(BN_bin2bn(kECDHPrivateKey, sizeof(kECDHPrivateKey), nullptr));
  ASSERT_TRUE(priv_key);
  bssl::UniquePtr<BIGNUM> x(BN_bin2bn(kECDH_X, sizeof(kECDH_X), nullptr));
  ASSERT_TRUE(x);
  bssl::UniquePtr<BIGNUM> y(BN_bin2bn(kECDH_Y, sizeof(kECDH_Y), nullptr));
  ASSERT_TRUE(y);
  bssl::UniquePtr<BIGNUM> peer_x(BN_bin2bn(kECDH_PeerX, sizeof(kECDH_PeerX), nullptr));
  ASSERT_TRUE(peer_x);
  bssl::UniquePtr<BIGNUM> peer_y(BN_bin2bn(kECDH_PeerY, sizeof(kECDH_PeerY), nullptr));
  ASSERT_TRUE(peer_y);
  std::vector<uint8_t> z(kECDH_Z, kECDH_Z + sizeof(kECDH_Z));

  bssl::UniquePtr<EC_KEY> key(EC_KEY_new());
  ASSERT_TRUE(key);
  bssl::UniquePtr<EC_POINT> pub_key(EC_POINT_new(group.get()));
  ASSERT_TRUE(pub_key);
  bssl::UniquePtr<EC_POINT> peer_pub_key(EC_POINT_new(group.get()));
  ASSERT_TRUE(peer_pub_key);
  ASSERT_TRUE(EC_KEY_set_group(key.get(), group.get()));
  ASSERT_TRUE(EC_KEY_set_private_key(key.get(), priv_key.get()));
  ASSERT_TRUE(EC_POINT_set_affine_coordinates_GFp(group.get(), pub_key.get(),
                                                  x.get(), y.get(), nullptr));
  ASSERT_TRUE(EC_POINT_set_affine_coordinates_GFp(
      group.get(), peer_pub_key.get(), peer_x.get(), peer_y.get(), nullptr));
  ASSERT_TRUE(EC_KEY_set_public_key(key.get(), pub_key.get()));
  ASSERT_TRUE(EC_KEY_check_key(key.get()));

  // Test that |ECDH_compute_key_fips| has service indicator approval as
  // expected.
  uint8_t digest[SHA256_DIGEST_LENGTH];
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(ECDH_compute_key_fips(digest,
                              sizeof(digest), peer_pub_key.get(), key.get())));
  ASSERT_EQ(approved, AWSLC_APPROVED);
}

TEST(ServiceIndicatorTest, DRBG) {
  int approved = AWSLC_NOT_APPROVED;
  CTR_DRBG_STATE drbg;
  uint8_t output[256];

  // Test DRBG functions service indicator approval directly. These DRBG functions
  // are not directly accessible for external consumers however.
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(CTR_DRBG_init(&drbg,
                        kDRBGEntropy, kDRBGPersonalization, sizeof(kDRBGPersonalization))));
  ASSERT_EQ(approved, AWSLC_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(CTR_DRBG_generate(&drbg,
                        output, sizeof(kDRBGOutput), kDRBGAD, sizeof(kDRBGAD))));
  ASSERT_EQ(approved, AWSLC_APPROVED);
  ASSERT_TRUE(check_test(kDRBGOutput, output, sizeof(kDRBGOutput),"DBRG Generate KAT"));

  CALL_SERVICE_AND_CHECK_APPROVED(approved, ASSERT_TRUE(CTR_DRBG_reseed(&drbg,
                        kDRBGEntropy2, kDRBGAD, sizeof(kDRBGAD))));
  ASSERT_EQ(approved, AWSLC_APPROVED);
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

TEST(ServiceIndicatorTest, TLSKDF) {
  int approved = AWSLC_NOT_APPROVED;

  // Test approved usages of KDF.
  uint8_t tls_output[sizeof(kTLSOutput_sha256)];
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
            CRYPTO_tls1_prf(EVP_sha256(), tls_output, sizeof(tls_output), kTLSSecret,
                            sizeof(kTLSSecret), kTLSLabel, sizeof(kTLSLabel),
                            kTLSSeed1, sizeof(kTLSSeed1), kTLSSeed2,
                            sizeof(kTLSSeed2)));
  ASSERT_TRUE(check_test(kTLSOutput_sha256, tls_output, sizeof(kTLSOutput_sha256), "TLS KDF KAT for sha256"));
  ASSERT_TRUE(approved);

  CALL_SERVICE_AND_CHECK_APPROVED(approved,
            CRYPTO_tls1_prf(EVP_md5_sha1(), tls_output, sizeof(tls_output), kTLSSecret,
                            sizeof(kTLSSecret), kTLSLabel, sizeof(kTLSLabel),
                            kTLSSeed1, sizeof(kTLSSeed1), kTLSSeed2,
                            sizeof(kTLSSeed2)));
  ASSERT_TRUE(check_test(kTLSOutput_mdsha1, tls_output, sizeof(kTLSOutput_mdsha1), "TLS KDF KAT for md5_sha1"));
  ASSERT_TRUE(approved);

  // Test non-approved usages of KDF.
  CALL_SERVICE_AND_CHECK_APPROVED(approved,
            CRYPTO_tls1_prf(EVP_sha1(), tls_output, sizeof(tls_output), kTLSSecret,
                            sizeof(kTLSSecret), kTLSLabel, sizeof(kTLSLabel),
                            kTLSSeed1, sizeof(kTLSSeed1), kTLSSeed2,
                            sizeof(kTLSSeed2)));
  ASSERT_FALSE(approved);

  CALL_SERVICE_AND_CHECK_APPROVED(approved,
            CRYPTO_tls1_prf(EVP_md5(), tls_output, sizeof(tls_output), kTLSSecret,
                            sizeof(kTLSSecret), kTLSLabel, sizeof(kTLSLabel),
                            kTLSSeed1, sizeof(kTLSSeed1), kTLSSeed2,
                            sizeof(kTLSSeed2)));
  ASSERT_FALSE(approved);
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


