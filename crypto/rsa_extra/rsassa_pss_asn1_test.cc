// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/base.h>

#include <stdlib.h>

#include <gtest/gtest.h>

#include <openssl/bytestring.h>
#include <openssl/nid.h>

#include <openssl/rsa.h>

// Below test inputs are created by running 'openssl req -x509',
// and then exacting the bytes of RSASSA-PSS-params from generated results.

// pss_sha1_salt_absent is a DER-encoded RSASSA-PSS-params:
//    Hash Algorithm: sha1
//    Mask Algorithm: mgf1 with sha1
//    Minimum Salt Length: 0x14 (absent)
//    Trailer Field: 0xBC (absent)
static const uint8_t pss_sha1_salt_absent[] = {0x30, 0x00};

// pss_sha256_salt_absent is a DER-encoded RSASSA-PSS-params:
//    Hash Algorithm: sha256
//    Mask Algorithm: mgf1 with sha256
//    Minimum Salt Length: 0x14 (absent)
//    Trailer Field: 0xBC (absent)
static const uint8_t pss_sha256_salt_absent[] = {
    0x30, 0x2B, 0xA0, 0x0D, 0x30, 0x0B, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01,
    0x65, 0x03, 0x04, 0x02, 0x01, 0xA1, 0x1A, 0x30, 0x18, 0x06, 0x09, 0x2A,
    0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x01, 0x08, 0x30, 0x0B, 0x06, 0x09,
    0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01};

// pss_sha512_salt_absent is a DER-encoded RSASSA-PSS-params:
//    Hash Algorithm: sha512
//    Mask Algorithm: mgf1 with sha512
//    Minimum Salt Length: 0x14 (absent)
//    Trailer Field: 0xBC (absent)
static const uint8_t pss_sha512_salt_absent[] = {
    0x30, 0x2B, 0xA0, 0x0D, 0x30, 0x0B, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01,
    0x65, 0x03, 0x04, 0x02, 0x03, 0xA1, 0x1A, 0x30, 0x18, 0x06, 0x09, 0x2A,
    0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x01, 0x08, 0x30, 0x0B, 0x06, 0x09,
    0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03};

// pss_sha256_salt_default is a DER-encoded RSASSA-PSS-params:
//    Hash Algorithm: sha256
//    Mask Algorithm: mgf1 with sha256
//    Minimum Salt Length: 0x14 (default)
//    Trailer Field: 0xBC (absent)
static const uint8_t pss_sha256_salt_default[] = {
    0x30, 0x30, 0xa0, 0x0d, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86,
    0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0xa1, 0x1a, 0x30,
    0x18, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01,
    0x01, 0x08, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01,
    0x65, 0x03, 0x04, 0x02, 0x01, 0xa2, 0x03, 0x02, 0x01, 0x14};

// pss_sha256_salt_30 is a DER-encoded RSASSA-PSS-params:
//    Hash Algorithm: sha256
//    Mask Algorithm: mgf1 with sha256
//    Minimum Salt Length: 0x1e (30)
//    Trailer Field: 0xBC (absent)
static const uint8_t pss_sha256_salt_30[] = {
    0x30, 0x30, 0xa0, 0x0d, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86,
    0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0xa1, 0x1a, 0x30,
    0x18, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01,
    0x01, 0x08, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01,
    0x65, 0x03, 0x04, 0x02, 0x01, 0xa2, 0x03, 0x02, 0x01, 0x1e};

// Invalid test inputs:

// invalid_pss_salt_missing is created by removing salt field from
// pss_sha256_salt_20. This is invalid because "type-length-value" cannot
// reconcile "length" and "value".
static const uint8_t invalid_pss_salt_missing[] = {
    0x30, 0x30, 0xa0, 0x0d, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01,
    0x65, 0x03, 0x04, 0x02, 0x01, 0xa1, 0x1a, 0x30, 0x18, 0x06, 0x09, 0x2a,
    0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x08, 0x30, 0x0b, 0x06, 0x09,
    0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01};

// pss_with_invalid_sha256_oid is created by changing sha512 oid
// from 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03
// to   0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x05.
static const uint8_t pss_with_invalid_sha256_oid[] = {
    0x30, 0x2b, 0xa0, 0x0d, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01,
    0x65, 0x03, 0x04, 0x02, 0x05, 0xa1, 0x1a, 0x30, 0x18, 0x06, 0x09, 0x2a,
    0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x08, 0x30, 0x0b, 0x06, 0x09,
    0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x04};

// pss_with_invalid_mgf1_oid is created by changing mgf1 oid
// from 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x08
// to   0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x09.
static const uint8_t pss_with_invalid_mgf1_oid[] = {
    0x30, 0x2b, 0xa0, 0x0d, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01,
    0x65, 0x03, 0x04, 0x02, 0x04, 0xa1, 0x1a, 0x30, 0x18, 0x06, 0x09, 0x2a,
    0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x09, 0x30, 0x0b, 0x06, 0x09,
    0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x04};

struct RSASSAPSSParamsTestInput {
  const uint8_t *der;
  size_t der_len;
  int expected_hash_nid;
  int expected_mask_gen_nid;
  int expected_salt_len;
  int expected_trailer_field;
} kRSASSAPSSParamsTestInputs[] = {
    {pss_sha1_salt_absent, sizeof(pss_sha1_salt_absent), NID_undef, NID_undef,
     NID_undef, NID_undef},
    {pss_sha256_salt_absent, sizeof(pss_sha256_salt_absent), NID_sha256,
     NID_mgf1, NID_undef, NID_undef},
    {pss_sha512_salt_absent, sizeof(pss_sha512_salt_absent), NID_sha512,
     NID_mgf1, NID_undef, NID_undef},
    {pss_sha256_salt_default, sizeof(pss_sha256_salt_default), NID_sha256,
     NID_mgf1, 20, NID_undef},
    {pss_sha256_salt_30, sizeof(pss_sha256_salt_30), NID_sha256, NID_mgf1, 30,
     NID_undef},
};

class RSASSAPSSASN1Test
    : public testing::TestWithParam<RSASSAPSSParamsTestInput> {};

TEST_P(RSASSAPSSASN1Test, TestDecodeParams) {
  const auto &param = GetParam();
  CBS params;
  params.data = param.der;
  params.len = param.der_len;
  RSASSA_PSS_PARAMS *pss = nullptr;
  ASSERT_TRUE(RSASSA_PSS_parse_params(&params, &pss));
  // Holds ownership of heap-allocated RSASSA_PSS_PARAMS.
  bssl::UniquePtr<RSASSA_PSS_PARAMS> pss_ptr(pss);
  // Expect all bytes of params are used.
  ASSERT_FALSE(CBS_len(&params));
  // Validate Hash Algorithm of RSASSA-PSS-params.
  if (param.expected_hash_nid) {
    ASSERT_TRUE(pss->hash_algor);
    EXPECT_EQ(pss->hash_algor->nid, param.expected_hash_nid);
  } else {
    // When no expectation, make sure this value is absent.
    EXPECT_FALSE(pss->hash_algor);
  }
  // Validate Mask Algorithm of RSASSA-PSS-params.
  RSA_MGA_IDENTIFIER *mga = pss->mask_gen_algor;
  if (param.expected_hash_nid) {
    ASSERT_TRUE(mga);
    ASSERT_TRUE(mga->mask_gen);
    ASSERT_TRUE(mga->one_way_hash);
    EXPECT_EQ(mga->mask_gen->nid, param.expected_mask_gen_nid);
    EXPECT_EQ(mga->one_way_hash->nid, param.expected_hash_nid);
  } else {
    // When no expectation, make sure this value is absent.
    EXPECT_FALSE(mga);
  }
  // Validate Minimum Salt Length of RSASSA-PSS-params.
  if (param.expected_salt_len) {
    ASSERT_TRUE(pss->salt_len);
    EXPECT_EQ(pss->salt_len->value, param.expected_salt_len);
  } else {
    // When no expectation, make sure this value is absent.
    EXPECT_FALSE(pss->salt_len);
  }
  // Validate Trailer Field of RSASSA-PSS-params.
  if (param.expected_trailer_field) {
    ASSERT_TRUE(pss->trailer_field);
    EXPECT_EQ(pss->trailer_field->value, param.expected_trailer_field);
  } else {
    // When no expectation, make sure this value is absent.
    EXPECT_FALSE(pss->trailer_field);
  }
}

INSTANTIATE_TEST_SUITE_P(All, RSASSAPSSASN1Test,
                         testing::ValuesIn(kRSASSAPSSParamsTestInputs));

struct RSASSAPSSParamsInvalidInput {
  const uint8_t *der;
  size_t der_len;
} kRSASSAPSSParamsInvalidInputs[] = {
    {invalid_pss_salt_missing, sizeof(invalid_pss_salt_missing)},
    {pss_with_invalid_sha256_oid, sizeof(pss_with_invalid_sha256_oid)},
    {pss_with_invalid_mgf1_oid, sizeof(pss_with_invalid_mgf1_oid)},
};

class RSASSAPSSInvalidASN1Test
    : public testing::TestWithParam<RSASSAPSSParamsInvalidInput> {};

TEST_P(RSASSAPSSInvalidASN1Test, TestDecodeInvalidBytes) {
  const auto &param = GetParam();
  CBS params;
  params.data = param.der;
  params.len = param.der_len;
  RSASSA_PSS_PARAMS *pss = nullptr;
  ASSERT_FALSE(RSASSA_PSS_parse_params(&params, &pss));
}

INSTANTIATE_TEST_SUITE_P(All, RSASSAPSSInvalidASN1Test,
                         testing::ValuesIn(kRSASSAPSSParamsInvalidInputs));
