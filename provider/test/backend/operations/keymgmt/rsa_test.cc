// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include <openssl/bn.h>
#include <openssl/err.h>
#include <openssl/rsa.h>

#include <stdint.h>
#include <string.h>

#include <memory>
#include <string>
#include <vector>

#include "internal/backend.h"
#include "internal/backend/keymgmt.h"

namespace {

struct BnDeleter {
  void operator()(BIGNUM *bn) const { BN_free(bn); }
};
using BnPtr = std::unique_ptr<BIGNUM, BnDeleter>;

struct ProviderBnDeleter {
  void operator()(void *bn) const { BN_clear_free(static_cast<BIGNUM *>(bn)); }
};
using ProviderBnPtr = std::unique_ptr<void, ProviderBnDeleter>;

struct ProviderRsaDeleter {
  void operator()(void *rsa) const { awslc_prov_rsa_free(rsa); }
};
using ProviderRsaPtr = std::unique_ptr<void, ProviderRsaDeleter>;

std::vector<unsigned char> Encode(const void *bn) {
  size_t size = 0;
  EXPECT_TRUE(awslc_prov_bn_to_bytes(bn, 0, nullptr, 0, &size));
  std::vector<unsigned char> out(size);
  size_t written = 0;
  EXPECT_TRUE(awslc_prov_bn_to_bytes(bn, 0, out.data(), out.size(), &written));
  EXPECT_EQ(out.size(), written);
  return out;
}

AWSLC_PROV_BN_BYTES View(const std::vector<unsigned char> &bytes,
                         int is_signed = 0) {
  return AWSLC_PROV_BN_BYTES{bytes.data(), bytes.size(), is_signed};
}

// A uint32_t's in-memory representation is host byte order by definition, so
// it is an encoding independent of the conversion under test.
TEST(BackendBnTest, ReadsAndWritesHostByteOrder) {
  const uint32_t value = 0x01020304;
  unsigned char bytes[sizeof(value)];
  memcpy(bytes, &value, sizeof(value));

  const AWSLC_PROV_BN_BYTES in = {bytes, sizeof(bytes), 0};
  ProviderBnPtr bn(awslc_prov_bn_from_bytes(&in));
  ASSERT_TRUE(bn);
  EXPECT_EQ(value, BN_get_word(static_cast<const BIGNUM *>(bn.get())));

  uint64_t widened = 0;
  size_t written = 0;
  ASSERT_TRUE(awslc_prov_bn_to_bytes(
      bn.get(), 0, reinterpret_cast<unsigned char *>(&widened), sizeof(widened),
      &written));
  EXPECT_EQ(sizeof(widened), written);
  EXPECT_EQ(static_cast<uint64_t>(value), widened);
}

TEST(BackendBnTest, RefusesNegativeSignedValues) {
  const int32_t negative = -5;
  const int32_t positive = 5;
  const uint32_t high_bit = 0x80000000u;
  unsigned char bytes[sizeof(int32_t)];

  memcpy(bytes, &negative, sizeof(bytes));
  AWSLC_PROV_BN_BYTES in = {bytes, sizeof(bytes), 1};
  EXPECT_EQ(nullptr, awslc_prov_bn_from_bytes(&in));

  memcpy(bytes, &positive, sizeof(bytes));
  ProviderBnPtr five(awslc_prov_bn_from_bytes(&in));
  ASSERT_TRUE(five);
  EXPECT_EQ(5u, BN_get_word(static_cast<const BIGNUM *>(five.get())));

  // The same bytes are a magnitude when unsigned.
  memcpy(bytes, &high_bit, sizeof(bytes));
  in.is_signed = 0;
  ProviderBnPtr magnitude(awslc_prov_bn_from_bytes(&in));
  ASSERT_TRUE(magnitude);
  EXPECT_EQ(high_bit,
            BN_get_word(static_cast<const BIGNUM *>(magnitude.get())));
  in.is_signed = 1;
  EXPECT_EQ(nullptr, awslc_prov_bn_from_bytes(&in));
}

TEST(BackendBnTest, ProbesSizeAndRefusesUndersizedOutput) {
  BnPtr bn(BN_new());
  ASSERT_TRUE(bn);
  ASSERT_TRUE(BN_set_word(bn.get(), 0x010203));

  size_t size = 0;
  ASSERT_TRUE(awslc_prov_bn_to_bytes(bn.get(), 0, nullptr, 0, &size));
  EXPECT_EQ(3u, size);
  ASSERT_TRUE(awslc_prov_bn_to_bytes(bn.get(), 1, nullptr, 0, &size));
  EXPECT_EQ(4u, size);

  const unsigned char kCanary = 0xa5;
  std::vector<unsigned char> out(3, kCanary);
  size = 0;
  EXPECT_FALSE(
      awslc_prov_bn_to_bytes(bn.get(), 1, out.data(), out.size(), &size));
  EXPECT_EQ(4u, size);
  for (unsigned char byte : out) {
    EXPECT_EQ(kCanary, byte);
  }

  BnPtr zero(BN_new());
  ASSERT_TRUE(zero);
  ASSERT_TRUE(awslc_prov_bn_to_bytes(zero.get(), 0, nullptr, 0, &size));
  EXPECT_EQ(1u, size);
}

// One generated key, decomposed into the OSSL_PARAM encoding, from which each
// test rebuilds the shapes it needs.
class BackendRsaTest : public ::testing::Test {
 protected:
  static void SetUpTestSuite() {
    key_ = awslc_prov_rsa_generate(2048);
    if (key_ == nullptr) {
      return;
    }
    for (int c = 0; c < AWSLC_PROV_RSA_COMPONENT_COUNT; c++) {
      encoded_[c] = Encode(
          awslc_prov_rsa_get0(key_, static_cast<AWSLC_PROV_RSA_COMPONENT>(c)));
    }
  }

  static void TearDownTestSuite() {
    awslc_prov_rsa_free(key_);
    key_ = nullptr;
  }

  void SetUp() override {
    ASSERT_NE(nullptr, key_) << "could not generate the test key";
    ERR_clear_error();
  }
  void TearDown() override { ERR_clear_error(); }

  // The components named in |present|, the rest absent.
  static std::vector<AWSLC_PROV_BN_BYTES> Shape(
      std::initializer_list<AWSLC_PROV_RSA_COMPONENT> present) {
    std::vector<AWSLC_PROV_BN_BYTES> components(
        AWSLC_PROV_RSA_COMPONENT_COUNT, AWSLC_PROV_BN_BYTES{nullptr, 0, 0});
    for (AWSLC_PROV_RSA_COMPONENT c : present) {
      components[c] = View(encoded_[c]);
    }
    return components;
  }

  static int Has(const void *rsa, AWSLC_PROV_RSA_COMPONENT c) {
    return awslc_prov_rsa_get0(rsa, c) != nullptr;
  }

  static void *key_;
  static std::vector<unsigned char> encoded_[AWSLC_PROV_RSA_COMPONENT_COUNT];
};

void *BackendRsaTest::key_ = nullptr;
std::vector<unsigned char>
    BackendRsaTest::encoded_[AWSLC_PROV_RSA_COMPONENT_COUNT];

constexpr AWSLC_PROV_RSA_COMPONENT kAll[] = {
    AWSLC_PROV_RSA_N,    AWSLC_PROV_RSA_E,   AWSLC_PROV_RSA_D,
    AWSLC_PROV_RSA_P,    AWSLC_PROV_RSA_Q,   AWSLC_PROV_RSA_DMP1,
    AWSLC_PROV_RSA_DMQ1, AWSLC_PROV_RSA_IQMP};

TEST_F(BackendRsaTest, BuildsEachSupportedShape) {
  ProviderRsaPtr pub(
      awslc_prov_rsa_new(Shape({AWSLC_PROV_RSA_N, AWSLC_PROV_RSA_E}).data()));
  ASSERT_TRUE(pub);
  EXPECT_TRUE(Has(pub.get(), AWSLC_PROV_RSA_N));
  EXPECT_FALSE(Has(pub.get(), AWSLC_PROV_RSA_D));

  ProviderRsaPtr no_crt(awslc_prov_rsa_new(
      Shape({AWSLC_PROV_RSA_N, AWSLC_PROV_RSA_E, AWSLC_PROV_RSA_D}).data()));
  ASSERT_TRUE(no_crt);
  EXPECT_TRUE(Has(no_crt.get(), AWSLC_PROV_RSA_D));
  EXPECT_FALSE(Has(no_crt.get(), AWSLC_PROV_RSA_P));

  std::vector<AWSLC_PROV_BN_BYTES> all(AWSLC_PROV_RSA_COMPONENT_COUNT);
  for (AWSLC_PROV_RSA_COMPONENT c : kAll) {
    all[c] = View(encoded_[c]);
  }
  ProviderRsaPtr full(awslc_prov_rsa_new(all.data()));
  ASSERT_TRUE(full);
  for (AWSLC_PROV_RSA_COMPONENT c : kAll) {
    EXPECT_EQ(encoded_[c], Encode(awslc_prov_rsa_get0(full.get(), c)))
        << "component " << c;
  }
  ProviderRsaPtr public_copy(awslc_prov_rsa_new_public(full.get()));
  ASSERT_TRUE(public_copy);
  EXPECT_FALSE(Has(public_copy.get(), AWSLC_PROV_RSA_D));
  EXPECT_TRUE(awslc_prov_bn_equal(
      awslc_prov_rsa_get0(public_copy.get(), AWSLC_PROV_RSA_N),
      awslc_prov_rsa_get0(full.get(), AWSLC_PROV_RSA_N)));
}

TEST_F(BackendRsaTest, RefusesShapesWithoutAConstructor) {
  EXPECT_EQ(nullptr, awslc_prov_rsa_new(Shape({AWSLC_PROV_RSA_N}).data()));
  EXPECT_EQ(nullptr, awslc_prov_rsa_new(
                         Shape({AWSLC_PROV_RSA_N, AWSLC_PROV_RSA_D}).data()));
  EXPECT_EQ(nullptr,
            awslc_prov_rsa_new(Shape({AWSLC_PROV_RSA_N, AWSLC_PROV_RSA_E,
                                      AWSLC_PROV_RSA_P, AWSLC_PROV_RSA_Q})
                                   .data()));
  EXPECT_EQ(nullptr,
            awslc_prov_rsa_new(
                Shape({AWSLC_PROV_RSA_N, AWSLC_PROV_RSA_E, AWSLC_PROV_RSA_D,
                       AWSLC_PROV_RSA_P, AWSLC_PROV_RSA_Q})
                    .data()));
}

// A 35-bit e is past AWS-LC's default bound, so it takes the _large_e
// constructor where one exists.
TEST_F(BackendRsaTest, AcceptsLargePublicExponentWhereAwslcCan) {
  BnPtr large(BN_new());
  ASSERT_TRUE(large);
  ASSERT_TRUE(BN_set_u64(large.get(), (UINT64_C(1) << 34) + 1));
  const std::vector<unsigned char> large_e = Encode(large.get());

  std::vector<AWSLC_PROV_BN_BYTES> pub =
      Shape({AWSLC_PROV_RSA_N, AWSLC_PROV_RSA_E});
  pub[AWSLC_PROV_RSA_E] = View(large_e);
  ProviderRsaPtr rsa(awslc_prov_rsa_new(pub.data()));
  ASSERT_TRUE(rsa);
  EXPECT_TRUE(awslc_prov_bn_equal(
      large.get(), awslc_prov_rsa_get0(rsa.get(), AWSLC_PROV_RSA_E)));

  ProviderRsaPtr public_copy(awslc_prov_rsa_new_public(rsa.get()));
  EXPECT_TRUE(public_copy);
}

TEST_F(BackendRsaTest, TranslatesAwslcImportFailure) {
  // The frontend suite matches on these values without AWS-LC's headers.
  EXPECT_EQ(4, ERR_LIB_RSA);
  EXPECT_EQ(132, RSA_R_N_NOT_EQUAL_P_Q);
  EXPECT_EQ(104, RSA_R_BAD_RSA_PARAMETERS);

  BnPtr q(BN_dup(static_cast<const BIGNUM *>(
      awslc_prov_rsa_get0(key_, AWSLC_PROV_RSA_Q))));
  ASSERT_TRUE(q);
  ASSERT_TRUE(BN_add_word(q.get(), 2));
  const std::vector<unsigned char> wrong_q = Encode(q.get());

  std::vector<AWSLC_PROV_BN_BYTES> components(AWSLC_PROV_RSA_COMPONENT_COUNT);
  for (AWSLC_PROV_RSA_COMPONENT c : kAll) {
    components[c] = View(encoded_[c]);
  }
  components[AWSLC_PROV_RSA_Q] = View(wrong_q);
  ERR_clear_error();
  EXPECT_EQ(nullptr, awslc_prov_rsa_new(components.data()));

  AWSLC_PROV_ERROR record;
  ASSERT_TRUE(awslc_prov_error_shift(&record));
  EXPECT_EQ(AWSLC_PROV_ERROR_REASON(ERR_LIB_RSA, RSA_R_N_NOT_EQUAL_P_Q),
            record.reason);
  EXPECT_NE(std::string::npos,
            std::string(record.detail).find("N_NOT_EQUAL_P_Q"))
      << record.detail;
}

}  // namespace
