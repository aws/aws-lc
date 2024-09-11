// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "internal.h"

#include <gtest/gtest.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/rsa.h>

#include "../../internal.h"
#include "internal.h"

class EvpPkeyCtxCtrlStrTest : public ::testing::Test {
 protected:
  void SetUp() override {}

  void TearDown() override {}
};

static bssl::UniquePtr<EVP_PKEY_CTX> gen_RSA() {
  EVP_PKEY *raw = nullptr;
  bssl::UniquePtr<EVP_PKEY_CTX> keygen_ctx(
      EVP_PKEY_CTX_new_id(EVP_PKEY_RSA, nullptr));
  if (!EVP_PKEY_keygen_init(keygen_ctx.get()) ||
      !EVP_PKEY_CTX_set_rsa_keygen_bits(keygen_ctx.get(), 2048) ||
      !EVP_PKEY_keygen(keygen_ctx.get(), &raw)) {
    return nullptr;
  }
  return bssl::UniquePtr<EVP_PKEY_CTX>(EVP_PKEY_CTX_new(raw, nullptr));
}

TEST_F(EvpPkeyCtxCtrlStrTest, RsaMissingValue) {
  // Create a EVP_PKEY_CTX with a newly generated RSA key
  bssl::UniquePtr<EVP_PKEY_CTX> ctx = gen_RSA();
  ASSERT_TRUE(ctx);
  EXPECT_FALSE(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_padding_mode", nullptr));
  unsigned long err = ERR_get_error();
  EXPECT_EQ(ERR_GET_LIB(err), ERR_LIB_EVP);
  EXPECT_EQ(ERR_GET_REASON(err), RSA_R_VALUE_MISSING);
}

TEST_F(EvpPkeyCtxCtrlStrTest, RsaPaddingModeValid) {
  bssl::UniquePtr<EVP_PKEY_CTX> ctx = gen_RSA();
  ASSERT_TRUE(ctx);

  int padding = 0;

  // Padding for sign
  ASSERT_TRUE(EVP_PKEY_sign_init(ctx.get()));

  EXPECT_TRUE(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_padding_mode", "pkcs1"));
  EXPECT_TRUE(EVP_PKEY_CTX_get_rsa_padding(ctx.get(), &padding));
  EXPECT_EQ(padding, RSA_PKCS1_PADDING);

  EXPECT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_padding_mode", "none"), 1);
  EXPECT_TRUE(EVP_PKEY_CTX_get_rsa_padding(ctx.get(), &padding));
  EXPECT_EQ(padding, RSA_NO_PADDING);

  EXPECT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_padding_mode", "pss"), 1);
  EXPECT_TRUE(EVP_PKEY_CTX_get_rsa_padding(ctx.get(), &padding));
  EXPECT_EQ(padding, RSA_PKCS1_PSS_PADDING);

  // Padding for encrypt
  ASSERT_TRUE(EVP_PKEY_encrypt_init(ctx.get()));

  EXPECT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_padding_mode", "oaep"), 1);
  EXPECT_TRUE(EVP_PKEY_CTX_get_rsa_padding(ctx.get(), &padding));
  EXPECT_EQ(padding, RSA_PKCS1_OAEP_PADDING);

  EXPECT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_padding_mode", "oeap"), 1);
  EXPECT_TRUE(EVP_PKEY_CTX_get_rsa_padding(ctx.get(), &padding));
  EXPECT_EQ(padding, RSA_PKCS1_OAEP_PADDING);

  EXPECT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_padding_mode", "nonsense"),
            -2);
}

TEST_F(EvpPkeyCtxCtrlStrTest, RsaPssSaltlen) {
  // Create a EVP_PKEY_CTX with a newly generated RSA key
  bssl::UniquePtr<EVP_PKEY_CTX> ctx = gen_RSA();
  ASSERT_TRUE(ctx);

  ASSERT_TRUE(EVP_PKEY_sign_init(ctx.get()));
  EXPECT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_padding_mode", "pss"), 1);
  EXPECT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_pss_saltlen", "128"), 1);

  int saltlen = 0;
  EXPECT_EQ(EVP_PKEY_CTX_get_rsa_pss_saltlen(ctx.get(), &saltlen), 1);
  EXPECT_EQ(saltlen, 128);

  EXPECT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_pss_saltlen", "digest"), 1);
  EXPECT_EQ(EVP_PKEY_CTX_get_rsa_pss_saltlen(ctx.get(), &saltlen), 1);
  EXPECT_EQ(saltlen, -1);

  EXPECT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_pss_saltlen", "-3"), -2);
}

TEST_F(EvpPkeyCtxCtrlStrTest, RsaKeygenBits) {
  // Create a EVP_PKEY_CTX with a newly generated RSA key
  EVP_PKEY *raw = nullptr;
  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new_id(EVP_PKEY_RSA, nullptr));
  ASSERT_TRUE(ctx);
  ASSERT_TRUE(EVP_PKEY_keygen_init(ctx.get()));
  ASSERT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_keygen_bits", "2048"), 1);
  ASSERT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_keygen_bits", "-3"), -2);
  ASSERT_TRUE(EVP_PKEY_keygen(ctx.get(), &raw));
  bssl::UniquePtr<EVP_PKEY> pkey(raw);
  ASSERT_TRUE(pkey);

  ASSERT_EQ(EVP_PKEY_bits(pkey.get()), 2048);
}

TEST_F(EvpPkeyCtxCtrlStrTest, RsaKeygenPubexp) {
  // Create a EVP_PKEY_CTX with a newly generated RSA key
  EVP_PKEY *raw = nullptr;
  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new_id(EVP_PKEY_RSA, nullptr));
  ASSERT_TRUE(ctx);
  ASSERT_TRUE(EVP_PKEY_keygen_init(ctx.get()));
  ASSERT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_keygen_pubexp", "729"), 1);
  ASSERT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_keygen_pubexp", "gg"), -2);
  ASSERT_TRUE(EVP_PKEY_keygen(ctx.get(), &raw));
  bssl::UniquePtr<EVP_PKEY> pkey(raw);
  ASSERT_TRUE(pkey);

  bssl::UniquePtr<RSA> rsa_key(EVP_PKEY_get1_RSA(pkey.get()));
  ASSERT_TRUE(rsa_key);
  const BIGNUM *const_pe_bn = RSA_get0_e(rsa_key.get());
  ASSERT_TRUE(const_pe_bn != nullptr);

  const uint64_t expected_pe = 729;
  uint64_t pe_u64;
  ASSERT_TRUE(BN_get_u64(const_pe_bn, &pe_u64));
  EXPECT_EQ(pe_u64, expected_pe);
}

TEST_F(EvpPkeyCtxCtrlStrTest, RsaMgf1Md) {
  bssl::UniquePtr<EVP_PKEY_CTX> ctx = gen_RSA();
  ASSERT_TRUE(ctx);

  ASSERT_TRUE(EVP_PKEY_sign_init(ctx.get()));
  ASSERT_TRUE(EVP_PKEY_CTX_set_rsa_padding(ctx.get(), RSA_PKCS1_PSS_PADDING));
  ASSERT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_mgf1_md", "sha256"), 1);

  const EVP_MD *out_md;
  ASSERT_TRUE(EVP_PKEY_CTX_get_rsa_mgf1_md(ctx.get(), &out_md));
  ASSERT_STREQ(EVP_MD_name(out_md), "SHA256");
}

// rsa_oaep_md
TEST_F(EvpPkeyCtxCtrlStrTest, RsaOaepMd) {
  bssl::UniquePtr<EVP_PKEY_CTX> ctx = gen_RSA();
  ASSERT_TRUE(ctx);

  ASSERT_TRUE(EVP_PKEY_encrypt_init(ctx.get()));
  ASSERT_TRUE(EVP_PKEY_CTX_set_rsa_padding(ctx.get(), RSA_PKCS1_OAEP_PADDING));
  ASSERT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_oaep_md", "sha256"), 1);

  const EVP_MD *out_md;
  ASSERT_TRUE(EVP_PKEY_CTX_get_rsa_oaep_md(ctx.get(), &out_md));
  ASSERT_STREQ(EVP_MD_name(out_md), "SHA256");
}

TEST_F(EvpPkeyCtxCtrlStrTest, RsaOaepLabel) {
  bssl::UniquePtr<EVP_PKEY_CTX> ctx = gen_RSA();
  ASSERT_TRUE(ctx);

  ASSERT_TRUE(EVP_PKEY_encrypt_init(ctx.get()));
  ASSERT_TRUE(EVP_PKEY_CTX_set_rsa_padding(ctx.get(), RSA_PKCS1_OAEP_PADDING));
  ASSERT_TRUE(EVP_PKEY_CTX_set_rsa_oaep_md(ctx.get(), EVP_sha256()));
  ASSERT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_oaep_label", "aabb11"), 1);
  ASSERT_EQ(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_oaep_label", "gg"), -2);

  const char expected_label[4] = "\xaa\xbb\x11";
  const uint8_t *actual_label;
  ASSERT_TRUE(EVP_PKEY_CTX_get0_rsa_oaep_label(ctx.get(), &actual_label));

  ASSERT_TRUE(OPENSSL_memcmp(actual_label, expected_label, 3) == 0);
}
