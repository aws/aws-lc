// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include <cctype>
#include "../crypto/test/test_util.h"
#include "internal.h"
#include "test_util.h"

class GenPKeyTest : public ::testing::Test {
 protected:
  void SetUp() override { ASSERT_GT(createTempFILEpath(out_path), 0u); }

  void TearDown() override { RemoveFile(out_path); }

  char out_path[PATH_MAX];
};

// ----------------------------- PKey Option Tests -----------------------------

// Test -out
TEST_F(GenPKeyTest, RSA_out_option) {
  args_list_t args = {"-algorithm", "RSA", "-pkeyopt",
                      "rsa_keygen_bits:3072",
                      "-out",
                      out_path};
  bool result = genpkeyTool(args);
  ASSERT_TRUE(result);

  // Verify that the generated private key is deserializable.
  ScopedFILE out_file(fopen(out_path, "rb"));
  ASSERT_TRUE(out_file);
  bssl::UniquePtr<EVP_PKEY> parsed_pkey(
      PEM_read_PrivateKey(out_file.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(parsed_pkey);
}

// Test -stdout
TEST_F(GenPKeyTest, RSA_stdout) {
  args_list_t args = {"-algorithm", "RSA", "-pkeyopt", "rsa_keygen_bits:3072"};
  bool result = genpkeyTool(args);
  ASSERT_TRUE(result);
  // The output goes to stdout, just verify the command succeeds
}

// Test ec p-256 keys
TEST_F(GenPKeyTest, ECKeys) {
  args_list_t args = {"-algorithm", "EC", "-pkeyopt",
                      "ec_paramgen_curve:P-256",
                      "-out",
                      out_path};
  bool result = genpkeyTool(args);
  ASSERT_TRUE(result);

  // Verify that the generated private key is deserializable.
  ScopedFILE out_file(fopen(out_path, "rb"));
  ASSERT_TRUE(out_file);
  bssl::UniquePtr<EVP_PKEY> parsed_pkey(
      PEM_read_PrivateKey(out_file.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(parsed_pkey);
}

// Test ed25519 keys
TEST_F(GenPKeyTest, ED25519) {
  args_list_t args = {"-algorithm", "ED25519", "-out", out_path};
  bool result = genpkeyTool(args);
  ASSERT_TRUE(result);

  // Verify that the generated private key is deserializable.
  ScopedFILE out_file(fopen(out_path, "rb"));
  ASSERT_TRUE(out_file);
  bssl::UniquePtr<EVP_PKEY> parsed_pkey(
      PEM_read_PrivateKey(out_file.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(parsed_pkey);
}
