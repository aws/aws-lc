// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "openssl/x509.h"
#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "internal.h"
#include "test_util.h"
#include "../crypto/test/test_util.h"


class VerifyTest : public ::testing::Test {
protected:
    void SetUp() override {
      ASSERT_GT(createTempFILEpath(ca_path), 0u);
      ASSERT_GT(createTempFILEpath(in_path), 0u);
      ASSERT_GT(createTempFILEpath(signkey_path), 0u);

      bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
      ASSERT_TRUE(pkey);
      bssl::UniquePtr<RSA> rsa(RSA_new());
      ASSERT_TRUE(rsa);
      bssl::UniquePtr<BIGNUM> bn(BN_new());
      ASSERT_TRUE(bn && rsa && BN_set_word(bn.get(), RSA_F4) && RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr));
      ASSERT_TRUE(EVP_PKEY_assign_RSA(pkey.get(), rsa.release()));

      ScopedFILE signkey_file(fopen(signkey_path, "wb"));
      ASSERT_TRUE(signkey_file);
      ASSERT_TRUE(PEM_write_PrivateKey(signkey_file.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr));

      bssl::UniquePtr<X509> x509(CreateAndSignX509Certificate());
      ASSERT_TRUE(x509);

      ScopedFILE in_file(fopen(in_path, "wb"));
      ASSERT_TRUE(in_file);
      ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));

      ScopedFILE ca_file(fopen(ca_path, "wb"));
      ASSERT_TRUE(ca_file);
      ASSERT_TRUE(PEM_write_X509(ca_file.get(), x509.get()));
    }
    void TearDown() override {
      RemoveFile(ca_path);
      RemoveFile(in_path);
      RemoveFile(signkey_path);
    }
    char ca_path[PATH_MAX];
    char in_path[PATH_MAX];
    char signkey_path[PATH_MAX];
};


// ----------------------------- Verify Option Tests -----------------------------

// Test -CAfile with self-signed certificate
TEST_F(VerifyTest, VerifyTestSelfSignedCertWithCAfileTest) {
  args_list_t args = {"-CAfile", ca_path, in_path};
  bool result = VerifyTool(args);
  ASSERT_TRUE(result);
}

// Test self-signed certificate without -CAfile
TEST_F(VerifyTest, VerifyTestSelfSignedCertWithoutCAfile) {
  args_list_t args = {in_path};
  bool result = VerifyTool(args);
  ASSERT_FALSE(result);
}


// -------------------- Verify OpenSSL Comparison Tests --------------------------

// Comparison tests cannot run without set up of environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.

class VerifyComparisonTest : public ::testing::Test {
protected:
    void SetUp() override {

      // Skip gtests if env variables not set
      tool_executable_path = getenv("AWSLC_TOOL_PATH");
      openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
      if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
        GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH environment variables are not set";
      }

      ASSERT_GT(createTempFILEpath(in_path), 0u);
      ASSERT_GT(createTempFILEpath(ca_path), 0u);
      ASSERT_GT(createTempFILEpath(signkey_path), 0u);
      ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
      ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);

      x509.reset(CreateAndSignX509Certificate());
      ASSERT_TRUE(x509);

      ScopedFILE in_file(fopen(in_path, "wb"));
      ASSERT_TRUE(in_file);
      ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));

      ScopedFILE ca_file(fopen(ca_path, "wb"));
      ASSERT_TRUE(ca_file);
      ASSERT_TRUE(PEM_write_X509(ca_file.get(), x509.get()));

      bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
      ASSERT_TRUE(pkey);
      bssl::UniquePtr<RSA> rsa(RSA_new());
      bssl::UniquePtr<BIGNUM> bn(BN_new());
      ASSERT_TRUE(bn && BN_set_word(bn.get(), RSA_F4) && RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr));
      ASSERT_TRUE(EVP_PKEY_assign_RSA(pkey.get(), rsa.release()));

      ScopedFILE signkey_file(fopen(signkey_path, "wb"));
      ASSERT_TRUE(signkey_file);
      ASSERT_TRUE(PEM_write_PrivateKey(signkey_file.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr));
    }

    void TearDown() override {
      if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
        RemoveFile(in_path);
        RemoveFile(out_path_tool);
        RemoveFile(out_path_openssl);
        RemoveFile(signkey_path);
        RemoveFile(ca_path);
      }
    }

    char in_path[PATH_MAX];
    char ca_path[PATH_MAX];
    char out_path_tool[PATH_MAX];
    char out_path_openssl[PATH_MAX];
    char signkey_path[PATH_MAX];
    bssl::UniquePtr<X509> x509;
    const char* tool_executable_path;
    const char* openssl_executable_path;
    std::string tool_output_str;
    std::string openssl_output_str;
};

// Test against OpenSSL output self-signed cert
// "openssl verify -CAfile cert.pem cert.pem"
TEST_F(VerifyComparisonTest, VerifyToolOpenSSLCAFileSelfSignedComparison) {
  std::string tool_command = std::string(tool_executable_path) + " verify -CAfile " + ca_path + " " + in_path + " &> " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " verify -CAfile " + ca_path + " " + in_path + " &> " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}
