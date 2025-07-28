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
      ASSERT_GT(createTempFILEpath(chain_path), 0u);
      ASSERT_GT(createTempFILEpath(in_path), 0u);

      bssl::UniquePtr<X509> x509(CreateAndSignX509Certificate());
      ASSERT_TRUE(x509);

      ScopedFILE in_file(fopen(in_path, "wb"));
      ASSERT_TRUE(in_file);
      ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));

      ScopedFILE ca_file(fopen(ca_path, "wb"));
      ASSERT_TRUE(ca_file);
      ASSERT_TRUE(PEM_write_X509(ca_file.get(), x509.get()));

      ScopedFILE chain_file(fopen(chain_path, "wb"));
      ASSERT_TRUE(chain_file);
      ASSERT_TRUE(PEM_write_X509(chain_file.get(), x509.get()));
    }
    void TearDown() override {
      RemoveFile(ca_path);
      RemoveFile(chain_path);
      RemoveFile(in_path);
    }
    char ca_path[PATH_MAX];
    char chain_path[PATH_MAX];
    char in_path[PATH_MAX];
};


// ----------------------------- Verify Option Tests -----------------------------

// Test -CAfile with self-signed certificate
TEST_F(VerifyTest, VerifyTestSelfSignedCertWithCAfileTest) {
  args_list_t args = {"-CAfile", ca_path, in_path};
  bool result = VerifyTool(args);
  ASSERT_TRUE(result);
}

// Test certificate without -CAfile 
TEST_F(VerifyTest, VerifyTestSelfSignedCertWithoutCAfile) {
  args_list_t args = {in_path};
  bool result = VerifyTool(args);
  ASSERT_FALSE(result);
}

// Test certificate with -untrusted
TEST_F(VerifyTest, VerifyTestSelfSignedCertWithUntrustedChain) {
  args_list_t args = {"-untrusted", chain_path, in_path};
  bool result = VerifyTool(args);
  ASSERT_FALSE(result);
}

// Test certificate with -untrusted and -CAfile
TEST_F(VerifyTest, VerifyTestSelfSignedCertWithCAFileAndUntrustedChain) {
  args_list_t args = {"-CAfile", ca_path, "-untrusted", chain_path, in_path};
  bool result = VerifyTool(args);
  ASSERT_TRUE(result);
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
    }

    void TearDown() override {
      if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
        RemoveFile(in_path);
        RemoveFile(out_path_tool);
        RemoveFile(out_path_openssl);
        RemoveFile(ca_path);
      }
    }

    char in_path[PATH_MAX];
    char ca_path[PATH_MAX];
    char out_path_tool[PATH_MAX];
    char out_path_openssl[PATH_MAX];
    bssl::UniquePtr<X509> x509;
    const char* tool_executable_path;
    const char* openssl_executable_path;
    std::string tool_output_str;
    std::string openssl_output_str;
};

// Test against OpenSSL with -CAfile & self-signed cert fed in as a file
// "openssl verify -CAfile cert.pem cert.pem"
TEST_F(VerifyComparisonTest, VerifyToolOpenSSLCAFileSelfSignedComparison) {
  std::string tool_command = std::string(tool_executable_path) + " verify -CAfile " + ca_path + " " + in_path + " &> " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " verify -CAfile " + ca_path + " " + in_path + " &> " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL with -CAfile & 2 self-signed cert fed in as files
// "openssl verify -CAfile cert.pem cert.pem cert.pem"
TEST_F(VerifyComparisonTest, VerifyToolOpenSSLCAFileMultipleFilesComparison) {
  std::string tool_command = std::string(tool_executable_path) + " verify -CAfile " + ca_path + " " + in_path + " " + in_path +  " &> " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " verify -CAfile " + ca_path + " " + in_path + " " + in_path + " &> " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL with -CAfile & self-signed cert fed through stdin
// "cat cert.pem | openssl verify -CAfile cert.pem"
TEST_F(VerifyComparisonTest, VerifyToolOpenSSLCAFileSelfSignedStdinComparison) {
  std::string tool_command = "cat " + std::string(ca_path) + " | " + std::string(tool_executable_path) + " verify -CAfile " + ca_path + " &> " + out_path_tool;
  std::string openssl_command = "cat " + std::string(ca_path) + " | " + std::string(openssl_executable_path) + " verify -CAfile " + ca_path + " &> " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}
