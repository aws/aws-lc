// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <sys/stat.h>
#include <cstdio>
#include <string>
#include "../crypto/test/test_util.h"
#include "internal.h"
#include "test_util.h"

// Define standard key sizes for testing
const std::vector<unsigned> kStandardKeySizes = {1024, 2048, 3072, 4096};

// Base test fixture with common functionality
class GenRSATestBase : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u)
        << "Failed to create temporary file path for tool output";
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u)
        << "Failed to create temporary file path for OpenSSL output";

    awslc_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
  }

  void TearDown() override {
    RemoveFile(out_path_tool);
    RemoveFile(out_path_openssl);
  }

  // CLI-focused validation: file exists, readable, basic PEM format
  bool ValidateKeyFile(const char *path) {
    if (!path) {
      ADD_FAILURE() << "Path parameter is null";
      return false;
    }

    // Check file exists and is readable
    ScopedFILE file(fopen(path, "rb"));
    if (!file) {
      ADD_FAILURE() << "Failed to open key file: " << path;
      return false;
    }

    // Basic PEM format validation - check for PEM headers
    std::string content = ReadFileToString(path);
    if (content.find("-----BEGIN RSA PRIVATE KEY-----") == std::string::npos ||
        content.find("-----END RSA PRIVATE KEY-----") == std::string::npos) {
      ADD_FAILURE() << "File does not contain valid PEM RSA private key format";
      return false;
    }

    // Verify the key can be parsed (basic sanity check)
    bssl::UniquePtr<RSA> rsa(
        PEM_read_RSAPrivateKey(file.get(), nullptr, nullptr, nullptr));
    if (!rsa) {
      ADD_FAILURE() << "Failed to parse RSA key from PEM file";
      return false;
    }

    return true;
  }

  bool GenerateKey(unsigned key_size) {
    args_list_t args{"-out", out_path_tool, std::to_string(key_size)};
    return genrsaTool(args);
  }

  bool GenerateKeyToStdout(unsigned key_size) {
    // Test stdout output by not providing -out
    args_list_t args{std::to_string(key_size)};
    return genrsaTool(args);
  }

  bool HasCrossCompatibilityTools() {
    return awslc_executable_path != nullptr &&
           openssl_executable_path != nullptr;
  }

  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  const char *awslc_executable_path = nullptr;
  const char *openssl_executable_path = nullptr;
};

// Non-parameterized test fixture
class GenRSATest : public GenRSATestBase {};

// Parameterized test fixture
class GenRSAParamTest : public GenRSATestBase,
                        public ::testing::WithParamInterface<unsigned> {};

// Test CLI can generate key files for various key sizes
TEST_P(GenRSAParamTest, GeneratesKeyFile) {
  EXPECT_TRUE(GenerateKey(GetParam())) << "Key generation failed";
  EXPECT_TRUE(ValidateKeyFile(out_path_tool)) << "Generated key file validation failed";
}

// Test OpenSSL compatibility - this is a CLI integration concern
TEST_P(GenRSAParamTest, OpenSSLCompatibility) {
  if (!HasCrossCompatibilityTools()) {
    GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH "
                    "environment variables are not set";
    return;
  }

  // Generate with AWS-LC
  EXPECT_TRUE(GenerateKey(GetParam())) << "AWS-LC key generation failed";

  // Verify with OpenSSL - tests PEM format compatibility
  std::string verify_cmd = std::string(openssl_executable_path) + " rsa -in " +
                           out_path_tool + " -check -noout";
  EXPECT_EQ(system(verify_cmd.c_str()), 0) << "OpenSSL verification failed";
}

INSTANTIATE_TEST_SUITE_P(StandardKeySizes, GenRSAParamTest,
                         ::testing::ValuesIn(kStandardKeySizes));

// Test default key generation (no key size specified)
TEST_F(GenRSATest, DefaultKeyGeneration) {
  args_list_t args{"-out", out_path_tool};
  EXPECT_TRUE(genrsaTool(args)) << "Default key generation failed";
  EXPECT_TRUE(ValidateKeyFile(out_path_tool)) << "Default key file validation failed";
}

// Test help option displays usage information
TEST_F(GenRSATest, HelpOption) {
  args_list_t args{"-help"};
  EXPECT_TRUE(genrsaTool(args)) << "Help command failed";
}

// Test stdout output (no -out specified)
TEST_F(GenRSATest, StdoutOutput) {
  // This test verifies the CLI can output to stdout
  // We can't easily capture stdout in this test framework,
  // but we can verify the command succeeds
  EXPECT_TRUE(GenerateKeyToStdout(2048)) << "Stdout key generation failed";
}

// Test file output vs stdout behavior
TEST_F(GenRSATest, FileVsStdoutOutput) {
  // Test file output
  args_list_t file_args{"-out", out_path_tool, "2048"};
  EXPECT_TRUE(genrsaTool(file_args)) << "File output failed";
  EXPECT_TRUE(ValidateKeyFile(out_path_tool)) << "File output validation failed";
  
  // Test that file has content
  std::string file_content = ReadFileToString(out_path_tool);
  EXPECT_FALSE(file_content.empty()) << "Generated key file is empty";
  EXPECT_GT(file_content.length(), 100u) << "Generated key file seems too small";
}

// Test CLI argument parsing and error handling
TEST_F(GenRSATest, ArgumentParsingErrors) {
  // Test incorrect argument order
  {
    args_list_t args{"2048", "-out", out_path_tool};
    EXPECT_FALSE(genrsaTool(args))
        << "Command should fail with incorrect argument order";
  }

  // Test invalid key size
  {
    args_list_t args{"-out", out_path_tool, "invalid"};
    EXPECT_FALSE(genrsaTool(args))
        << "Command should fail with invalid key size";
  }

  // Test zero key size
  {
    args_list_t args{"-out", out_path_tool, "0"};
    EXPECT_FALSE(genrsaTool(args)) << "Command should fail with zero key size";
  }
}

// Test file I/O error handling
TEST_F(GenRSATest, FileIOErrors) {
  // Test invalid output path
  {
    args_list_t args{"-out", "/nonexistent/directory/key.pem", "2048"};
    EXPECT_FALSE(genrsaTool(args))
        << "Command should fail with invalid output path";
  }
}

// Test argument validation
TEST_F(GenRSATest, ArgumentValidation) {
  // Test missing key size (should use default)
  {
    args_list_t args{"-out", out_path_tool};
    EXPECT_TRUE(genrsaTool(args)) << "Default key size should work";
    EXPECT_TRUE(ValidateKeyFile(out_path_tool)) << "Default key should be valid";
  }

  // Test help takes precedence
  {
    args_list_t args{"-help", "-out", out_path_tool, "2048"};
    EXPECT_TRUE(genrsaTool(args)) << "Help should work even with other args";
  }
}
