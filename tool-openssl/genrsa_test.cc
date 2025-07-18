// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/bio.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <openssl/err.h>
#include <string>
#include <cstdio>
#include <sys/stat.h>
#include "internal.h"
#include "test_util.h"
#include "../crypto/test/test_util.h"

// Define standard key sizes for testing
const std::vector<unsigned> kStandardKeySizes = {1024, 2048, 3072, 4096};
const unsigned kDefaultKeySize = 2048;

// Base test fixture with common functionality
class GenRSATestBase : public ::testing::Test {
protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u) << "Failed to create temporary file path for tool output";
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u) << "Failed to create temporary file path for OpenSSL output";
    
    awslc_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
  }
  
  void TearDown() override {
    RemoveFile(out_path_tool);
    RemoveFile(out_path_openssl);
  }

  bool ValidateKey(const char* path, unsigned expected_bits, bool check_components = false) {
    ScopedFILE file(fopen(path, "rb"));
    if (!file) {
      ADD_FAILURE() << "Failed to open key file: " << path;
      return false;
    }

    bssl::UniquePtr<RSA> rsa(PEM_read_RSAPrivateKey(file.get(), nullptr, nullptr, nullptr));
    if (!rsa) {
      ADD_FAILURE() << "Failed to read RSA key";
      return false;
    }

    unsigned actual_bits = static_cast<unsigned>(RSA_bits(rsa.get()));
    if (actual_bits != expected_bits) {
      ADD_FAILURE() << "Incorrect key size. Expected: " << expected_bits << ", Got: " << actual_bits;
      return false;
    }

    if (check_components) {
      const BIGNUM *n = nullptr, *e = nullptr, *d = nullptr, *p = nullptr, *q = nullptr;
      const BIGNUM *dmp1 = nullptr, *dmq1 = nullptr, *iqmp = nullptr;
      
      RSA_get0_key(rsa.get(), &n, &e, &d);
      RSA_get0_factors(rsa.get(), &p, &q);
      RSA_get0_crt_params(rsa.get(), &dmp1, &dmq1, &iqmp);

      if (!n || !e || !d || !p || !q || !dmp1 || !dmq1 || !iqmp) {
        ADD_FAILURE() << "Missing key components";
        return false;
      }

      if (BN_get_word(e) != RSA_F4) {
        ADD_FAILURE() << "Unexpected public exponent value";
        return false;
      }
    }

    return true;
  }

  bool GenerateKey(unsigned key_size) {
    args_list_t args{"-out", out_path_tool, std::to_string(key_size)};
    return genrsaTool(args);
  }

  bool HasCrossCompatibilityTools() {
    return awslc_executable_path != nullptr && openssl_executable_path != nullptr;
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

// Test key generation with various key sizes
TEST_P(GenRSAParamTest, KeyGeneration) {
  EXPECT_TRUE(GenerateKey(GetParam())) << "Key generation failed";
  EXPECT_TRUE(ValidateKey(out_path_tool, GetParam())) << "Key validation failed";
}

// Test key components validation
TEST_P(GenRSAParamTest, KeyComponentsValidation) {
  EXPECT_TRUE(GenerateKey(GetParam())) << "Key generation failed";
  EXPECT_TRUE(ValidateKey(out_path_tool, GetParam(), true)) << "Component validation failed";
}

// Test key uniqueness
TEST_P(GenRSAParamTest, KeyUniqueness) {
  char out_path2[PATH_MAX];
  ASSERT_GT(createTempFILEpath(out_path2), 0u) << "Failed to create second temporary file path";

  // Generate two keys of the same size
  args_list_t args1{"-out", out_path_tool, std::to_string(GetParam())};
  args_list_t args2{"-out", out_path2, std::to_string(GetParam())};
  
  EXPECT_TRUE(genrsaTool(args1)) << "First key generation failed";
  EXPECT_TRUE(genrsaTool(args2)) << "Second key generation failed";

  {
    ScopedFILE file1(fopen(out_path_tool, "rb"));
    ScopedFILE file2(fopen(out_path2, "rb"));
    ASSERT_TRUE(file1) << "Failed to open first key file";
    ASSERT_TRUE(file2) << "Failed to open second key file";

    std::string key1 = ReadFileToString(out_path_tool);
    std::string key2 = ReadFileToString(out_path2);

    ASSERT_FALSE(key1.empty()) << "First key file is empty";
    ASSERT_FALSE(key2.empty()) << "Second key file is empty";
    EXPECT_NE(key1, key2) << "Generated keys are identical";
  }

  RemoveFile(out_path2);
}

// Test OpenSSL compatibility
TEST_P(GenRSAParamTest, OpenSSLCompatibility) {
  if (!HasCrossCompatibilityTools()) {
    GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH environment variables are not set";
    return;
  }

  // Generate with AWS-LC
  EXPECT_TRUE(GenerateKey(GetParam())) << "AWS-LC key generation failed";

  // Verify with OpenSSL
  std::string verify_cmd = std::string(openssl_executable_path) + 
                         " rsa -in " + out_path_tool + " -check -noout";
  EXPECT_EQ(system(verify_cmd.c_str()), 0) << "OpenSSL verification failed";
}

INSTANTIATE_TEST_SUITE_P(
  StandardKeySizes,
  GenRSAParamTest,
  ::testing::ValuesIn(kStandardKeySizes)
);

// Test default key generation (no key size specified)
TEST_F(GenRSATest, DefaultKeyGeneration) {
  args_list_t args{"-out", out_path_tool};
  EXPECT_TRUE(genrsaTool(args)) << "Default key generation failed";
  EXPECT_TRUE(ValidateKey(out_path_tool, kDefaultKeySize)) << "Default key validation failed";
}

// Test help option
TEST_F(GenRSATest, HelpOption) {
  args_list_t args{"-help"};
  EXPECT_TRUE(genrsaTool(args)) << "Help command failed";
}

// Test error cases
TEST_F(GenRSATest, ErrorCases) {
  // Test incorrect argument order
  {
    args_list_t args{"2048", "-out", out_path_tool};
    EXPECT_FALSE(genrsaTool(args)) << "Command should fail with incorrect argument order";
  }

  // Test invalid key size
  {
    args_list_t args{"-out", out_path_tool, "invalid"};
    EXPECT_FALSE(genrsaTool(args)) << "Command should fail with invalid key size";
  }

  // Test zero key size
  {
    args_list_t args{"-out", out_path_tool, "0"};
    EXPECT_FALSE(genrsaTool(args)) << "Command should fail with zero key size";
  }

  // Test invalid output path
  {
    args_list_t args{"-out", "/nonexistent/directory/key.pem"};
    EXPECT_FALSE(genrsaTool(args)) << "Command should fail with invalid output path";
  }
}
