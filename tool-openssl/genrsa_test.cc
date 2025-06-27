// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/bio.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <openssl/err.h>
#include <fstream>
#include <string>
#include <cstdio>
#include <sys/stat.h>
#include "internal.h"
#include "test_util.h"
#include "../crypto/test/test_util.h"

class GenRSATest : public ::testing::Test {
protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);
  }
  
  void TearDown() override {
    RemoveFile(out_path_tool);
    RemoveFile(out_path_openssl);
  }
  
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  
  // Validate RSA key from PEM content
  bool ValidateRSAKey(const std::string& pem_content, unsigned expected_bits) {
    bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(pem_content.c_str(), pem_content.length()));
    if (!bio) return false;
    
    bssl::UniquePtr<RSA> rsa(PEM_read_bio_RSAPrivateKey(bio.get(), nullptr, nullptr, nullptr));
    if (!rsa) return false;
    
    int key_bits = RSA_bits(rsa.get());
    if (static_cast<unsigned>(key_bits) != expected_bits) return false;
    
    // Verify key components exist
    const BIGNUM *n, *e, *d;
    RSA_get0_key(rsa.get(), &n, &e, &d);
    
    return n != nullptr && e != nullptr && d != nullptr;
  }
  
  // Check if content is valid PEM private key (either format)
  bool IsPEMPrivateKey(const std::string& content) {
    return (content.find("-----BEGIN RSA PRIVATE KEY-----") != std::string::npos &&
            content.find("-----END RSA PRIVATE KEY-----") != std::string::npos) ||
           (content.find("-----BEGIN PRIVATE KEY-----") != std::string::npos &&
            content.find("-----END PRIVATE KEY-----") != std::string::npos);
  }
};

// ----------------------------- Basic Functionality Tests -----------------------------

TEST_F(GenRSATest, DefaultKeyGeneration) {
  std::string command = std::string("./tool-openssl/openssl genrsa -out ") + out_path_tool;
  int result = system(command.c_str());
  ASSERT_EQ(result, 0);
  
  std::string key_content = ReadFileToString(out_path_tool);
  ASSERT_FALSE(key_content.empty());
  ASSERT_TRUE(IsPEMPrivateKey(key_content));
  ASSERT_TRUE(ValidateRSAKey(key_content, 2048));
}

TEST_F(GenRSATest, CustomKeySize4096) {
  std::string command = std::string("./tool-openssl/openssl genrsa -out ") + out_path_tool + " 4096";
  int result = system(command.c_str());
  ASSERT_EQ(result, 0);
  
  std::string key_content = ReadFileToString(out_path_tool);
  ASSERT_FALSE(key_content.empty());
  ASSERT_TRUE(IsPEMPrivateKey(key_content));
  ASSERT_TRUE(ValidateRSAKey(key_content, 4096));
}

TEST_F(GenRSATest, CustomKeySize1024) {
  std::string command = std::string("./tool-openssl/openssl genrsa -out ") + out_path_tool + " 1024";
  int result = system(command.c_str());
  ASSERT_EQ(result, 0);
  
  std::string key_content = ReadFileToString(out_path_tool);
  ASSERT_FALSE(key_content.empty());
  ASSERT_TRUE(IsPEMPrivateKey(key_content));
  ASSERT_TRUE(ValidateRSAKey(key_content, 1024));
}

// ----------------------------- Error Handling Tests -----------------------------

TEST_F(GenRSATest, InvalidKeySize) {
  std::string command = std::string("./tool-openssl/openssl genrsa -out ") + out_path_tool + " invalid";
  int result = system(command.c_str());
  ASSERT_NE(result, 0);
}

TEST_F(GenRSATest, ZeroKeySize) {
  std::string command = std::string("./tool-openssl/openssl genrsa -out ") + out_path_tool + " 0";
  int result = system(command.c_str());
  ASSERT_NE(result, 0);
}

TEST_F(GenRSATest, InvalidOutputPath) {
  std::string command = "./tool-openssl/openssl genrsa -out /nonexistent/directory/key.pem";
  int result = system(command.c_str());
  ASSERT_NE(result, 0);
}

TEST_F(GenRSATest, HelpOption) {
  int result = system("./tool-openssl/openssl genrsa -help");
  ASSERT_EQ(result, 0);
}

// ----------------------------- OpenSSL Cross-Compatibility Tests -----------------------------

// Cross-compatibility tests require environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.

class GenRSAComparisonTest : public ::testing::Test {
protected:
  void SetUp() override {
    // Skip gtests if env variables not set
    awslc_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
    if (awslc_executable_path == nullptr || openssl_executable_path == nullptr) {
      GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH environment variables are not set";
    }
    
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);
  }
  
  void TearDown() override {
    if (awslc_executable_path != nullptr && openssl_executable_path != nullptr) {
      RemoveFile(out_path_tool);
      RemoveFile(out_path_openssl);
    }
  }
  
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  const char *awslc_executable_path;
  const char *openssl_executable_path;
  std::string tool_output_str;
  std::string openssl_output_str;
  
  // Validate RSA key from PEM content (handles both formats)
  bool ValidateRSAKey(const std::string& pem_content, unsigned expected_bits) {
    bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(pem_content.c_str(), pem_content.length()));
    if (!bio) return false;
    
    bssl::UniquePtr<RSA> rsa(PEM_read_bio_RSAPrivateKey(bio.get(), nullptr, nullptr, nullptr));
    if (!rsa) return false;
    
    return static_cast<unsigned>(RSA_bits(rsa.get())) == expected_bits;
  }
  
  // Check if content is valid PEM private key (either format)
  bool IsPEMPrivateKey(const std::string& content) {
    return (content.find("-----BEGIN RSA PRIVATE KEY-----") != std::string::npos &&
            content.find("-----END RSA PRIVATE KEY-----") != std::string::npos) ||
           (content.find("-----BEGIN PRIVATE KEY-----") != std::string::npos &&
            content.find("-----END PRIVATE KEY-----") != std::string::npos);
  }
};

TEST_F(GenRSAComparisonTest, ArgumentCompatibilityDefault) {
  // Test that both tools accept the same arguments and produce valid keys
  std::string tool_cmd = std::string(awslc_executable_path) + " genrsa -out " + out_path_tool;
  std::string openssl_cmd = std::string(openssl_executable_path) + " genrsa -out " + out_path_openssl;
  
  int tool_result = system(tool_cmd.c_str());
  int openssl_result = system(openssl_cmd.c_str());
  
  // Both commands should succeed
  ASSERT_EQ(tool_result, 0) << "AWS-LC genrsa command failed";
  ASSERT_EQ(openssl_result, 0) << "OpenSSL genrsa command failed";
  
  // Both should produce valid 2048-bit keys
  std::string tool_output = ReadFileToString(out_path_tool);
  std::string openssl_output = ReadFileToString(out_path_openssl);
  
  ASSERT_TRUE(IsPEMPrivateKey(tool_output)) << "AWS-LC output is not a valid PEM key";
  ASSERT_TRUE(IsPEMPrivateKey(openssl_output)) << "OpenSSL output is not a valid PEM key";
  ASSERT_TRUE(ValidateRSAKey(tool_output, 2048)) << "AWS-LC key is not valid 2048-bit RSA";
  ASSERT_TRUE(ValidateRSAKey(openssl_output, 2048)) << "OpenSSL key is not valid 2048-bit RSA";
}

TEST_F(GenRSAComparisonTest, ArgumentCompatibility4096) {
  // Test that both tools handle custom key sizes identically
  std::string tool_cmd = std::string(awslc_executable_path) + " genrsa -out " + out_path_tool + " 4096";
  std::string openssl_cmd = std::string(openssl_executable_path) + " genrsa -out " + out_path_openssl + " 4096";
  
  int tool_result = system(tool_cmd.c_str());
  int openssl_result = system(openssl_cmd.c_str());
  
  ASSERT_EQ(tool_result, 0) << "AWS-LC genrsa 4096 command failed";
  ASSERT_EQ(openssl_result, 0) << "OpenSSL genrsa 4096 command failed";
  
  std::string tool_output = ReadFileToString(out_path_tool);
  std::string openssl_output = ReadFileToString(out_path_openssl);
  
  ASSERT_TRUE(ValidateRSAKey(tool_output, 4096)) << "AWS-LC key is not valid 4096-bit RSA";
  ASSERT_TRUE(ValidateRSAKey(openssl_output, 4096)) << "OpenSSL key is not valid 4096-bit RSA";
}

TEST_F(GenRSAComparisonTest, OpenSSLCanReadOurKeys) {
  // Generate key with our tool
  std::string gen_command = std::string(awslc_executable_path) + " genrsa -out " + out_path_tool;
  int gen_result = system(gen_command.c_str());
  ASSERT_EQ(gen_result, 0) << "AWS-LC key generation failed";
  
  // Verify OpenSSL can read and process our key
  std::string verify_command = std::string(openssl_executable_path) + " rsa -in " + out_path_tool + " -check -noout";
  int verify_result = system(verify_command.c_str());
  ASSERT_EQ(verify_result, 0) << "OpenSSL cannot validate AWS-LC generated key";
}

TEST_F(GenRSAComparisonTest, ArgumentOrderCompatibility) {
  // Test that both tools enforce the same argument order: [options] numbits
  
  // Test correct order (should work for both)
  std::string awslc_correct = std::string(awslc_executable_path) + " genrsa -out " + out_path_tool + " 2048";
  std::string openssl_correct = std::string(openssl_executable_path) + " genrsa -out " + out_path_openssl + " 2048";
  
  int awslc_result = system(awslc_correct.c_str());
  int openssl_result = system(openssl_correct.c_str());
  
  ASSERT_EQ(awslc_result, 0) << "AWS-LC should accept correct argument order";
  ASSERT_EQ(openssl_result, 0) << "OpenSSL should accept correct argument order";
  
  // Clean up for next test
  RemoveFile(out_path_tool);
  RemoveFile(out_path_openssl);
  
  // Test incorrect order - both tools should have matching behavior (both fail)
  std::string awslc_incorrect = std::string(awslc_executable_path) + " genrsa 2048 -out " + out_path_tool;
  std::string openssl_incorrect = std::string(openssl_executable_path) + " genrsa 2048 -out " + out_path_openssl;
  
  int awslc_incorrect_result = system(awslc_incorrect.c_str());
  int openssl_incorrect_result = system(openssl_incorrect.c_str());
  
  // Both tools should have identical behavior for incorrect order
  ASSERT_EQ(awslc_incorrect_result, openssl_incorrect_result) 
    << "AWS-LC and OpenSSL should have matching behavior for incorrect argument order";
}



// ----------------------------- PEM Format Validation Tests -----------------------------

TEST_F(GenRSATest, PEMFormatStructure) {
  std::string command = std::string("./tool-openssl/openssl genrsa -out ") + out_path_tool;
  int result = system(command.c_str());
  ASSERT_EQ(result, 0);
  
  std::string key_content = ReadFileToString(out_path_tool);
  ASSERT_FALSE(key_content.empty());
  
  // Check PEM structure
  ASSERT_TRUE(key_content.find("-----BEGIN RSA PRIVATE KEY-----") != std::string::npos);
  ASSERT_TRUE(key_content.find("-----END RSA PRIVATE KEY-----") != std::string::npos);
  
  // Verify proper ordering
  size_t begin_pos = key_content.find("-----BEGIN RSA PRIVATE KEY-----");
  size_t end_pos = key_content.find("-----END RSA PRIVATE KEY-----");
  ASSERT_LT(begin_pos, end_pos);
  
  // Check for base64 content between markers
  std::string content_between = key_content.substr(
    begin_pos + strlen("-----BEGIN RSA PRIVATE KEY-----"), 
    end_pos - begin_pos - strlen("-----BEGIN RSA PRIVATE KEY-----")
  );
  
  content_between.erase(std::remove_if(content_between.begin(), content_between.end(), ::isspace), content_between.end());
  ASSERT_GT(content_between.length(), 100u);
}

// ----------------------------- RSA Key Component Validation Tests -----------------------------

TEST_F(GenRSATest, KeyComponentsValidation) {
  std::string command = std::string("./tool-openssl/openssl genrsa -out ") + out_path_tool;
  int result = system(command.c_str());
  ASSERT_EQ(result, 0);
  
  std::string key_content = ReadFileToString(out_path_tool);
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(key_content.c_str(), key_content.length()));
  ASSERT_TRUE(bio);
  
  bssl::UniquePtr<RSA> rsa(PEM_read_bio_RSAPrivateKey(bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(rsa);
  
  // Check all key components
  const BIGNUM *n, *e, *d, *p, *q, *dmp1, *dmq1, *iqmp;
  RSA_get0_key(rsa.get(), &n, &e, &d);
  RSA_get0_factors(rsa.get(), &p, &q);
  RSA_get0_crt_params(rsa.get(), &dmp1, &dmq1, &iqmp);
  
  ASSERT_TRUE(n != nullptr);
  ASSERT_TRUE(e != nullptr);
  ASSERT_TRUE(d != nullptr);
  ASSERT_TRUE(p != nullptr);
  ASSERT_TRUE(q != nullptr);
  ASSERT_TRUE(dmp1 != nullptr);
  ASSERT_TRUE(dmq1 != nullptr);
  ASSERT_TRUE(iqmp != nullptr);
  
  // Verify public exponent is RSA_F4 (65537)
  ASSERT_EQ(BN_get_word(e), static_cast<unsigned long>(RSA_F4));
}

TEST_F(GenRSATest, KeyUniqueness) {
  char out_path2[PATH_MAX];
  ASSERT_GT(createTempFILEpath(out_path2), 0u);
  
  std::string command1 = std::string("./tool-openssl/openssl genrsa -out ") + out_path_tool;
  std::string command2 = std::string("./tool-openssl/openssl genrsa -out ") + out_path2;
  
  int result1 = system(command1.c_str());
  int result2 = system(command2.c_str());
  
  ASSERT_EQ(result1, 0);
  ASSERT_EQ(result2, 0);
  
  std::string key1 = ReadFileToString(out_path_tool);
  std::string key2 = ReadFileToString(out_path2);
  
  ASSERT_FALSE(key1.empty());
  ASSERT_FALSE(key2.empty());
  ASSERT_NE(key1, key2);
  
  RemoveFile(out_path2);
}


