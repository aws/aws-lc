// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/pem.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include "internal.h"
#include "test_util.h"
#include "../crypto/test/test_util.h"
#include <cctype>

class PKeyUtlTest : public ::testing::Test {
protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);
    ASSERT_GT(createTempFILEpath(sig_path), 0u);
    ASSERT_GT(createTempFILEpath(key_path), 0u);
    ASSERT_GT(createTempFILEpath(pubkey_path), 0u);
    ASSERT_GT(createTempFILEpath(protected_key_path), 0u);
    
    // Create and save a private key in PEM format
    bssl::UniquePtr<EVP_PKEY> pkey(CreateTestKey(2048));
    ASSERT_TRUE(pkey);
    
    ScopedFILE key_file(fopen(key_path, "wb"));
    ASSERT_TRUE(key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(key_file.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr));
    
    // Create a public key file
    ScopedFILE pubkey_file(fopen(pubkey_path, "wb"));
    ASSERT_TRUE(pubkey_file);
    ASSERT_TRUE(PEM_write_PUBKEY(pubkey_file.get(), pkey.get()));
    
    // Create a password-protected private key
    ScopedFILE protected_key_file(fopen(protected_key_path, "wb"));
    ASSERT_TRUE(protected_key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(protected_key_file.get(), pkey.get(), 
                                     EVP_aes_256_cbc(), 
                                     (unsigned char*)"testpassword", 12,
                                     nullptr, nullptr));
    
    // Create a test input file with some data
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    const char* test_data = "Test data for signing and verification";
    ASSERT_EQ(fwrite(test_data, 1, strlen(test_data), in_file.get()), strlen(test_data));
  }
  
  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(out_path);
    RemoveFile(sig_path);
    RemoveFile(key_path);
    RemoveFile(pubkey_path);
    RemoveFile(protected_key_path);
  }
  
  char in_path[PATH_MAX];
  char out_path[PATH_MAX];
  char sig_path[PATH_MAX];
  char key_path[PATH_MAX];
  char pubkey_path[PATH_MAX];
  char protected_key_path[PATH_MAX];
};

// ----------------------------- PKeyUtl Option Tests -----------------------------

// Test basic signing operation
TEST_F(PKeyUtlTest, SignTest) {
  args_list_t args = {"-sign", "-inkey", key_path, "-in", in_path, "-out", out_path};
  bool result = pkeyutlTool(args);
  ASSERT_TRUE(result);
  
  // Verify the signature file was created and has content
  struct stat st;
  ASSERT_EQ(stat(out_path, &st), 0);
  ASSERT_GT(st.st_size, 0);
}

// Test basic verification operation
TEST_F(PKeyUtlTest, VerifyTest) {
  // First sign the data
  {
    args_list_t args = {"-sign", "-inkey", key_path, "-in", in_path, "-out", sig_path};
    bool result = pkeyutlTool(args);
    ASSERT_TRUE(result);
  }
  
  // Then verify the signature
  {
    args_list_t args = {"-verify", "-pubin", "-inkey", pubkey_path, "-in", in_path, 
                        "-sigfile", sig_path, "-out", out_path};
    bool result = pkeyutlTool(args);
    ASSERT_TRUE(result);
    
    // Check that the output contains "Signature Verified Successfully"
    std::string output = ReadFileToString(out_path);
    ASSERT_NE(output.find("Signature Verified Successfully"), std::string::npos);
  }
}

// Test basic passin integration with password-protected key
TEST_F(PKeyUtlTest, PassinBasicIntegrationTest) {
  args_list_t args = {"-sign", "-inkey", protected_key_path, "-passin", "pass:testpassword", "-in", in_path, "-out", out_path};
  bool result = pkeyutlTool(args);
  ASSERT_TRUE(result);
  
  struct stat st;
  ASSERT_EQ(stat(out_path, &st), 0);
  ASSERT_GT(st.st_size, 0);
}

// Test that pass_util errors are properly propagated 
TEST_F(PKeyUtlTest, PassinErrorHandlingTest) {
  args_list_t args = {"-sign", "-inkey", protected_key_path, "-passin", "invalid:format", "-in", in_path, "-out", out_path};
  bool result = pkeyutlTool(args);
  ASSERT_FALSE(result);
  
  args_list_t args2 = {"-sign", "-inkey", protected_key_path, "-passin", "pass:wrongpassword", "-in", in_path, "-out", out_path};
  bool result2 = pkeyutlTool(args2);
  ASSERT_FALSE(result2);
}

// Test that unprotected key works without passin
TEST_F(PKeyUtlTest, NoPassinRequiredTest) {
  args_list_t args = {"-sign", "-inkey", key_path, "-in", in_path, "-out", out_path};
  bool result = pkeyutlTool(args);
  ASSERT_TRUE(result);
  
  // Verify the signature file was created and has content
  struct stat st;
  ASSERT_EQ(stat(out_path, &st), 0);
  ASSERT_GT(st.st_size, 0);
}

// -------------------- PKeyUtl Option Usage Error Tests --------------------------

class PKeyUtlOptionUsageErrorsTest : public PKeyUtlTest {
protected:
  void TestOptionUsageErrors(const std::vector<std::string>& args) {
    args_list_t c_args;
    for (const auto& arg : args) {
      c_args.push_back(arg.c_str());
    }
    bool result = pkeyutlTool(c_args);
    ASSERT_FALSE(result);
  }
};

// Test invalid option combinations
TEST_F(PKeyUtlOptionUsageErrorsTest, InvalidOptionCombinationsTest) {
  std::vector<std::vector<std::string>> testparams = {
    // Both sign and verify specified
    {"-sign", "-verify", "-inkey", key_path, "-in", in_path},
    // Missing inkey
    {"-sign", "-in", in_path},
    // Verify without sigfile
    {"-verify", "-inkey", key_path, "-in", in_path},
    // Sigfile with sign operation
    {"-sign", "-inkey", key_path, "-in", in_path, "-sigfile", sig_path},
  };
  
  for (const auto& args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// -------------------- PKeyUtl OpenSSL Comparison Tests --------------------------

// Comparison tests cannot run without set up of environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.

class PKeyUtlComparisonTest : public ::testing::Test {
protected:
  void SetUp() override {
    // Skip gtests if env variables not set
    tool_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
    if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
      GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH environment variables are not set";
    }

    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);
    ASSERT_GT(createTempFILEpath(sig_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(sig_path_openssl), 0u);
    ASSERT_GT(createTempFILEpath(key_path), 0u);
    ASSERT_GT(createTempFILEpath(pubkey_path), 0u);
    
    // Create and save a private key
    pkey.reset(CreateTestKey(2048));
    ASSERT_TRUE(pkey);
    
    ScopedFILE key_file(fopen(key_path, "wb"));
    ASSERT_TRUE(key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(key_file.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr));
    
    // Create a public key file
    ScopedFILE pubkey_file(fopen(pubkey_path, "wb"));
    ASSERT_TRUE(pubkey_file);
    ASSERT_TRUE(PEM_write_PUBKEY(pubkey_file.get(), pkey.get()));
    
    // Create a test input file with some data
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    const char* test_data = "Test data for signing and verification";
    ASSERT_EQ(fwrite(test_data, 1, strlen(test_data), in_file.get()), strlen(test_data));
  }
  
  void TearDown() override {
    if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
      RemoveFile(in_path);
      RemoveFile(out_path_tool);
      RemoveFile(out_path_openssl);
      RemoveFile(sig_path_tool);
      RemoveFile(sig_path_openssl);
      RemoveFile(key_path);
      RemoveFile(pubkey_path);
    }
  }
  
  char in_path[PATH_MAX];
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  char sig_path_tool[PATH_MAX];
  char sig_path_openssl[PATH_MAX];
  char key_path[PATH_MAX];
  char pubkey_path[PATH_MAX];
  bssl::UniquePtr<EVP_PKEY> pkey;
  const char* tool_executable_path;
  const char* openssl_executable_path;
  std::string tool_output_str;
  std::string openssl_output_str;
};

// Test signing operation against OpenSSL
TEST_F(PKeyUtlComparisonTest, SignCompareOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " pkeyutl -sign -inkey " + 
                             key_path + " -in " + in_path + " -out " + sig_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " pkeyutl -sign -inkey " + 
                                key_path + " -in " + in_path + " -out " + sig_path_openssl;

  int tool_result = system(tool_command.c_str());
  ASSERT_EQ(tool_result, 0) << "AWS-LC tool command failed: " << tool_command;

  int openssl_result = system(openssl_command.c_str());
  ASSERT_EQ(openssl_result, 0) << "OpenSSL command failed: " << openssl_command;

  // Verify both signatures with the public key
  std::string tool_verify_cmd = std::string(tool_executable_path) + " pkeyutl -verify -pubin -inkey " + 
                                pubkey_path + " -in " + in_path + " -sigfile " + sig_path_tool + 
                                " > " + out_path_tool;
  std::string openssl_verify_cmd = std::string(openssl_executable_path) + " pkeyutl -verify -pubin -inkey " + 
                                   pubkey_path + " -in " + in_path + " -sigfile " + sig_path_openssl + 
                                   " > " + out_path_openssl;

  ASSERT_EQ(system(tool_verify_cmd.c_str()), 0);
  ASSERT_EQ(system(openssl_verify_cmd.c_str()), 0);

  // Read verification results
  std::ifstream tool_output(out_path_tool);
  tool_output_str = std::string((std::istreambuf_iterator<char>(tool_output)), std::istreambuf_iterator<char>());
  std::ifstream openssl_output(out_path_openssl);
  openssl_output_str = std::string((std::istreambuf_iterator<char>(openssl_output)), std::istreambuf_iterator<char>());

  // Both should verify successfully
  ASSERT_NE(tool_output_str.find("Signature Verified Successfully"), std::string::npos);
  ASSERT_NE(openssl_output_str.find("Signature Verified Successfully"), std::string::npos);
}
