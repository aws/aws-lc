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

// Helper function to create a test key
EVP_PKEY* CreateTestKey(int key_bits) {
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  if (!pkey) {
    return nullptr;
  }
  
  bssl::UniquePtr<RSA> rsa(RSA_new());
  bssl::UniquePtr<BIGNUM> bn(BN_new());
  if (!bn || !BN_set_word(bn.get(), RSA_F4) ||
      !RSA_generate_key_ex(rsa.get(), key_bits, bn.get(), nullptr) ||
      !EVP_PKEY_assign_RSA(pkey.get(), rsa.release())) {
    return nullptr;
  }
  
  return pkey.release();
}

class PKeyTest : public ::testing::Test {
protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);
    ASSERT_GT(createTempFILEpath(der_key_path), 0u);
    
    // Create and save a private key in PEM format
    bssl::UniquePtr<EVP_PKEY> pkey(CreateTestKey(2048));
    ASSERT_TRUE(pkey);
    
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_PrivateKey(in_file.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr));
    
    // Create a DER format key
    ScopedFILE der_file(fopen(der_key_path, "wb"));
    ASSERT_TRUE(der_file);
    ASSERT_TRUE(i2d_PrivateKey_fp(der_file.get(), pkey.get()));
  }
  
  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(out_path);
    RemoveFile(der_key_path);
  }
  
  char in_path[PATH_MAX];
  char out_path[PATH_MAX];
  char der_key_path[PATH_MAX];
};

// ----------------------------- PKey Option Tests -----------------------------

// Test -in and -out
TEST_F(PKeyTest, PKeyToolInOutTest) {
  args_list_t args = {"-in", in_path, "-out", out_path};
  bool result = pkeyTool(args);
  ASSERT_TRUE(result);
  {
    ScopedFILE out_file(fopen(out_path, "rb"));
    ASSERT_TRUE(out_file);
    bssl::UniquePtr<EVP_PKEY> parsed_pkey(PEM_read_PrivateKey(out_file.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(parsed_pkey);
  }
}

// Test -inform DER
TEST_F(PKeyTest, PKeyToolInformDERTest) {
  args_list_t args = {"-in", der_key_path, "-inform", "DER", "-out", out_path};
  bool result = pkeyTool(args);
  ASSERT_TRUE(result);
  {
    ScopedFILE out_file(fopen(out_path, "rb"));
    ASSERT_TRUE(out_file);
    bssl::UniquePtr<EVP_PKEY> parsed_pkey(PEM_read_PrivateKey(out_file.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(parsed_pkey);
  }
}

// Test -outform DER
TEST_F(PKeyTest, PKeyToolOutformDERTest) {
  args_list_t args = {"-in", in_path, "-outform", "DER", "-out", out_path};
  bool result = pkeyTool(args);
  ASSERT_TRUE(result);
  {
    ScopedFILE out_file(fopen(out_path, "rb"));
    ASSERT_TRUE(out_file);
    bssl::UniquePtr<EVP_PKEY> parsed_pkey(d2i_PrivateKey_fp(out_file.get(), nullptr));
    ASSERT_TRUE(parsed_pkey);
  }
}

// Test -pubout
TEST_F(PKeyTest, PKeyToolPuboutTest) {
  args_list_t args = {"-in", in_path, "-pubout", "-out", out_path};
  bool result = pkeyTool(args);
  ASSERT_TRUE(result);
  {
    ScopedFILE out_file(fopen(out_path, "rb"));
    ASSERT_TRUE(out_file);
    bssl::UniquePtr<EVP_PKEY> parsed_pkey(PEM_read_PUBKEY(out_file.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(parsed_pkey);
  }
}

// Test -pubin
TEST_F(PKeyTest, PKeyToolPubinTest) {
  // First create a public key file
  {
    args_list_t args = {"-in", in_path, "-pubout", "-out", out_path};
    bool result = pkeyTool(args);
    ASSERT_TRUE(result);
  }
  
  // Then test reading it with -pubin
  {
    char temp_out[PATH_MAX];
    ASSERT_GT(createTempFILEpath(temp_out), 0u);
    
    args_list_t args = {"-in", out_path, "-pubin", "-out", temp_out};
    bool result = pkeyTool(args);
    ASSERT_TRUE(result);
    
    ScopedFILE out_file(fopen(temp_out, "rb"));
    ASSERT_TRUE(out_file);
    bssl::UniquePtr<EVP_PKEY> parsed_pkey(PEM_read_PUBKEY(out_file.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(parsed_pkey);
    
    RemoveFile(temp_out);
  }
}

// Test -text
TEST_F(PKeyTest, PKeyToolTextTest) {
  args_list_t args = {"-in", in_path, "-text", "-noout"};
  bool result = pkeyTool(args);
  ASSERT_TRUE(result);
}

// Test -text_pub
TEST_F(PKeyTest, PKeyToolTextPubTest) {
  args_list_t args = {"-in", in_path, "-text_pub", "-noout"};
  bool result = pkeyTool(args);
  ASSERT_TRUE(result);
}

// -------------------- PKey Option Usage Error Tests --------------------------

class PKeyOptionUsageErrorsTest : public PKeyTest {
protected:
  void TestOptionUsageErrors(const std::vector<std::string>& args) {
    args_list_t c_args;
    for (const auto& arg : args) {
      c_args.push_back(arg.c_str());
    }
    bool result = pkeyTool(c_args);
    ASSERT_FALSE(result);
  }
};

// Test invalid format options
TEST_F(PKeyOptionUsageErrorsTest, InvalidFormatOptionsTest) {
  std::vector<std::vector<std::string>> testparams = {
    {"-in", in_path, "-inform", "INVALID"},
    {"-in", in_path, "-outform", "INVALID"},
  };
  for (const auto& args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// -------------------- PKey OpenSSL Comparison Tests --------------------------

// Comparison tests cannot run without set up of environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.

class PKeyComparisonTest : public ::testing::Test {
protected:
  // Helper method to normalize key headers by removing algorithm prefixes
  // (e.g., "RSA Private-Key:" -> "Private-Key:")
  void normalizeKeyHeader(std::string& str, const std::string& keyType) {
    size_t pos = str.find(keyType + "-Key:");
    if (pos != std::string::npos && pos > 0) {
      size_t prefixStart = 0; 
      str.erase(prefixStart, pos - prefixStart);
    }
  }

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
    ASSERT_GT(createTempFILEpath(der_key_path), 0u);
    
    // Create and save a private key
    pkey.reset(CreateTestKey(2048));
    ASSERT_TRUE(pkey);
    
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_PrivateKey(in_file.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr));
    
    // Create a DER format key
    ScopedFILE der_file(fopen(der_key_path, "wb"));
    ASSERT_TRUE(der_file);
    ASSERT_TRUE(i2d_PrivateKey_fp(der_file.get(), pkey.get()));
  }
  
  void TearDown() override {
    if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
      RemoveFile(in_path);
      RemoveFile(out_path_tool);
      RemoveFile(out_path_openssl);
      RemoveFile(der_key_path);
    }
  }
  
  char in_path[PATH_MAX];
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  char der_key_path[PATH_MAX];
  bssl::UniquePtr<EVP_PKEY> pkey;
  const char* tool_executable_path;
  const char* openssl_executable_path;
  std::string tool_output_str;
  std::string openssl_output_str;
};

// Test against OpenSSL output "openssl pkey -in file -text -noout"
TEST_F(PKeyComparisonTest, PKeyToolCompareTextOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " pkey -in " + in_path + " -text -noout > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " pkey -in " + in_path + " -text -noout > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // OpenSSL versions may have slight formatting differences, so we remove whitespace for comparison
  tool_output_str.erase(remove_if(tool_output_str.begin(), tool_output_str.end(), isspace), tool_output_str.end());
  openssl_output_str.erase(remove_if(openssl_output_str.begin(), openssl_output_str.end(), isspace), openssl_output_str.end());

  // Normalize algorithm prefixes before "Private-Key:"
  normalizeKeyHeader(tool_output_str, "Private");
  normalizeKeyHeader(openssl_output_str, "Private");

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl pkey -in file -text_pub -noout"
TEST_F(PKeyComparisonTest, PKeyToolCompareTextPubOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " pkey -in " + in_path + " -text_pub -noout > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " pkey -in " + in_path + " -text_pub -noout > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // OpenSSL versions may have slight formatting differences, so we remove whitespace for comparison
  tool_output_str.erase(remove_if(tool_output_str.begin(), tool_output_str.end(), isspace), tool_output_str.end());
  openssl_output_str.erase(remove_if(openssl_output_str.begin(), openssl_output_str.end(), isspace), openssl_output_str.end());

  // Normalize algorithm prefixes before "Public-Key:"
  normalizeKeyHeader(tool_output_str, "Public");
  normalizeKeyHeader(openssl_output_str, "Public");

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl pkey -in file -pubout"
TEST_F(PKeyComparisonTest, PKeyToolComparePuboutOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " pkey -in " + in_path + " -pubout > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " pkey -in " + in_path + " -pubout > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Check that both outputs contain the public key header
  const std::string PUB_KEY_BEGIN = "-----BEGIN PUBLIC KEY-----";
  const std::string PUB_KEY_END = "-----END PUBLIC KEY-----";
  
  ASSERT_NE(tool_output_str.find(PUB_KEY_BEGIN), std::string::npos);
  ASSERT_NE(tool_output_str.find(PUB_KEY_END), std::string::npos);
  ASSERT_NE(openssl_output_str.find(PUB_KEY_BEGIN), std::string::npos);
  ASSERT_NE(openssl_output_str.find(PUB_KEY_END), std::string::npos);
}

// Test against OpenSSL output "openssl pkey -in file -inform DER"
TEST_F(PKeyComparisonTest, PKeyToolCompareInformDEROpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " pkey -in " + der_key_path + " -inform DER > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " pkey -in " + der_key_path + " -inform DER > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Check that both outputs contain the private key header
  const std::string PRIV_KEY_BEGIN = "-----BEGIN PRIVATE KEY-----";
  const std::string PRIV_KEY_END = "-----END PRIVATE KEY-----";
  
  ASSERT_NE(tool_output_str.find(PRIV_KEY_BEGIN), std::string::npos);
  ASSERT_NE(tool_output_str.find(PRIV_KEY_END), std::string::npos);
  ASSERT_NE(openssl_output_str.find(PRIV_KEY_BEGIN), std::string::npos);
  ASSERT_NE(openssl_output_str.find(PRIV_KEY_END), std::string::npos);
}

// Test against OpenSSL output "openssl pkey -in file -outform DER"
TEST_F(PKeyComparisonTest, PKeyToolCompareOutformDEROpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " pkey -in " + in_path + " -outform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " pkey -in " + in_path + " -outform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl pkey -in file -pubin -pubout"
TEST_F(PKeyComparisonTest, PKeyToolComparePubinPuboutOpenSSL) {
  // First create a public key file
  std::string create_pubkey_cmd = std::string(tool_executable_path) + " pkey -in " + in_path + " -pubout -out " + out_path_tool;
  ASSERT_EQ(system(create_pubkey_cmd.c_str()), 0);
  
  // Then test reading it with -pubin
  std::string tool_command = std::string(tool_executable_path) + " pkey -in " + out_path_tool + " -pubin > " + out_path_tool + ".new";
  std::string openssl_command = std::string(openssl_executable_path) + " pkey -in " + out_path_tool + " -pubin > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, (std::string(out_path_tool) + ".new").c_str(), out_path_openssl, tool_output_str, openssl_output_str);

  // Check that both outputs contain the public key header
  const std::string PUB_KEY_BEGIN = "-----BEGIN PUBLIC KEY-----";
  const std::string PUB_KEY_END = "-----END PUBLIC KEY-----";
  
  ASSERT_NE(tool_output_str.find(PUB_KEY_BEGIN), std::string::npos);
  ASSERT_NE(tool_output_str.find(PUB_KEY_END), std::string::npos);
  ASSERT_NE(openssl_output_str.find(PUB_KEY_BEGIN), std::string::npos);
  ASSERT_NE(openssl_output_str.find(PUB_KEY_END), std::string::npos);
  
  // Clean up the extra file
  RemoveFile((std::string(out_path_tool) + ".new").c_str());
}

// Test against OpenSSL output reading from stdin "cat file | openssl pkey"
TEST_F(PKeyComparisonTest, PKeyToolCompareStdinOpenSSL) {
  std::string tool_command = "cat " + std::string(in_path) + " | " + std::string(tool_executable_path) + " pkey > " + out_path_tool;
  std::string openssl_command = "cat " + std::string(in_path) + " | " + std::string(openssl_executable_path) + " pkey > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Check that both outputs contain the private key header
  const std::string PRIV_KEY_BEGIN = "-----BEGIN PRIVATE KEY-----";
  const std::string PRIV_KEY_END = "-----END PRIVATE KEY-----";
  
  ASSERT_NE(tool_output_str.find(PRIV_KEY_BEGIN), std::string::npos);
  ASSERT_NE(tool_output_str.find(PRIV_KEY_END), std::string::npos);
  ASSERT_NE(openssl_output_str.find(PRIV_KEY_BEGIN), std::string::npos);
  ASSERT_NE(openssl_output_str.find(PRIV_KEY_END), std::string::npos);
}
