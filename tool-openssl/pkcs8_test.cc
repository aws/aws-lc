// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "openssl/pkcs8.h"
#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "internal.h"
#include "test_util.h"
#include "../crypto/test/test_util.h"

bool CheckPKCS8Boundaries(const std::string &content, const std::string &begin1, const std::string &end1, 
                     const std::string &begin2, const std::string &end2);

// Helper function to create a test RSA key for the PKCS8 tests
static EVP_PKEY* CreateTestKey() {
  bssl::UniquePtr<BIGNUM> bn(BN_new());
  if (!bn || !BN_set_word(bn.get(), RSA_F4)) {
    return nullptr;
  }
  bssl::UniquePtr<RSA> rsa(RSA_new());
  if (!rsa || !RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr)) {
    return nullptr;
  }
  
  EVP_PKEY *pkey = EVP_PKEY_new();
  if (!pkey || !EVP_PKEY_assign_RSA(pkey, rsa.release())) {
    EVP_PKEY_free(pkey);
    return nullptr;
  }
  return pkey;
}

class PKCS8Test : public ::testing::Test {
protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);
    ASSERT_GT(createTempFILEpath(pass_path), 0u);

    key.reset(CreateTestKey());
    ASSERT_TRUE(key);

    // Use BIO for writing the key to input file
    ScopedBIO in_bio(in_path, "wb");
    ASSERT_TRUE(in_bio.valid());
    ASSERT_TRUE(PEM_write_bio_PrivateKey(in_bio.get(), key.get(), nullptr, nullptr, 0, nullptr, nullptr));
    
    // Make sure password is just "testpassword" without any extra characters
    ScopedBIO pass_bio(pass_path, "wb");
    ASSERT_TRUE(pass_bio.valid());
    ASSERT_TRUE(BIO_printf(pass_bio.get(), "testpassword") > 0);
  }
  
  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(out_path);
    RemoveFile(pass_path);
  }
  
  char in_path[PATH_MAX];
  char out_path[PATH_MAX];
  char pass_path[PATH_MAX];
  bssl::UniquePtr<EVP_PKEY> key;
};

// ----------------------------- PKCS8 Option Tests -----------------------------

// Test -in, -out, -topk8, and -nocrypt
TEST_F(PKCS8Test, PKCS8ToolBasicTest) {
  args_list_t args = {"-in", in_path, "-out", out_path, "-topk8", "-nocrypt"};
  bool result = pkcs8Tool(args);
  ASSERT_TRUE(result);
  {
    ScopedBIO out_bio(out_path, "rb");
    ASSERT_TRUE(out_bio.valid());
    bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(PEM_read_bio_PKCS8_PRIV_KEY_INFO(out_bio.get(), nullptr, nullptr, nullptr));
    bssl::UniquePtr<EVP_PKEY> parsed_key(EVP_PKCS82PKEY(p8inf.get()));
    ASSERT_TRUE(parsed_key);
  }
}

// Test -inform and -outform
TEST_F(PKCS8Test, PKCS8ToolFormatTest) {
  args_list_t args = {"-in", in_path, "-out", out_path, "-topk8", "-nocrypt", "-inform", "PEM", "-outform", "PEM"};
  bool result = pkcs8Tool(args);
  ASSERT_TRUE(result);
}

// Test -v2 with aes-256-cbc and -passout
TEST_F(PKCS8Test, PKCS8ToolEncryptionTest) {
  std::string passout = std::string("file:") + pass_path;
  args_list_t args = {"-in", in_path, "-out", out_path, "-topk8", "-v2", "aes-256-cbc", "-passout", passout.c_str()};
  bool result = pkcs8Tool(args);
  ASSERT_TRUE(result);
}

// Test -v2 option with the default cipher (aes-256-cbc)
TEST_F(PKCS8Test, PKCS8ToolV2DefaultTest) {
  // First verify the password file content is correct
  ScopedBIO test_bio(pass_path, "r");
  ASSERT_TRUE(test_bio.valid());
  char password_buffer[100] = {0};
  ASSERT_GT(BIO_gets(test_bio.get(), password_buffer, sizeof(password_buffer)), 0);
  ASSERT_STREQ(password_buffer, "testpassword");
  
  std::string passout = std::string("pass:testpassword");  // Use direct password instead of file
  args_list_t args = {"-in", in_path, "-out", out_path, "-topk8", "-v2", "aes-256-cbc", "-passout", passout.c_str()};
  bool result = pkcs8Tool(args);
  ASSERT_TRUE(result);
  
  // Verify the output is an encrypted PKCS8 file
  std::string content = ReadFileToString(out_path);
  ASSERT_FALSE(content.empty());
  ASSERT_TRUE(content.find("-----BEGIN ENCRYPTED PRIVATE KEY-----") != std::string::npos);
}

// Test -v2prf with hmacWithSHA1 (only supported PRF in AWS-LC)
TEST_F(PKCS8Test, PKCS8ToolPRFTest) {
  std::string passout = std::string("file:") + pass_path;
  args_list_t args = {"-in", in_path, "-out", out_path, "-topk8", "-v2", "aes-256-cbc", "-v2prf", "hmacWithSHA1", "-passout", passout.c_str()};
  bool result = pkcs8Tool(args);
  ASSERT_TRUE(result);
}

// Test that unsupported PRF algorithms are rejected
TEST_F(PKCS8Test, PKCS8ToolUnsupportedPRFTest) {
  std::string passout = std::string("file:") + pass_path;
  args_list_t args = {"-in", in_path, "-out", out_path, "-topk8", "-v2", "aes-256-cbc", "-v2prf", "hmacWithSHA256", "-passout", passout.c_str()};
  bool result = pkcs8Tool(args);
  ASSERT_FALSE(result);
}

// -------------------- PKCS8 Option Usage Error Tests --------------------------

class PKCS8OptionUsageErrorsTest : public PKCS8Test {
protected:
  void TestOptionUsageErrors(const std::vector<std::string>& args) {
    args_list_t c_args;
    for (const auto& arg : args) {
      c_args.push_back(arg.c_str());
    }
    bool result = pkcs8Tool(c_args);
    ASSERT_FALSE(result);
  }
};

// Test missing -in required option
TEST_F(PKCS8OptionUsageErrorsTest, RequiredOptionTests) {
  std::vector<std::vector<std::string>> testparams = {
    {"-out", "output.pem", "-topk8"},
    {"-topk8", "-nocrypt"},
  };
  for (const auto& args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// Test invalid format
TEST_F(PKCS8OptionUsageErrorsTest, InvalidFormatTest) {
  std::vector<std::vector<std::string>> testparams = {
    {"-in", in_path, "-inform", "INVALID"},
    {"-in", in_path, "-outform", "INVALID"},
  };
  for (const auto& args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// -------------------- PKCS8 OpenSSL Comparison Tests --------------------------

// Comparison tests cannot run without set up of environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.

class PKCS8ComparisonTest : public ::testing::Test {
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
    ASSERT_GT(createTempFILEpath(pass_path), 0u);
    ASSERT_GT(createTempFILEpath(decrypt_path), 0u);

    key.reset(CreateTestKey());
    ASSERT_TRUE(key);

    ScopedBIO in_bio(in_path, "wb");
    ASSERT_TRUE(in_bio.valid());
    ASSERT_TRUE(PEM_write_bio_PrivateKey(in_bio.get(), key.get(), nullptr, nullptr, 0, nullptr, nullptr));
    
    ScopedBIO pass_bio(pass_path, "wb");
    ASSERT_TRUE(pass_bio.valid());
    ASSERT_TRUE(BIO_printf(pass_bio.get(), "testpassword") > 0);
  }

  void TearDown() override {
    if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
      RemoveFile(in_path);
      RemoveFile(out_path_tool);
      RemoveFile(out_path_openssl);
      RemoveFile(pass_path);
      RemoveFile(decrypt_path);
    }
  }

  char in_path[PATH_MAX];
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  char pass_path[PATH_MAX];
  char decrypt_path[PATH_MAX];
  bssl::UniquePtr<EVP_PKEY> key;
  const char* tool_executable_path;
  const char* openssl_executable_path;
  std::string tool_output_str;
  std::string openssl_output_str;
};

// PKCS8 boundaries
const std::string PKCS8_BEGIN = "-----BEGIN PRIVATE KEY-----";
const std::string PKCS8_END = "-----END PRIVATE KEY-----";
const std::string ENC_PKCS8_BEGIN = "-----BEGIN ENCRYPTED PRIVATE KEY-----";
const std::string ENC_PKCS8_END = "-----END ENCRYPTED PRIVATE KEY-----";

// Check if the content has the expected boundaries
bool CheckPKCS8Boundaries(const std::string &content, const std::string &begin1, const std::string &end1, 
                     const std::string &begin2, const std::string &end2) {
  return (content.compare(0, begin1.size(), begin1) == 0 && 
          content.compare(content.size() - end1.size(), end1.size(), end1) == 0) ||
         (content.compare(0, begin2.size(), begin2) == 0 && 
          content.compare(content.size() - end2.size(), end2.size(), end2) == 0);
}


// Test against OpenSSL output "openssl pkcs8 -topk8 -nocrypt -in file -out file"
TEST_F(PKCS8ComparisonTest, PKCS8ToolCompareUnencryptedOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " pkcs8 -topk8 -nocrypt -in " + in_path + " -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " pkcs8 -topk8 -nocrypt -in " + in_path + " -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  trim(tool_output_str);
  trim(openssl_output_str);
  
  ASSERT_TRUE(CheckPKCS8Boundaries(tool_output_str, PKCS8_BEGIN, PKCS8_END, PKCS8_BEGIN, PKCS8_END));
  ASSERT_TRUE(CheckPKCS8Boundaries(openssl_output_str, PKCS8_BEGIN, PKCS8_END, PKCS8_BEGIN, PKCS8_END));
}

// Test cross-compatibility: AWS-LC encrypts, OpenSSL decrypts
TEST_F(PKCS8ComparisonTest, PKCS8ToolCrossCompat_AWSLC_To_OpenSSL) {
  // Step 1: Use AWS-LC to encrypt the private key
  std::string encrypt_command = std::string(tool_executable_path) + " pkcs8 -topk8 -v2 aes-256-cbc -in " + in_path + 
                             " -out " + out_path_tool + " -passout file:" + pass_path;
  
  int result = system(encrypt_command.c_str());
  ASSERT_EQ(0, result) << "AWS-LC encryption command failed";
  
  // Verify AWS-LC output has correct PKCS8 boundaries
  tool_output_str = ReadFileToString(out_path_tool);
  ASSERT_FALSE(tool_output_str.empty());
  trim(tool_output_str);
  std::cout << "AWS-LC output content:" << std::endl << tool_output_str << std::endl;
  ASSERT_TRUE(CheckPKCS8Boundaries(tool_output_str, ENC_PKCS8_BEGIN, ENC_PKCS8_END, ENC_PKCS8_BEGIN, ENC_PKCS8_END));
  
  // Step 2: Use OpenSSL to decrypt the AWS-LC encrypted file
  std::string decrypt_command = std::string(openssl_executable_path) + " pkcs8 -in " + out_path_tool + 
                             " -out " + decrypt_path + " -passin file:" + pass_path;
  
  result = system(decrypt_command.c_str());
  ASSERT_EQ(0, result) << "OpenSSL decryption of AWS-LC output failed";
  
  // Step 3: Load decrypted key and compare with original
  bssl::UniquePtr<EVP_PKEY> decrypted_key(DecryptPrivateKey(decrypt_path, nullptr));
  ASSERT_TRUE(decrypted_key) << "Failed to load decrypted key";
  
  // Step 4: Compare with original key
  ASSERT_TRUE(CompareKeys(key.get(), decrypted_key.get())) << "Decrypted key doesn't match original";
}

// Test cross-compatibility: OpenSSL encrypts, AWS-LC decrypts
TEST_F(PKCS8ComparisonTest, PKCS8ToolCrossCompat_OpenSSL_To_AWSLC) {
  // Step 1: Use OpenSSL to encrypt the private key
  std::string encrypt_command = std::string(openssl_executable_path) + " pkcs8 -topk8 -v2 aes-256-cbc -in " + in_path + 
                             " -out " + out_path_openssl + " -passout file:" + pass_path;
  
  int result = system(encrypt_command.c_str());
  ASSERT_EQ(0, result) << "OpenSSL encryption command failed";
  
  // Verify OpenSSL output has correct PKCS8 boundaries
  openssl_output_str = ReadFileToString(out_path_openssl);
  ASSERT_FALSE(openssl_output_str.empty());
  trim(openssl_output_str);
  std::cout << "OpenSSL output content:" << std::endl << openssl_output_str << std::endl;
  ASSERT_TRUE(CheckPKCS8Boundaries(openssl_output_str, ENC_PKCS8_BEGIN, ENC_PKCS8_END, ENC_PKCS8_BEGIN, ENC_PKCS8_END));
  
  // Step 2: Use AWS-LC to decrypt the OpenSSL encrypted file
  std::string decrypt_command = std::string(tool_executable_path) + " pkcs8 -in " + out_path_openssl + 
                             " -out " + decrypt_path + " -passin file:" + pass_path;
  
  result = system(decrypt_command.c_str());
  ASSERT_EQ(0, result) << "AWS-LC decryption of OpenSSL output failed";
  
  // Step 3: Load decrypted key and compare with original
  bssl::UniquePtr<EVP_PKEY> decrypted_key(DecryptPrivateKey(decrypt_path, nullptr));
  ASSERT_TRUE(decrypted_key) << "Failed to load decrypted key";
  
  // Step 4: Compare with original key
  ASSERT_TRUE(CompareKeys(key.get(), decrypted_key.get())) << "Decrypted key doesn't match original";
}

// Original format comparison test kept for backward compatibility
TEST_F(PKCS8ComparisonTest, PKCS8ToolCompareEncryptedOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " pkcs8 -topk8 -v2 aes-256-cbc -in " + in_path + 
                             " -out " + out_path_tool + " -passout file:" + pass_path;
  std::string openssl_command = std::string(openssl_executable_path) + " pkcs8 -topk8 -v2 aes-256-cbc -in " + in_path + 
                                " -out " + out_path_openssl + " -passout file:" + pass_path;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  trim(tool_output_str);
  trim(openssl_output_str);
  
  // Verify both outputs have correct format
  ASSERT_TRUE(CheckPKCS8Boundaries(tool_output_str, ENC_PKCS8_BEGIN, ENC_PKCS8_END, ENC_PKCS8_BEGIN, ENC_PKCS8_END));
  ASSERT_TRUE(CheckPKCS8Boundaries(openssl_output_str, ENC_PKCS8_BEGIN, ENC_PKCS8_END, ENC_PKCS8_BEGIN, ENC_PKCS8_END));
  
  // Decrypt both outputs and verify they match the original key
  bssl::UniquePtr<EVP_PKEY> aws_lc_decrypted(DecryptPrivateKey(out_path_tool, "testpassword"));
  bssl::UniquePtr<EVP_PKEY> openssl_decrypted(DecryptPrivateKey(out_path_openssl, "testpassword"));
  
  ASSERT_TRUE(aws_lc_decrypted) << "Failed to decrypt AWS-LC output";
  ASSERT_TRUE(openssl_decrypted) << "Failed to decrypt OpenSSL output";
  
  ASSERT_TRUE(CompareKeys(key.get(), aws_lc_decrypted.get())) << "AWS-LC encrypted key doesn't match original after decryption";
  ASSERT_TRUE(CompareKeys(key.get(), openssl_decrypted.get())) << "OpenSSL encrypted key doesn't match original after decryption";
}

// Test against OpenSSL output with DER format
TEST_F(PKCS8ComparisonTest, PKCS8ToolCompareDERFormatOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " pkcs8 -topk8 -nocrypt -in " + in_path + 
                             " -outform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " pkcs8 -topk8 -nocrypt -in " + in_path + 
                                " -outform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);
}

// Test cross-compatibility with PRF: AWS-LC encrypts with hmacWithSHA1 PRF, OpenSSL decrypts
TEST_F(PKCS8ComparisonTest, PKCS8ToolCrossCompat_AWSLC_To_OpenSSL_WithPRF) {
  // Step 1: Use AWS-LC to encrypt the private key with custom PRF
  std::string encrypt_command = std::string(tool_executable_path) + " pkcs8 -topk8 -v2 aes-256-cbc -v2prf hmacWithSHA1 -in " + 
                             in_path + " -out " + out_path_tool + " -passout file:" + pass_path;
  
  int result = system(encrypt_command.c_str());
  ASSERT_EQ(0, result) << "AWS-LC encryption command with PRF failed";
  
  // Verify AWS-LC output has correct PKCS8 boundaries
  tool_output_str = ReadFileToString(out_path_tool);
  ASSERT_FALSE(tool_output_str.empty());
  trim(tool_output_str);
  std::cout << "AWS-LC output content (with PRF):" << std::endl << tool_output_str << std::endl;
  ASSERT_TRUE(CheckPKCS8Boundaries(tool_output_str, ENC_PKCS8_BEGIN, ENC_PKCS8_END, ENC_PKCS8_BEGIN, ENC_PKCS8_END));
  
  // Step 2: Use OpenSSL to decrypt the AWS-LC encrypted file
  std::string decrypt_command = std::string(openssl_executable_path) + " pkcs8 -in " + out_path_tool + 
                             " -out " + decrypt_path + " -passin file:" + pass_path;
  
  result = system(decrypt_command.c_str());
  ASSERT_EQ(0, result) << "OpenSSL decryption of AWS-LC output with PRF failed";
  
  // Step 3: Load decrypted key and compare with original
  bssl::UniquePtr<EVP_PKEY> decrypted_key(DecryptPrivateKey(decrypt_path, nullptr));
  ASSERT_TRUE(decrypted_key) << "Failed to load decrypted key";
  
  // Step 4: Compare with original key
  ASSERT_TRUE(CompareKeys(key.get(), decrypted_key.get())) << "Decrypted key doesn't match original";
}

// Test cross-compatibility with PRF: OpenSSL encrypts with hmacWithSHA1 PRF, AWS-LC decrypts
TEST_F(PKCS8ComparisonTest, PKCS8ToolCrossCompat_OpenSSL_To_AWSLC_WithPRF) {
  // Step 1: Use OpenSSL to encrypt the private key with custom PRF
  std::string encrypt_command = std::string(openssl_executable_path) + " pkcs8 -topk8 -v2 aes-256-cbc -v2prf hmacWithSHA1 -in " + 
                             in_path + " -out " + out_path_openssl + " -passout file:" + pass_path;
  
  int result = system(encrypt_command.c_str());
  ASSERT_EQ(0, result) << "OpenSSL encryption command with PRF failed";
  
  // Verify OpenSSL output has correct PKCS8 boundaries
  openssl_output_str = ReadFileToString(out_path_openssl);
  ASSERT_FALSE(openssl_output_str.empty());
  trim(openssl_output_str);
  std::cout << "OpenSSL output content (with PRF):" << std::endl << openssl_output_str << std::endl;
  ASSERT_TRUE(CheckPKCS8Boundaries(openssl_output_str, ENC_PKCS8_BEGIN, ENC_PKCS8_END, ENC_PKCS8_BEGIN, ENC_PKCS8_END));
  
  // Step 2: Use AWS-LC to decrypt the OpenSSL encrypted file
  std::string decrypt_command = std::string(tool_executable_path) + " pkcs8 -in " + out_path_openssl + 
                             " -out " + decrypt_path + " -passin file:" + pass_path;
  
  result = system(decrypt_command.c_str());
  ASSERT_EQ(0, result) << "AWS-LC decryption of OpenSSL output with PRF failed";
  
  // Step 3: Load decrypted key and compare with original
  bssl::UniquePtr<EVP_PKEY> decrypted_key(DecryptPrivateKey(decrypt_path, nullptr));
  ASSERT_TRUE(decrypted_key) << "Failed to load decrypted key";
  
  // Step 4: Compare with original key
  ASSERT_TRUE(CompareKeys(key.get(), decrypted_key.get())) << "Decrypted key doesn't match original";
}

// Original format comparison test with PRF kept for backward compatibility
TEST_F(PKCS8ComparisonTest, PKCS8ToolCompareV2prfOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " pkcs8 -topk8 -v2 aes-256-cbc -v2prf hmacWithSHA1 -in " + 
                             in_path + " -out " + out_path_tool + " -passout file:" + pass_path;
  std::string openssl_command = std::string(openssl_executable_path) + " pkcs8 -topk8 -v2 aes-256-cbc -v2prf hmacWithSHA1 -in " + 
                                in_path + " -out " + out_path_openssl + " -passout file:" + pass_path;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  trim(tool_output_str);
  trim(openssl_output_str);
  
  ASSERT_TRUE(CheckPKCS8Boundaries(tool_output_str, ENC_PKCS8_BEGIN, ENC_PKCS8_END, ENC_PKCS8_BEGIN, ENC_PKCS8_END));
  ASSERT_TRUE(CheckPKCS8Boundaries(openssl_output_str, ENC_PKCS8_BEGIN, ENC_PKCS8_END, ENC_PKCS8_BEGIN, ENC_PKCS8_END));
  
  // Decrypt both outputs and verify they match the original key
  bssl::UniquePtr<EVP_PKEY> aws_lc_decrypted(DecryptPrivateKey(out_path_tool, "testpassword"));
  bssl::UniquePtr<EVP_PKEY> openssl_decrypted(DecryptPrivateKey(out_path_openssl, "testpassword"));
  
  ASSERT_TRUE(aws_lc_decrypted) << "Failed to decrypt AWS-LC output";
  ASSERT_TRUE(openssl_decrypted) << "Failed to decrypt OpenSSL output";
  
  ASSERT_TRUE(CompareKeys(key.get(), aws_lc_decrypted.get())) << "AWS-LC encrypted key doesn't match original after decryption";
  ASSERT_TRUE(CompareKeys(key.get(), openssl_decrypted.get())) << "OpenSSL encrypted key doesn't match original after decryption";
}

// End of file
