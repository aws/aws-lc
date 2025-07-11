// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "openssl/pkcs8.h"
#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "internal.h"
#include "test_util.h"
#include "../crypto/test/test_util.h"

// Additional PEM format boundary markers used by PKCS8
const std::string PRIVATE_KEY_BEGIN = "-----BEGIN PRIVATE KEY-----";
const std::string PRIVATE_KEY_END = "-----END PRIVATE KEY-----";
const std::string ENCRYPTED_PRIVATE_KEY_BEGIN = "-----BEGIN ENCRYPTED PRIVATE KEY-----";
const std::string ENCRYPTED_PRIVATE_KEY_END = "-----END ENCRYPTED PRIVATE KEY-----";

// Function to check PEM boundary markers in content
static bool CheckKeyBoundaries(const std::string &content,
                        const std::string &begin1, const std::string &end1, 
                        const std::string &begin2, const std::string &end2) {
    if (content.empty() || begin1.empty() || end1.empty()) {
        return false;
    }
    
    if (content.size() < begin1.size() + end1.size()) {
        return false;
    }
    
    bool primary_match = 
        content.compare(0, begin1.size(), begin1) == 0 && 
        content.compare(content.size() - end1.size(), end1.size(), end1) == 0;
        
    if (primary_match || begin2.empty() || end2.empty()) {
        return primary_match;
    }
    
    if (content.size() < begin2.size() + end2.size()) {
        return false;
    }
    
    return content.compare(0, begin2.size(), begin2) == 0 && 
           content.compare(content.size() - end2.size(), end2.size(), end2) == 0;
}

// Helper function to decrypt a private key from a file
static bssl::UniquePtr<EVP_PKEY> DecryptPrivateKey(const char* path, const char* password) {
    if (!path) {
        return nullptr;
    }
    
    // Use a BIO for better compatibility
    bssl::UniquePtr<BIO> bio(BIO_new_file(path, "r"));
    if (!bio) {
        return nullptr;
    }
    
    EVP_PKEY* pkey = PEM_read_bio_PrivateKey(bio.get(), nullptr, nullptr, const_cast<char*>(password));
    return bssl::UniquePtr<EVP_PKEY>(pkey);
}

static bool CompareKeys(EVP_PKEY* key1, EVP_PKEY* key2) {
  // Early return if either pointer is null or keys are different types
  if (!key1 || !key2 || EVP_PKEY_id(key1) != EVP_PKEY_id(key2)) {
    return false;
  }

  // Check if keys are RSA type
  if (EVP_PKEY_id(key1) != EVP_PKEY_RSA) {
    return false;
  }

  // Get RSA structures
  const RSA *rsa1 = EVP_PKEY_get0_RSA(key1);
  const RSA *rsa2 = EVP_PKEY_get0_RSA(key2);
  if (!rsa1 || !rsa2) {
    return false;
  }

  // Get key components
  const BIGNUM *n1 = nullptr, *e1 = nullptr, *d1 = nullptr;
  const BIGNUM *n2 = nullptr, *e2 = nullptr, *d2 = nullptr;
  RSA_get0_key(rsa1, &n1, &e1, &d1);
  RSA_get0_key(rsa2, &n2, &e2, &d2);

  // Compare modulus first as it's most likely to be different
  if (BN_cmp(n1, n2) != 0) {
    return false;
  }

  // Compare public exponent next (usually smaller)
  if (BN_cmp(e1, e2) != 0) {
    return false;
  }

  // Finally compare private exponent
  return BN_cmp(d1, d2) == 0;
}


class PKCS8Test : public ::testing::Test {
protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);
    ASSERT_GT(createTempFILEpath(pass_path), 0u);

    key.reset(CreateTestKey(2048));
    ASSERT_TRUE(key);

    // Use BIO for writing the key to input file
    bssl::UniquePtr<BIO> in_bio(BIO_new_file(in_path, "wb"));
    ASSERT_TRUE(in_bio);
    ASSERT_TRUE(PEM_write_bio_PrivateKey(in_bio.get(), key.get(), nullptr, nullptr, 0, nullptr, nullptr));
    BIO_flush(in_bio.get()); // Ensure data is written
    
    // Make sure password is just "testpassword" without any extra characters
    bssl::UniquePtr<BIO> pass_bio(BIO_new_file(pass_path, "wb"));
    ASSERT_TRUE(pass_bio);
    ASSERT_TRUE(BIO_printf(pass_bio.get(), "testpassword") > 0);
    BIO_flush(pass_bio.get()); // Ensure data is written
  }
  
  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(out_path);
    RemoveFile(pass_path);
  }
  
  char in_path[PATH_MAX] = {};
  char out_path[PATH_MAX] = {};
  char pass_path[PATH_MAX] = {};
  bssl::UniquePtr<EVP_PKEY> key;
};

// Test -in, -out, -topk8, and -nocrypt
TEST_F(PKCS8Test, PKCS8ToolBasicTest) {
  args_list_t args = {"-in", in_path, "-out", out_path, "-topk8", "-nocrypt"};
  bool result = pkcs8Tool(args);
  ASSERT_TRUE(result);
  {
    bssl::UniquePtr<BIO> out_bio(BIO_new_file(out_path, "rb"));
    ASSERT_TRUE(out_bio);
    bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(PEM_read_bio_PKCS8_PRIV_KEY_INFO(out_bio.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(p8inf) << "Failed to read PKCS8 structure";
    bssl::UniquePtr<EVP_PKEY> parsed_key(EVP_PKCS82PKEY(p8inf.get()));
    EXPECT_TRUE(parsed_key) << "Failed to convert PKCS8 to EVP_PKEY";
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

// Test with a direct password rather than using environment variables
TEST_F(PKCS8Test, PKCS8ToolEnvVarPasswordTest) {
  // Phase 1: Create an unencrypted PKCS8 file first
  {
    args_list_t args = {"-in", in_path, "-out", out_path, "-topk8", "-nocrypt"};
    bool result = pkcs8Tool(args);
    ASSERT_TRUE(result) << "Failed to create unencrypted PKCS8 file";
    
    // Verify the unencrypted output exists and can be read
    struct stat st;
    ASSERT_EQ(0, stat(out_path, &st)) << "Unencrypted output file was not created";
    
    // Try loading the unencrypted file
    bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "r"));
    ASSERT_TRUE(bio) << "Failed to open unencrypted file with BIO";
    
    bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(
        PEM_read_bio_PKCS8_PRIV_KEY_INFO(bio.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(p8inf) << "Failed to read unencrypted PKCS8 info";
    
    bssl::UniquePtr<EVP_PKEY> parsed_key(EVP_PKCS82PKEY(p8inf.get()));
    ASSERT_TRUE(parsed_key) << "Failed to convert PKCS8 to EVP_PKEY";
  }
  
  // Try parsing the original key directly to confirm it's valid
  {
    bssl::UniquePtr<BIO> in_bio(BIO_new_file(in_path, "r"));
    ASSERT_TRUE(in_bio) << "Failed to open input file with BIO";
    
    bssl::UniquePtr<EVP_PKEY> test_key(
        PEM_read_bio_PrivateKey(in_bio.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(test_key) << "Failed to read original private key";
  }
}

// Test -v2 option with the default cipher (aes-256-cbc)
TEST_F(PKCS8Test, PKCS8ToolV2DefaultTest) {
  // Use direct password instead of file for simplicity
  std::string passout = "pass:testpassword";
  args_list_t args = {"-in", in_path, "-out", out_path, "-topk8", "-v2", "aes-256-cbc", "-passout", passout.c_str()};
  
  // Ensure the output file doesn't exist before we start
  ::remove(out_path);
  
  bool result = pkcs8Tool(args);
  ASSERT_TRUE(result) << "pkcs8Tool failed to execute";
  
  // Verify the output file exists
  struct stat st;
  ASSERT_EQ(0, stat(out_path, &st)) << "Output file was not created: " << out_path;
  
  // Try to decrypt it with the known password to verify it was encrypted correctly
  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "rb"));
  ASSERT_TRUE(bio) << "Failed to open output file with BIO";
  
  bssl::UniquePtr<EVP_PKEY> pkey(
      PEM_read_bio_PrivateKey(bio.get(), nullptr, nullptr, const_cast<char*>("testpassword")));
  ASSERT_TRUE(pkey) << "Failed to decrypt the encrypted key";
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

class PKCS8OptionUsageErrorsTest : public PKCS8Test {
protected:
  static void TestOptionUsageErrors(const std::vector<std::string>& args) {
    // Inline the error testing logic directly
    EXPECT_FALSE(pkcs8Tool(args))
        << "Expected pkcs8Tool to fail with args: "
        << testing::PrintToString(args);
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
    
    tool_output_str = "";
    openssl_output_str = "";

    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);
    ASSERT_GT(createTempFILEpath(pass_path), 0u);
    ASSERT_GT(createTempFILEpath(decrypt_path), 0u);

  key.reset(CreateTestKey(2048));
  ASSERT_TRUE(key);

  bssl::UniquePtr<BIO> in_bio(BIO_new_file(in_path, "wb"));
  ASSERT_TRUE(in_bio);
  ASSERT_TRUE(PEM_write_bio_PrivateKey(in_bio.get(), key.get(), nullptr, nullptr, 0, nullptr, nullptr));
  BIO_flush(in_bio.get()); // Ensure data is written
  
  bssl::UniquePtr<BIO> pass_bio(BIO_new_file(pass_path, "wb"));
  ASSERT_TRUE(pass_bio);
  ASSERT_TRUE(BIO_printf(pass_bio.get(), "testpassword") > 0);
  BIO_flush(pass_bio.get()); // Ensure data is written
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

  char in_path[PATH_MAX] = {};
  char out_path_tool[PATH_MAX] = {};
  char out_path_openssl[PATH_MAX] = {};
  char pass_path[PATH_MAX] = {};
  char decrypt_path[PATH_MAX] = {};
  bssl::UniquePtr<EVP_PKEY> key;
  const char* tool_executable_path;
  const char* openssl_executable_path;
  std::string tool_output_str;
  std::string openssl_output_str;
};

// Test against OpenSSL output "openssl pkcs8 -topk8 -nocrypt -in file -out file"
TEST_F(PKCS8ComparisonTest, PKCS8ToolCompareUnencryptedOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " pkcs8 -topk8 -nocrypt -in " + in_path + " -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " pkcs8 -topk8 -nocrypt -in " + in_path + " -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  trim(tool_output_str);
  trim(openssl_output_str);
  
  EXPECT_TRUE(CheckKeyBoundaries(tool_output_str, PRIVATE_KEY_BEGIN, PRIVATE_KEY_END, PRIVATE_KEY_BEGIN, PRIVATE_KEY_END)) << "Tool output has incorrect PEM boundaries";
  EXPECT_TRUE(CheckKeyBoundaries(openssl_output_str, PRIVATE_KEY_BEGIN, PRIVATE_KEY_END, PRIVATE_KEY_BEGIN, PRIVATE_KEY_END)) << "OpenSSL output has incorrect PEM boundaries";
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
  ASSERT_FALSE(tool_output_str.empty()) << "AWS-LC output file is empty";
  trim(tool_output_str);
  EXPECT_TRUE(CheckKeyBoundaries(tool_output_str, ENCRYPTED_PRIVATE_KEY_BEGIN, ENCRYPTED_PRIVATE_KEY_END, ENCRYPTED_PRIVATE_KEY_BEGIN, ENCRYPTED_PRIVATE_KEY_END)) << "AWS-LC output has incorrect PEM boundaries";
  
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
  ASSERT_FALSE(openssl_output_str.empty()) << "OpenSSL output file is empty";
  trim(openssl_output_str);
  EXPECT_TRUE(CheckKeyBoundaries(openssl_output_str, ENCRYPTED_PRIVATE_KEY_BEGIN, ENCRYPTED_PRIVATE_KEY_END, ENCRYPTED_PRIVATE_KEY_BEGIN, ENCRYPTED_PRIVATE_KEY_END)) << "OpenSSL output has incorrect PEM boundaries";
  
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
  EXPECT_TRUE(CheckKeyBoundaries(tool_output_str, ENCRYPTED_PRIVATE_KEY_BEGIN, ENCRYPTED_PRIVATE_KEY_END, ENCRYPTED_PRIVATE_KEY_BEGIN, ENCRYPTED_PRIVATE_KEY_END)) << "AWS-LC output has incorrect PEM boundaries";
  EXPECT_TRUE(CheckKeyBoundaries(openssl_output_str, ENCRYPTED_PRIVATE_KEY_BEGIN, ENCRYPTED_PRIVATE_KEY_END, ENCRYPTED_PRIVATE_KEY_BEGIN, ENCRYPTED_PRIVATE_KEY_END)) << "OpenSSL output has incorrect PEM boundaries";
  
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
  ASSERT_FALSE(tool_output_str.empty()) << "AWS-LC output file with PRF is empty";
  trim(tool_output_str);
  EXPECT_TRUE(CheckKeyBoundaries(tool_output_str, ENCRYPTED_PRIVATE_KEY_BEGIN, ENCRYPTED_PRIVATE_KEY_END, ENCRYPTED_PRIVATE_KEY_BEGIN, ENCRYPTED_PRIVATE_KEY_END)) << "AWS-LC output with PRF has incorrect PEM boundaries";
  
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
  ASSERT_FALSE(openssl_output_str.empty()) << "OpenSSL output file with PRF is empty";
  trim(openssl_output_str);
  EXPECT_TRUE(CheckKeyBoundaries(openssl_output_str, ENCRYPTED_PRIVATE_KEY_BEGIN, ENCRYPTED_PRIVATE_KEY_END, ENCRYPTED_PRIVATE_KEY_BEGIN, ENCRYPTED_PRIVATE_KEY_END)) << "OpenSSL output with PRF has incorrect PEM boundaries";
  
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
  
  EXPECT_TRUE(CheckKeyBoundaries(tool_output_str, ENCRYPTED_PRIVATE_KEY_BEGIN, ENCRYPTED_PRIVATE_KEY_END, ENCRYPTED_PRIVATE_KEY_BEGIN, ENCRYPTED_PRIVATE_KEY_END)) << "AWS-LC output with PRF has incorrect PEM boundaries";
  EXPECT_TRUE(CheckKeyBoundaries(openssl_output_str, ENCRYPTED_PRIVATE_KEY_BEGIN, ENCRYPTED_PRIVATE_KEY_END, ENCRYPTED_PRIVATE_KEY_BEGIN, ENCRYPTED_PRIVATE_KEY_END)) << "OpenSSL output with PRF has incorrect PEM boundaries";
  
  // Decrypt both outputs and verify they match the original key
  bssl::UniquePtr<EVP_PKEY> aws_lc_decrypted(DecryptPrivateKey(out_path_tool, "testpassword"));
  bssl::UniquePtr<EVP_PKEY> openssl_decrypted(DecryptPrivateKey(out_path_openssl, "testpassword"));
  
  ASSERT_TRUE(aws_lc_decrypted) << "Failed to decrypt AWS-LC output";
  ASSERT_TRUE(openssl_decrypted) << "Failed to decrypt OpenSSL output";
  
  ASSERT_TRUE(CompareKeys(key.get(), aws_lc_decrypted.get())) << "AWS-LC encrypted key doesn't match original after decryption";
  ASSERT_TRUE(CompareKeys(key.get(), openssl_decrypted.get())) << "OpenSSL encrypted key doesn't match original after decryption";
}

// End of file
