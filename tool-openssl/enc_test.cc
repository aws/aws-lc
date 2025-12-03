// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/pem.h>
#include <sys/stat.h>
#include <cctype>
#include "internal.h"
#include "test_util.h"

class EncTest : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);

    // Create test input file with sample data
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    const char *test_data = "Hello, World! This is test data for encryption.";
    fwrite(test_data, 1, strlen(test_data), in_file.get());
  }

  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(out_path);
  }

  char in_path[PATH_MAX];
  char out_path[PATH_MAX];
};

// -------------------- Enc Basic Functionality Tests -------------------------

// Test help option
TEST_F(EncTest, EncToolHelpTest) {
  args_list_t args = {"-help"};
  bool result = encTool(args);
  ASSERT_TRUE(result);
}

// Test basic encryption with AES-128-CBC
TEST_F(EncTest, EncToolBasicEncryptionTest) {
  args_list_t args = {"-e",   "-aes-128-cbc",
                      "-K",   "0123456789abcdef0123456789abcdef",
                      "-iv",  "0123456789abcdef0123456789abcdef",
                      "-in",  in_path,
                      "-out", out_path};
  bool result = encTool(args);
  ASSERT_TRUE(result);

  // Verify output file exists and has content
  struct stat st;
  ASSERT_EQ(stat(out_path, &st), 0);
  ASSERT_GT(st.st_size, 0);
}

// Test basic decryption with AES-128-CBC
TEST_F(EncTest, EncToolBasicDecryptionTest) {
  // First encrypt
  args_list_t encrypt_args = {"-e",   "-aes-128-cbc",
                              "-K",   "0123456789abcdef0123456789abcdef",
                              "-iv",  "0123456789abcdef0123456789abcdef",
                              "-in",  in_path,
                              "-out", out_path};
  bool result = encTool(encrypt_args);
  ASSERT_TRUE(result);

  // Create temp file for decrypted output
  char decrypt_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(decrypt_path), 0u);

  // Then decrypt
  args_list_t decrypt_args = {"-d",   "-aes-128-cbc",
                              "-K",   "0123456789abcdef0123456789abcdef",
                              "-iv",  "0123456789abcdef0123456789abcdef",
                              "-in",  out_path,
                              "-out", decrypt_path};
  result = encTool(decrypt_args);
  ASSERT_TRUE(result);

  // Verify decrypted content matches original
  std::string original = ReadFileToString(in_path);
  std::string decrypted = ReadFileToString(decrypt_path);
  ASSERT_EQ(original, decrypted);

  RemoveFile(decrypt_path);
}

// Test decryption with explicit -d flag
TEST_F(EncTest, EncToolExplicitDecryptionTest) {
  // First encrypt
  args_list_t encrypt_args = {"-e",   "-aes-128-cbc",
                              "-K",   "0123456789abcdef0123456789abcdef",
                              "-iv",  "0123456789abcdef0123456789abcdef",
                              "-in",  in_path,
                              "-out", out_path};
  bool result = encTool(encrypt_args);
  ASSERT_TRUE(result);

  // Create temp file for decrypted output
  char decrypt_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(decrypt_path), 0u);

  // Test explicit -d flag
  args_list_t decrypt_args = {"-d",   "-aes-128-cbc",
                              "-K",   "0123456789abcdef0123456789abcdef",
                              "-iv",  "0123456789abcdef0123456789abcdef",
                              "-in",  out_path,
                              "-out", decrypt_path};
  result = encTool(decrypt_args);
  ASSERT_TRUE(result);

  RemoveFile(decrypt_path);
}

// Test decryption with default cipher
TEST_F(EncTest, EncToolDecryptionDefaultCipherTest) {
  // First encrypt with default cipher
  args_list_t encrypt_args = {"-e",
                              "-K",
                              "0123456789abcdef0123456789abcdef",
                              "-iv",
                              "0123456789abcdef0123456789abcdef",
                              "-in",
                              in_path,
                              "-out",
                              out_path};
  bool result = encTool(encrypt_args);
  ASSERT_TRUE(result);

  // Create temp file for decrypted output
  char decrypt_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(decrypt_path), 0u);

  // Decrypt with default cipher
  args_list_t decrypt_args = {"-d",
                              "-K",
                              "0123456789abcdef0123456789abcdef",
                              "-iv",
                              "0123456789abcdef0123456789abcdef",
                              "-in",
                              out_path,
                              "-out",
                              decrypt_path};
  result = encTool(decrypt_args);
  ASSERT_TRUE(result);

  RemoveFile(decrypt_path);
}

// Test default cipher (should be aes-128-cbc)
TEST_F(EncTest, EncToolDefaultCipherTest) {
  args_list_t args = {"-e",
                      "-K",
                      "0123456789abcdef0123456789abcdef",
                      "-iv",
                      "0123456789abcdef0123456789abcdef",
                      "-in",
                      in_path,
                      "-out",
                      out_path};
  bool result = encTool(args);
  ASSERT_TRUE(result);
}

// Test encryption without -e flag (should default to encrypt)
TEST_F(EncTest, EncToolDefaultEncryptTest) {
  args_list_t args = {"-aes-128-cbc",
                      "-K",
                      "0123456789abcdef0123456789abcdef",
                      "-iv",
                      "0123456789abcdef0123456789abcdef",
                      "-in",
                      in_path,
                      "-out",
                      out_path};
  bool result = encTool(args);
  ASSERT_TRUE(result);
}

// -------------------- Enc Option Usage Error Tests --------------------------

class EncOptionUsageErrorsTest : public EncTest {
 protected:
  void TestOptionUsageErrors(const std::vector<std::string> &args) {
    args_list_t c_args;
    for (const auto &arg : args) {
      c_args.push_back(arg.c_str());
    }
    bool result = encTool(c_args);
    ASSERT_FALSE(result);
  }
};

// Test missing required key
TEST_F(EncOptionUsageErrorsTest, MissingKeyTest) {
  std::vector<std::vector<std::string>> testparams = {
      {"-e", "-aes-128-cbc", "-iv", "0123456789abcdef0123456789abcdef", "-in",
       in_path},
      {"-d", "-aes-128-cbc", "-iv", "0123456789abcdef0123456789abcdef", "-in",
       in_path},
      {"-aes-128-cbc", "-iv", "0123456789abcdef0123456789abcdef", "-in",
       in_path}};
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// Test mutually exclusive -e and -d options
TEST_F(EncOptionUsageErrorsTest, MutuallyExclusiveOptionsTest) {
  std::vector<std::vector<std::string>> testparams = {
      {"-e", "-d", "-aes-128-cbc", "-K", "0123456789abcdef0123456789abcdef",
       "-iv", "0123456789abcdef0123456789abcdef", "-in", in_path}};
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// Test invalid hex key
TEST_F(EncOptionUsageErrorsTest, InvalidHexKeyTest) {
  std::vector<std::vector<std::string>> testparams = {
      {"-e", "-aes-128-cbc", "-K", "invalidhexkey", "-iv",
       "0123456789abcdef0123456789abcdef", "-in", in_path},
      {"-e", "-aes-128-cbc", "-K", "0123456789abcdefg123456789abcdef", "-iv",
       "0123456789abcdef0123456789abcdef", "-in", in_path}};
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// Test invalid hex IV
TEST_F(EncOptionUsageErrorsTest, InvalidHexIVTest) {
  std::vector<std::vector<std::string>> testparams = {
      {"-e", "-aes-128-cbc", "-K", "0123456789abcdef0123456789abcdef", "-iv",
       "invalidhexiv", "-in", in_path},
      {"-e", "-aes-128-cbc", "-K", "0123456789abcdef0123456789abcdef", "-iv",
       "0123456789abcdefg123456789abcdef", "-in", in_path}};
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// Test missing IV for cipher that requires it
TEST_F(EncOptionUsageErrorsTest, MissingIVTest) {
  std::vector<std::vector<std::string>> testparams = {
      {"-e", "-aes-128-cbc", "-K", "0123456789abcdef0123456789abcdef", "-in",
       in_path}};
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// Test invalid input file
TEST_F(EncOptionUsageErrorsTest, InvalidInputFileTest) {
  std::vector<std::vector<std::string>> testparams = {
      {"-e", "-aes-128-cbc", "-K", "0123456789abcdef0123456789abcdef", "-iv",
       "0123456789abcdef0123456789abcdef", "-in", "/nonexistent/file.txt"}};
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// -------------------- Enc OpenSSL Comparison Tests --------------------------

// Comparison tests cannot run without set up of environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.

class EncComparisonTest : public ::testing::Test {
 protected:
  void SetUp() override {
    // Skip gtests if env variables not set
    tool_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
    if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
      GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH "
                      "environment variables are not set";
    }

    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);

    // Create test input file
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    const char *test_data =
        "Hello, World! This is test data for encryption comparison.";
    fwrite(test_data, 1, strlen(test_data), in_file.get());
  }

  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(out_path_tool);
    RemoveFile(out_path_openssl);
  }

  char in_path[PATH_MAX];
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  const char *tool_executable_path;
  const char *openssl_executable_path;
};

// Test encryption comparison with OpenSSL
TEST_F(EncComparisonTest, EncryptionComparisonTest) {
  std::string key = "0123456789abcdef0123456789abcdef";
  std::string iv = "0123456789abcdef0123456789abcdef";

  std::string tool_command = std::string(tool_executable_path) +
                             " enc -e -aes-128-cbc -K " + key + " -iv " + iv +
                             " -in " + in_path + " -out " + out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " enc -e -aes-128-cbc -K " + key +
      " -iv " + iv + " -in " + in_path + " -out " + out_path_openssl;

  std::string tool_output_str, openssl_output_str;
  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  // Compare encrypted outputs
  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test decryption comparison with OpenSSL
TEST_F(EncComparisonTest, DecryptionComparisonTest) {
  std::string key = "0123456789abcdef0123456789abcdef";
  std::string iv = "0123456789abcdef0123456789abcdef";

  // First encrypt with OpenSSL to create encrypted data
  char encrypted_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(encrypted_path), 0u);

  std::string openssl_encrypt_cmd =
      std::string(openssl_executable_path) + " enc -e -aes-128-cbc -K " + key +
      " -iv " + iv + " -in " + in_path + " -out " + encrypted_path;
  ASSERT_EQ(ExecuteCommand(openssl_encrypt_cmd), 0);

  // Now test decryption comparison
  std::string tool_command =
      std::string(tool_executable_path) + " enc -d -aes-128-cbc -K " + key +
      " -iv " + iv + " -in " + encrypted_path + " -out " + out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " enc -d -aes-128-cbc -K " + key +
      " -iv " + iv + " -in " + encrypted_path + " -out " + out_path_openssl;

  std::string tool_output_str, openssl_output_str;
  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  // Compare decrypted outputs
  ASSERT_EQ(tool_output_str, openssl_output_str);

  RemoveFile(encrypted_path);
}
