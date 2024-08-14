// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "../crypto/test/test_util.h"
#include "test_util.h"

// -------------------- MD5 OpenSSL Comparison Test ---------------------------

// Comparison tests cannot run without set up of environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.

class DgstComparisonTest : public ::testing::Test {
 protected:
  void SetUp() override {
    // Skip gtests if env variables not set
    awslc_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
    if (awslc_executable_path == nullptr ||
        openssl_executable_path == nullptr) {
      GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH "
                      "environment variables are not set";
    }
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path_awslc), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);
  }
  void TearDown() override {
    if (awslc_executable_path != nullptr &&
        openssl_executable_path != nullptr) {
      //      RemoveFile(in_path);
      RemoveFile(out_path_awslc);
      RemoveFile(out_path_openssl);
    }
  }
  char in_path[PATH_MAX];
  char out_path_awslc[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  const char *awslc_executable_path;
  const char *openssl_executable_path;
  std::string awslc_output_str;
  std::string openssl_output_str;
};

// OpenSSL versions 3.1.0 and later change from "(stdin)= " to "MD5(stdin) ="
std::string GetHash(const std::string &str) {
  size_t pos = str.find('=');
  if (pos == std::string::npos) {
    return "";
  }
  return str.substr(pos + 1);
}

// Test against OpenSSL output for "-hmac"
TEST_F(DgstComparisonTest, HMAC_default_files) {
  std::string input_file = std::string(in_path);
  std::ofstream ofs(input_file);
  ofs << "AWS_LC_TEST_STRING_INPUT";
  ofs.close();

  // Run -hmac against a single file.
  std::string awslc_command = std::string(awslc_executable_path) +
                              " dgst -hmac test_key_string " + input_file +
                              " > " + out_path_awslc;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " dgst -hmac test_key_string " + input_file +
                                " > " + out_path_openssl;

  RunCommandsAndCompareOutput(awslc_command, openssl_command, out_path_awslc,
                              out_path_openssl, awslc_output_str,
                              openssl_output_str);

  std::string awslc_hash = GetHash(awslc_output_str);
  std::string openssl_hash = GetHash(openssl_output_str);

  EXPECT_EQ(awslc_hash, openssl_hash);

  // Run -hmac again against multiple files.
  char in_path2[PATH_MAX];
  ASSERT_GT(createTempFILEpath(in_path2), 0u);
  std::string input_file2 = std::string(in_path2);
  ofs.open(input_file2);
  ofs << "AWS_LC_TEST_STRING_INPUT_2";
  ofs.close();

  awslc_command = std::string(awslc_executable_path) +
                  " dgst -hmac alternative_key_string " + input_file + " " +
                  input_file2 + " > " + out_path_awslc;
  openssl_command = std::string(openssl_executable_path) +
                    " dgst -hmac alternative_key_string " + input_file + " " +
                    input_file2 + +" > " + out_path_openssl;

  RunCommandsAndCompareOutput(awslc_command, openssl_command, out_path_awslc,
                              out_path_openssl, awslc_output_str,
                              openssl_output_str);

  awslc_hash = GetHash(awslc_output_str);
  openssl_hash = GetHash(openssl_output_str);

  EXPECT_EQ(awslc_hash, openssl_hash);

  // Run -hmac with empty key
  awslc_command = std::string(awslc_executable_path) +
                  " dgst -hmac \"\" "
                  " " +
                  input_file + " " + input_file2 + " > " + out_path_awslc;
  openssl_command = std::string(openssl_executable_path) + " dgst -hmac \"\" " +
                    input_file + " " + input_file2 + +" > " + out_path_openssl;

  RunCommandsAndCompareOutput(awslc_command, openssl_command, out_path_awslc,
                              out_path_openssl, awslc_output_str,
                              openssl_output_str);

  awslc_hash = GetHash(awslc_output_str);
  openssl_hash = GetHash(openssl_output_str);

  EXPECT_EQ(awslc_hash, openssl_hash);

  RemoveFile(input_file.c_str());
  RemoveFile(input_file2.c_str());
}


TEST_F(DgstComparisonTest, HMAC_default_stdin) {
  std::string tool_command = "echo hmac_this_string | " +
                             std::string(awslc_executable_path) +
                             " dgst -hmac key > " + out_path_awslc;
  std::string openssl_command = "echo hmac_this_string | " +
                                std::string(openssl_executable_path) +
                                " dgst -hmac key > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_awslc,
                              out_path_openssl, awslc_output_str,
                              openssl_output_str);

  std::string tool_hash = GetHash(awslc_output_str);
  std::string openssl_hash = GetHash(openssl_output_str);

  EXPECT_EQ(tool_hash, openssl_hash);
}

TEST_F(DgstComparisonTest, MD5_files) {
  std::string input_file = std::string(in_path);
  std::ofstream ofs(input_file);
  ofs << "AWS_LC_TEST_STRING_INPUT";
  ofs.close();

  // Input file as pipe (stdin)
  std::string tool_command = std::string(awslc_executable_path) + " md5 < " +
                             input_file + " > " + out_path_awslc;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " md5 < " + input_file + " > " +
                                out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_awslc,
                              out_path_openssl, awslc_output_str,
                              openssl_output_str);

  std::string tool_hash = GetHash(awslc_output_str);
  std::string openssl_hash = GetHash(openssl_output_str);

  EXPECT_EQ(tool_hash, openssl_hash);

  // Input file as regular command line option.
  tool_command = std::string(awslc_executable_path) + " md5 " + input_file +
                 " > " + out_path_awslc;
  openssl_command = std::string(openssl_executable_path) + " md5 " +
                    input_file + " > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_awslc,
                              out_path_openssl, awslc_output_str,
                              openssl_output_str);

  tool_hash = GetHash(awslc_output_str);
  openssl_hash = GetHash(openssl_output_str);

  EXPECT_EQ(tool_hash, openssl_hash);

  RemoveFile(input_file.c_str());
}

// Test against OpenSSL output with stdin.
TEST_F(DgstComparisonTest, MD5_stdin) {
  std::string tool_command = "echo hash_this_string | " +
                             std::string(awslc_executable_path) + " md5 > " +
                             out_path_awslc;
  std::string openssl_command = "echo hash_this_string | " +
                                std::string(openssl_executable_path) +
                                " md5 > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_awslc,
                              out_path_openssl, awslc_output_str,
                              openssl_output_str);

  std::string tool_hash = GetHash(awslc_output_str);
  std::string openssl_hash = GetHash(openssl_output_str);

  EXPECT_EQ(tool_hash, openssl_hash);
}
