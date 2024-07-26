// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "internal.h"
#include <fstream>
#include <cctype>


#ifdef _WIN32
#include <windows.h>
#ifndef PATH_MAX
#define PATH_MAX MAX_PATH
#endif
#else
#include <unistd.h>
#ifndef PATH_MAX
#define PATH_MAX 4096
#endif
#endif

size_t createTempFILEpath(char buffer[PATH_MAX]);

void RemoveFile(const char* path);

std::string ReadFileToString(const std::string& file_path);

RSA* CreateRSAKey();


// -------------------- MD5 OpenSSL Comparison Test ---------------------------

// Comparison tests cannot run without set up of environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.

class MD5ComparisonTest : public ::testing::Test {
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

  }

  void TearDown() override {
    if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
      RemoveFile(in_path);
      RemoveFile(out_path_tool);
      RemoveFile(out_path_openssl);
    }
  }

  char in_path[PATH_MAX];
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  bssl::UniquePtr<RSA> rsa;
  const char* tool_executable_path;
  const char* openssl_executable_path;
  std::string tool_output_str;
  std::string openssl_output_str;
};

const std::string MODULUS = "MD5(stdin)= ";

// Test against OpenSSL output
TEST_F(MD5ComparisonTest, MD5ToolCompareOpenSSL) {
  // Create input file with test string
  std::string input_file = std::string(in_path) + "_md5_input";
  std::ofstream ofs(input_file);
  ofs << "AWS_LC_TEST_STRING_INPUT";
  ofs.close();

  std::string tool_command = std::string(tool_executable_path) + " md5 < " + input_file + " > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " md5 < " + input_file + " > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);

  RemoveFile(input_file.c_str());
}
