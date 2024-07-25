// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "openssl/rsa.h"
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
// TODO: add instructions in readme

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

    rsa.reset(CreateRSAKey());
    ASSERT_TRUE(rsa);

    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_RSAPrivateKey(in_file.get(), rsa.get(), nullptr, nullptr, 0, nullptr, nullptr));
  }

  void RunCommandsAndCompareOutput(const std::string &tool_command, const std::string &openssl_command) {
    int tool_result = system(tool_command.c_str());
    ASSERT_EQ(tool_result, 0) << "AWS-LC tool command failed: " << tool_command;

    int openssl_result = system(openssl_command.c_str());
    ASSERT_EQ(openssl_result, 0) << "OpenSSL command failed: " << openssl_command;

    std::ifstream tool_output(out_path_tool);
    this->tool_output_str = std::string((std::istreambuf_iterator<char>(tool_output)), std::istreambuf_iterator<char>());
    std::ifstream openssl_output(out_path_openssl);
    this->openssl_output_str = std::string((std::istreambuf_iterator<char>(openssl_output)), std::istreambuf_iterator<char>());

    std::cout << "AWS-LC tool output:" << std::endl << this->tool_output_str << std::endl;
    std::cout << "OpenSSL output:" << std::endl << this->openssl_output_str << std::endl;
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

// Test against OpenSSL output "openssl rsa -noout -modulus -in file | openssl md5"
TEST_F(MD5ComparisonTest, MD5ToolCompareOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -noout -modulus -in " + in_path + " | openssl md5 > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -noout -modulus -in " + in_path + " | openssl md5 > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command);
  ASSERT_EQ(tool_output_str.compare(0, MODULUS.size(), MODULUS), 0);
  ASSERT_EQ(openssl_output_str.compare(0, MODULUS.size(), MODULUS), 0);
  ASSERT_EQ(tool_output_str.size(), openssl_output_str.size());

}
