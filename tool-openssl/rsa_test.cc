// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "openssl/rsa.h"
#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "internal.h"
#include <fstream>
#include <sstream>
#include <iterator>
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

RSA* CreateRSAKey() {
  bssl::UniquePtr<BIGNUM> bn(BN_new());
  if (!bn || !BN_set_word(bn.get(), RSA_F4)) {
    return nullptr;
  }
  bssl::UniquePtr<RSA> rsa(RSA_new());
  if (!rsa || !RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr)) {
    return nullptr;
  }
  return rsa.release();
}

class RSATest : public ::testing::Test {
protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);

    bssl::UniquePtr<RSA> rsa(CreateRSAKey());
    ASSERT_TRUE(rsa);

    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_RSAPrivateKey(in_file.get(), rsa.get(), nullptr, nullptr, 0, nullptr, nullptr));
  }
  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(out_path);
  }
  char in_path[PATH_MAX];
  char out_path[PATH_MAX];
};

// ----------------------------- RSA Option Tests -----------------------------

// Test -in and -out
TEST_F(RSATest, RSAToolInOutTest) {
  args_list_t args = {"-in", in_path, "-out", out_path};
  bool result = rsaTool(args);
  ASSERT_TRUE(result);
  {
    ScopedFILE out_file(fopen(out_path, "rb"));
    ASSERT_TRUE(out_file);
    bssl::UniquePtr<RSA> parsed_rsa(PEM_read_RSAPrivateKey(out_file.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(parsed_rsa);
  }
}

// Test -modulus
TEST_F(RSATest, RSAToolModulusTest) {
  args_list_t args = {"-in", in_path, "-modulus"};
  bool result = rsaTool(args);
  ASSERT_TRUE(result);
}

// Test -noout
TEST_F(RSATest, RSAToolNooutTest) {
  args_list_t args = {"-in", in_path, "-noout"};
  bool result = rsaTool(args);
  ASSERT_TRUE(result);
}


// -------------------- RSA Option Usage Error Tests --------------------------

class RSAOptionUsageErrorsTest : public RSATest {
protected:
  void TestOptionUsageErrors(const std::vector<std::string>& args) {
    args_list_t c_args;
    for (const auto& arg : args) {
      c_args.push_back(arg.c_str());
    }
    bool result = rsaTool(c_args);
    ASSERT_FALSE(result);
  }
};

// Test missing -in required option
TEST_F(RSAOptionUsageErrorsTest, RequiredOptionTests) {
  std::vector<std::vector<std::string>> testparams = {
    {"-out", "output.pem"},
    {"-modulus"},
  };
  for (const auto& args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// -------------------- RSA OpenSSL Comparison Tests --------------------------

// Comparison tests cannot run without set up of environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.
// TODO: add instructions in readme

class RSAComparisonTest : public ::testing::Test {
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

// Helper function to trim whitespace from both ends of a string to test RSA output
static inline std::string &trim(std::string &s) {
  s.erase(s.begin(), std::find_if(s.begin(), s.end(), [](unsigned char ch) {
      return !std::isspace(static_cast<unsigned char>(ch));
  }));
  s.erase(std::find_if(s.rbegin(), s.rend(), [](unsigned char ch) {
      return !std::isspace(static_cast<unsigned char>(ch));
  }).base(), s.end());
  return s;
}

// Helper function to read file content into a string
// Helper function to read file content into a string
std::string ReadFileToString(const std::string& file_path) {
  std::ifstream file_stream(file_path, std::ios::binary);
  if (!file_stream) {
    return "";
  }
  std::ostringstream buffer;
  buffer << file_stream.rdbuf();
  return buffer.str();
}

// OpenSSL rsa boundaries
const std::string BEGIN = "-----BEGIN PRIVATE KEY-----";
const std::string END = "-----END PRIVATE KEY-----";
// AWS-LC rsa boundaries
const std::string RSA_BEGIN = "-----BEGIN RSA PRIVATE KEY-----";
const std::string RSA_END = "-----END RSA PRIVATE KEY-----";

const std::string MODULUS = "Modulus=";

// Test against OpenSSL output "openssl rsa -in file -modulus"
// Rsa private key is printed to stdin
TEST_F(RSAComparisonTest, RSAToolCompareModulusOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + in_path + " > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + in_path + " > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command);

  trim(tool_output_str);
  ASSERT_EQ(tool_output_str.compare(0, RSA_BEGIN.size(), RSA_BEGIN), 0);
  ASSERT_EQ(tool_output_str.compare(tool_output_str.size() - RSA_END.size(), RSA_END.size(), RSA_END), 0);

  trim(openssl_output_str);
  ASSERT_EQ(openssl_output_str.compare(0, BEGIN.size(), BEGIN), 0);
  ASSERT_EQ(openssl_output_str.compare(openssl_output_str.size() - END.size(), END.size(), END), 0);
}

// Test against OpenSSL output "openssl rsa -in file -modulus -noout"
// Only modulus is printed to stdin
TEST_F(RSAComparisonTest, RSAToolCompareModulusNooutOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + in_path + " -modulus -noout > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + in_path + " -modulus -noout > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl rsa -in file -modulus -out out_file"
// Modulus and rsa private key are printed to output file
TEST_F(RSAComparisonTest, RSAToolCompareModulusOutOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + in_path + " -modulus -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + in_path + " -modulus -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command);

  ScopedFILE tool_out_file(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out_file);
  ScopedFILE openssl_out_file(fopen(out_path_openssl, "rb"));
  ASSERT_TRUE(openssl_out_file);

  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  trim(tool_output_str);
  ASSERT_EQ(tool_output_str.compare(0, MODULUS.size(), MODULUS), 0);
  ASSERT_EQ(tool_output_str.compare(tool_output_str.size() - RSA_END.size(), RSA_END.size(), RSA_END), 0);

  trim(openssl_output_str);
  ASSERT_EQ(openssl_output_str.compare(0, MODULUS.size(), MODULUS), 0);
  ASSERT_EQ(openssl_output_str.compare(openssl_output_str.size() - END.size(), END.size(), END), 0);
}

// Test against OpenSSL output "openssl rsa -in file -modulus -out out_file -noout"
// Only modulus is printed to output file
TEST_F(RSAComparisonTest, RSAToolCompareModulusOutNooutOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + in_path + " -modulus -out " + out_path_tool + " -noout";
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + in_path + " -modulus -out " + out_path_openssl + " -noout";

  RunCommandsAndCompareOutput(tool_command, openssl_command);

  ScopedFILE tool_out_file(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out_file);
  ScopedFILE openssl_out_file(fopen(out_path_openssl, "rb"));
  ASSERT_TRUE(openssl_out_file);

  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  ASSERT_EQ(tool_output_str, openssl_output_str);
}
