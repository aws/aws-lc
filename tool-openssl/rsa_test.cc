// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "openssl/rsa.h"
#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "internal.h"
#include "test_util.h"
#include "../crypto/test/test_util.h"

bool CheckBoundaries(const std::string &content, const std::string &begin1, const std::string &end1, const std::string &begin2, const std::string &end2);

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


// RSA boundaries
const std::string RSA_BEGIN = "-----BEGIN RSA PRIVATE KEY-----";
const std::string RSA_END = "-----END RSA PRIVATE KEY-----";
const std::string BEGIN = "-----BEGIN PRIVATE KEY-----";
const std::string END = "-----END PRIVATE KEY-----";
const std::string MODULUS = "Modulus=";

// OpenSSL versions 3.1.0 and later change PEM outputs from "BEGIN RSA PRIVATE KEY" to "BEGIN PRIVATE KEY"
bool CheckBoundaries(const std::string &content, const std::string &begin1, const std::string &end1, const std::string &begin2, const std::string &end2) {
  return (content.compare(0, begin1.size(), begin1) == 0 && content.compare(content.size() - end1.size(), end1.size(), end1) == 0) ||
         (content.compare(0, begin2.size(), begin2) == 0 && content.compare(content.size() - end2.size(), end2.size(), end2) == 0);
}

// Test against OpenSSL output "openssl rsa -in file -modulus"
// Rsa private key is printed to stdin
TEST_F(RSAComparisonTest, RSAToolCompareModulusOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + in_path + " > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + in_path + " > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  trim(tool_output_str);
  ASSERT_TRUE(CheckBoundaries(tool_output_str, RSA_BEGIN, RSA_END, BEGIN, END));

  trim(openssl_output_str);
  ASSERT_TRUE(CheckBoundaries(openssl_output_str, RSA_BEGIN, RSA_END, BEGIN, END));
}

// Test against OpenSSL output "openssl rsa -in file -modulus -noout"
// Only modulus is printed to stdin
TEST_F(RSAComparisonTest, RSAToolCompareModulusNooutOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + in_path + " -modulus -noout > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + in_path + " -modulus -noout > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl rsa -in file -modulus -out out_file"
// Modulus and rsa private key are printed to output file
TEST_F(RSAComparisonTest, RSAToolCompareModulusOutOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + in_path + " -modulus -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + in_path + " -modulus -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ScopedFILE tool_out_file(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out_file);
  ScopedFILE openssl_out_file(fopen(out_path_openssl, "rb"));
  ASSERT_TRUE(openssl_out_file);

  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  trim(tool_output_str);
  ASSERT_TRUE(CheckBoundaries(tool_output_str, MODULUS, RSA_END, MODULUS, END));

  trim(openssl_output_str);
  ASSERT_TRUE(CheckBoundaries(openssl_output_str, MODULUS, RSA_END, MODULUS, END));
}

// Test against OpenSSL output "openssl rsa -in file -modulus -out out_file -noout"
// Only modulus is printed to output file
TEST_F(RSAComparisonTest, RSAToolCompareModulusOutNooutOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + in_path + " -modulus -out " + out_path_tool + " -noout";
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + in_path + " -modulus -out " + out_path_openssl + " -noout";

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ScopedFILE tool_out_file(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out_file);
  ScopedFILE openssl_out_file(fopen(out_path_openssl, "rb"));
  ASSERT_TRUE(openssl_out_file);

  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  trim(tool_output_str);
  trim(openssl_output_str);
  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl rsa -in file -noout -modulus"
// Only modulus is printed to stdin (reordered parameters)
TEST_F(RSAComparisonTest, RSAToolCompareReorderedModulusNooutOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + in_path + " -noout -modulus > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + in_path + " -noout -modulus > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl rsa -in file -noout -modulus -out out_file"
// Only modulus is printed to output file (reordered parameters)
TEST_F(RSAComparisonTest, RSAToolCompareReorderedModulusOutNooutOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + in_path + " -noout -modulus -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + in_path + " -noout -modulus -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ScopedFILE tool_out_file(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out_file);
  ScopedFILE openssl_out_file(fopen(out_path_openssl, "rb"));
  ASSERT_TRUE(openssl_out_file);

  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  trim(tool_output_str);
  trim(openssl_output_str);
  ASSERT_EQ(tool_output_str, openssl_output_str);
}
