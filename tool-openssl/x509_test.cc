// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "openssl/x509.h"
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

X509* CreateAndSignX509Certificate() {
  bssl::UniquePtr<X509> x509(X509_new());
  if (!x509) return nullptr;

  // Set validity period for 30 days
  if (!X509_gmtime_adj(X509_getm_notBefore(x509.get()), 0) ||
      !X509_gmtime_adj(X509_getm_notAfter(x509.get()), 60 * 60 * 24 * 30L)) {
    return nullptr;
  }

  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  if (!pkey) {
    return nullptr;
  }
  bssl::UniquePtr<RSA> rsa(RSA_new());
  bssl::UniquePtr<BIGNUM> bn(BN_new());
  if (!bn || !BN_set_word(bn.get(), RSA_F4) ||
      !RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr) ||
      !EVP_PKEY_assign_RSA(pkey.get(), rsa.release())) {
    return nullptr;
  }
  if (!X509_set_pubkey(x509.get(), pkey.get())) {
    return nullptr;
  }

  if (X509_sign(x509.get(), pkey.get(), EVP_sha256()) <= 0) {
    return nullptr;
  }

  return x509.release();
}

void RemoveFile(const char* path) {
  struct stat buffer;
  if (path != nullptr && stat(path, &buffer) == 0) {
    if (remove(path) != 0) {
      fprintf(stderr, "Error deleting %s: %s\n", path, strerror(errno));
    }
  }
}

class X509Test : public ::testing::Test {
public:
  static char in_path[PATH_MAX];
  static char csr_path[PATH_MAX];
  static char out_path[PATH_MAX];
  static char signkey_path[PATH_MAX];

protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(csr_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);
    ASSERT_GT(createTempFILEpath(signkey_path), 0u);

    bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
    ASSERT_TRUE(pkey);
    bssl::UniquePtr<RSA> rsa(RSA_new());
    ASSERT_TRUE(rsa);
    bssl::UniquePtr<BIGNUM> bn(BN_new());
    ASSERT_TRUE(bn && rsa && BN_set_word(bn.get(), RSA_F4) && RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr));
    ASSERT_TRUE(EVP_PKEY_assign_RSA(pkey.get(), rsa.release()));

    ScopedFILE signkey_file(fopen(signkey_path, "wb"));
    ASSERT_TRUE(signkey_file);
    ASSERT_TRUE(PEM_write_PrivateKey(signkey_file.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr));

    bssl::UniquePtr<X509> x509(CreateAndSignX509Certificate());
    ASSERT_TRUE(x509);

    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));

    bssl::UniquePtr<X509_REQ> csr(X509_REQ_new());
    ASSERT_TRUE(csr);
    X509_REQ_set_pubkey(csr.get(), pkey.get());
    X509_REQ_sign(csr.get(), pkey.get(), EVP_sha256());

    ScopedFILE csr_file(fopen(csr_path, "wb"));
    ASSERT_TRUE(csr_file);
    ASSERT_TRUE(PEM_write_X509_REQ(csr_file.get(), csr.get()));

  }
  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(csr_path);
    RemoveFile(out_path);
    RemoveFile(signkey_path);
  }
};

char X509Test::in_path[PATH_MAX];
char X509Test::csr_path[PATH_MAX];
char X509Test::out_path[PATH_MAX];
char X509Test::signkey_path[PATH_MAX];


// ----------------------------- X590 Option Tests -----------------------------

// Test -in and -out
TEST_F(X509Test, X509ToolInOutTest) {
  args_list_t args = {"-in", in_path, "-out", out_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
  {
    ScopedFILE out_file(fopen(out_path, "rb"));
    ASSERT_TRUE(out_file);
    bssl::UniquePtr<X509> parsed_x509(PEM_read_X509(out_file.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(parsed_x509);
  }
}

// Test -modulus
TEST_F(X509Test, X509ToolModulusTest) {
  args_list_t args = {"-in", in_path, "-modulus"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test signkey
TEST_F(X509Test, X509ToolSignkeyTest) {
  args_list_t args = {"-in", in_path, "-signkey", signkey_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -days
TEST_F(X509Test, X509ToolDaysTest) {
  args_list_t args = {"-in", in_path, "-out", out_path, "-signkey", signkey_path, "-days", "365"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -dates
TEST_F(X509Test, X509ToolDatesTest) {
  args_list_t args = {"-in", in_path, "-dates"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -checkend
TEST_F(X509Test, X509ToolCheckendTest) {
  args_list_t args = {"-in", in_path, "-checkend", "3600"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -req
TEST_F(X509Test, X509ToolReqTest) {
  args_list_t args = {"-in", csr_path, "-req", "-signkey", signkey_path, "-out", out_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// -------------------- X590 Option Usage Error Tests --------------------------

class X509OptionUsageErrorsTest : public X509Test {
protected:
  void TestOptionUsageErrors(const std::vector<std::string>& args) {
    args_list_t c_args;
    for (const auto& arg : args) {
      c_args.push_back(arg.c_str());
    }
    bool result = X509Tool(c_args);
    ASSERT_FALSE(result);
  }
};

//  Test mutually exclusive options
TEST_F(X509OptionUsageErrorsTest, MutuallyExclusiveOptionsTests) {
  std::vector<std::vector<std::string>> testparams = {
    {"-in", in_path, "-req", "-signkey", signkey_path, "-dates"},
    {"-in", in_path, "-req", "-signkey", signkey_path, "-checkend", "3600"},
    {"-in", in_path, "-signkey", signkey_path, "-dates"},
    {"-in", in_path, "-signkey", signkey_path, "-checkend", "3600"},
    {"-in", in_path, "-days", "365", "-dates"},
    {"-in", in_path, "-days", "365", "-checkend", "3600"},
  };
  for (const auto& args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// Test missing -in required option and test -req without -signkey
TEST_F(X509OptionUsageErrorsTest, RequiredOptionTests) {
  std::vector<std::vector<std::string>> testparams = {
    {"-out", "output.pem"},
    {"-in", in_path, "-req"},
  };
  for (const auto& args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// Test argument errors for -days: !<0 || non-integer, -checkend: !<=0 || non-integer
TEST_F(X509OptionUsageErrorsTest, DaysAndCheckendArgTests) {
  std::vector<std::vector<std::string>> testparams = {
    {"-in", in_path, "-checkend", "abc"},
    {"-in", in_path, "-checkend", "-1"},
    {"-in", in_path, "-signkey", signkey_path, "-days", "abc"},
    {"-in", in_path, "-signkey", signkey_path, "-days", "0"},
    {"-in", in_path, "-signkey", signkey_path, "-days", "-1.7"}
  };
  for (const auto& args : testparams) {
    TestOptionUsageErrors(args);
  }
}


// -------------------- X590 OpenSSL Comparison Tests --------------------------

// Comparison tests cannot run without set up of environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.
// TODO: add instructions in readme

class X509ComparisonTest : public ::testing::Test {
protected:
  void SetUp() override {

    // Skip gtests if env variables not set
    tool_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
    if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
      GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH environment variables are not set";
    }

    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(csr_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);
    ASSERT_GT(createTempFILEpath(signkey_path), 0u);

    x509.reset(CreateAndSignX509Certificate());
    ASSERT_TRUE(x509);

    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));

    bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
    ASSERT_TRUE(pkey);
    bssl::UniquePtr<RSA> rsa(RSA_new());
    bssl::UniquePtr<BIGNUM> bn(BN_new());
    ASSERT_TRUE(bn && BN_set_word(bn.get(), RSA_F4) && RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr));
    ASSERT_TRUE(EVP_PKEY_assign_RSA(pkey.get(), rsa.release()));

    ScopedFILE signkey_file(fopen(signkey_path, "wb"));
    ASSERT_TRUE(signkey_file);
    ASSERT_TRUE(PEM_write_PrivateKey(signkey_file.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr));

    csr.reset(X509_REQ_new());
    ASSERT_TRUE(csr);
    X509_REQ_set_pubkey(csr.get(), pkey.get());
    X509_REQ_sign(csr.get(), pkey.get(), EVP_sha256());

    ScopedFILE csr_file(fopen(csr_path, "wb"));
    ASSERT_TRUE(csr_file);
    ASSERT_TRUE(PEM_write_X509_REQ(csr_file.get(), csr.get()));
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
      RemoveFile(csr_path);
      RemoveFile(out_path_tool);
      RemoveFile(out_path_openssl);
      RemoveFile(signkey_path);
    }
  }

  char in_path[PATH_MAX];
  char csr_path[PATH_MAX];
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  char signkey_path[PATH_MAX];
  bssl::UniquePtr<X509> x509;
  bssl::UniquePtr<X509_REQ> csr;
  const char* tool_executable_path;
  const char* openssl_executable_path;
  std::string tool_output_str;
  std::string openssl_output_str;
};

// Helper function to trim whitespace from both ends of a string to test certificate output
static inline std::string &trim(std::string &s) {
  s.erase(s.begin(), std::find_if(s.begin(), s.end(), [](unsigned char ch) {
      return !std::isspace(static_cast<unsigned char>(ch));
  }));
  s.erase(std::find_if(s.rbegin(), s.rend(), [](unsigned char ch) {
      return !std::isspace(static_cast<unsigned char>(ch));
  }).base(), s.end());
  return s;
}

// Test against OpenSSL output "openssl x509 -in file -modulus"
TEST_F(X509ComparisonTest, X509ToolCompareModulusOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " + std::string(in_path) + " -modulus > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " x509 -in " + std::string(in_path) + " -modulus > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl x509 -in in_file -checkend 0"
TEST_F(X509ComparisonTest, X509ToolCompareCheckendOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " + std::string(in_path) + " -checkend 0 > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " x509 -in " + std::string(in_path) + " -checkend 0 > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl x509 -req -in csr_file -signkey private_key_file -days 80 -out out_file"
TEST_F(X509ComparisonTest, X509ToolCompareReqSignkeyDaysOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -req -in " + std::string(csr_path) + " -signkey " + std::string(signkey_path) + " -days 80 -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " x509 -req -in " + std::string(csr_path) + " -signkey " + std::string(signkey_path) + " -days 80 -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command);

  // Certificates will not be identical, therefore testing that cert header and footer are present
  ASSERT_TRUE(tool_output_str.find("-----BEGIN CERTIFICATE-----") == 0);
  trim(tool_output_str);
  ASSERT_TRUE(tool_output_str.compare(tool_output_str.size() - 25, 25, "-----END CERTIFICATE-----") == 0);

  ASSERT_TRUE(openssl_output_str.find("-----BEGIN CERTIFICATE-----") == 0);
  trim(openssl_output_str);
  ASSERT_TRUE(openssl_output_str.compare(openssl_output_str.size() - 25, 25, "-----END CERTIFICATE-----") == 0);
}

// Test against OpenSSL output "openssl x509 -in file -dates -noout"
TEST_F(X509ComparisonTest, X509ToolCompareDatesNooutOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " + std::string(in_path) + " -dates -noout > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " x509 -in " + std::string(in_path) + " -dates -noout > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}
