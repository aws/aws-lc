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

// Test invalid file path
TEST_F(RSAOptionUsageErrorsTest, InvalidFilePathTest) {
  args_list_t args = {"-in", "/nonexistent/path/to/key.pem"};
  bool result = rsaTool(args);
  ASSERT_FALSE(result);
}

// -------------------- RSA Functional Unit Tests -----------------------------

class RSAFunctionalTest : public ::testing::Test {
protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);
    ASSERT_GT(createTempFILEpath(pub_path), 0u);

    rsa.reset(CreateRSAKey());
    ASSERT_TRUE(rsa);

    // Write private key in PEM format
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_RSAPrivateKey(in_file.get(), rsa.get(), nullptr, nullptr, 0, nullptr, nullptr));
  }

  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(out_path);
    RemoveFile(pub_path);
  }

  char in_path[PATH_MAX];
  char out_path[PATH_MAX];
  char pub_path[PATH_MAX];
  bssl::UniquePtr<RSA> rsa;
};

// Test PEM to PEM conversion (default)
TEST_F(RSAFunctionalTest, PEMtoPEMConversion) {
  args_list_t args = {"-in", in_path, "-out", out_path};
  ASSERT_TRUE(rsaTool(args));

  ScopedFILE out_file(fopen(out_path, "rb"));
  ASSERT_TRUE(out_file);
  bssl::UniquePtr<RSA> parsed_rsa(PEM_read_RSAPrivateKey(out_file.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(parsed_rsa);

  // Verify modulus matches
  EXPECT_EQ(BN_cmp(RSA_get0_n(rsa.get()), RSA_get0_n(parsed_rsa.get())), 0);
}

// Test PEM to DER conversion
TEST_F(RSAFunctionalTest, PEMtoDERConversion) {
  args_list_t args = {"-in", in_path, "-out", out_path, "-outform", "DER"};
  ASSERT_TRUE(rsaTool(args));

  ScopedFILE out_file(fopen(out_path, "rb"));
  ASSERT_TRUE(out_file);
  bssl::UniquePtr<EVP_PKEY> pkey(d2i_PrivateKey_fp(out_file.get(), nullptr));
  ASSERT_TRUE(pkey);
  bssl::UniquePtr<RSA> parsed_rsa(EVP_PKEY_get1_RSA(pkey.get()));
  ASSERT_TRUE(parsed_rsa);

  // Verify modulus matches
  EXPECT_EQ(BN_cmp(RSA_get0_n(rsa.get()), RSA_get0_n(parsed_rsa.get())), 0);
}

// Test DER to PEM conversion
TEST_F(RSAFunctionalTest, DERtoPEMConversion) {
  // First create a DER input file
  char der_in_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(der_in_path), 0u);
  {
    ScopedFILE der_file(fopen(der_in_path, "wb"));
    ASSERT_TRUE(der_file);
    bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
    ASSERT_TRUE(pkey);
    ASSERT_TRUE(EVP_PKEY_set1_RSA(pkey.get(), rsa.get()));
    ASSERT_TRUE(i2d_PrivateKey_fp(der_file.get(), pkey.get()));
  }

  args_list_t args = {"-in", der_in_path, "-inform", "DER", "-out", out_path, "-outform", "PEM"};
  ASSERT_TRUE(rsaTool(args));

  ScopedFILE out_file(fopen(out_path, "rb"));
  ASSERT_TRUE(out_file);
  bssl::UniquePtr<RSA> parsed_rsa(PEM_read_RSAPrivateKey(out_file.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(parsed_rsa);

  // Verify modulus matches
  EXPECT_EQ(BN_cmp(RSA_get0_n(rsa.get()), RSA_get0_n(parsed_rsa.get())), 0);

  RemoveFile(der_in_path);
}

// Test public key output
TEST_F(RSAFunctionalTest, PublicKeyOutput) {
  args_list_t args = {"-in", in_path, "-out", out_path, "-pubout"};
  ASSERT_TRUE(rsaTool(args));

  ScopedFILE out_file(fopen(out_path, "rb"));
  ASSERT_TRUE(out_file);
  bssl::UniquePtr<EVP_PKEY> pkey(PEM_read_PUBKEY(out_file.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(pkey);
  bssl::UniquePtr<RSA> parsed_rsa(EVP_PKEY_get1_RSA(pkey.get()));
  ASSERT_TRUE(parsed_rsa);

  // Verify modulus matches (public component)
  EXPECT_EQ(BN_cmp(RSA_get0_n(rsa.get()), RSA_get0_n(parsed_rsa.get())), 0);
  // Verify public exponent matches
  EXPECT_EQ(BN_cmp(RSA_get0_e(rsa.get()), RSA_get0_e(parsed_rsa.get())), 0);
  // Private key should not be present
  EXPECT_EQ(RSA_get0_d(parsed_rsa.get()), nullptr);
}

// Test public key input and output
TEST_F(RSAFunctionalTest, PublicKeyInputOutput) {
  // First create a public key input file
  {
    ScopedFILE pub_file(fopen(pub_path, "wb"));
    ASSERT_TRUE(pub_file);
    bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
    ASSERT_TRUE(pkey);
    ASSERT_TRUE(EVP_PKEY_set1_RSA(pkey.get(), rsa.get()));
    ASSERT_TRUE(PEM_write_PUBKEY(pub_file.get(), pkey.get()));
  }

  args_list_t args = {"-in", pub_path, "-pubin", "-out", out_path};
  ASSERT_TRUE(rsaTool(args));

  ScopedFILE out_file(fopen(out_path, "rb"));
  ASSERT_TRUE(out_file);
  bssl::UniquePtr<EVP_PKEY> pkey(PEM_read_PUBKEY(out_file.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(pkey);
  bssl::UniquePtr<RSA> parsed_rsa(EVP_PKEY_get1_RSA(pkey.get()));
  ASSERT_TRUE(parsed_rsa);

  // Verify modulus matches
  EXPECT_EQ(BN_cmp(RSA_get0_n(rsa.get()), RSA_get0_n(parsed_rsa.get())), 0);
}

// Test public key DER to PEM conversion
TEST_F(RSAFunctionalTest, PublicKeyDERtoPEM) {
  // First create a DER public key input file
  char der_pub_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(der_pub_path), 0u);
  {
    ScopedFILE der_file(fopen(der_pub_path, "wb"));
    ASSERT_TRUE(der_file);
    bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
    ASSERT_TRUE(pkey);
    ASSERT_TRUE(EVP_PKEY_set1_RSA(pkey.get(), rsa.get()));
    ASSERT_TRUE(i2d_PUBKEY_fp(der_file.get(), pkey.get()));
  }

  args_list_t args = {"-in", der_pub_path, "-inform", "DER", "-pubin", "-out", out_path, "-outform", "PEM"};
  ASSERT_TRUE(rsaTool(args));

  ScopedFILE out_file(fopen(out_path, "rb"));
  ASSERT_TRUE(out_file);
  bssl::UniquePtr<EVP_PKEY> pkey(PEM_read_PUBKEY(out_file.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(pkey);
  bssl::UniquePtr<RSA> parsed_rsa(EVP_PKEY_get1_RSA(pkey.get()));
  ASSERT_TRUE(parsed_rsa);

  // Verify modulus matches
  EXPECT_EQ(BN_cmp(RSA_get0_n(rsa.get()), RSA_get0_n(parsed_rsa.get())), 0);

  RemoveFile(der_pub_path);
}

// Test modulus output
TEST_F(RSAFunctionalTest, ModulusOutput) {
  args_list_t args = {"-in", in_path, "-modulus", "-noout"};
  ASSERT_TRUE(rsaTool(args));
  // The output goes to stdout, just verify the command succeeds
}

// Test modulus with output file
TEST_F(RSAFunctionalTest, ModulusWithOutput) {
  args_list_t args = {"-in", in_path, "-modulus", "-out", out_path};
  ASSERT_TRUE(rsaTool(args));

  // Read output and verify it contains "Modulus="
  std::string output = ReadFileToString(out_path);
  EXPECT_TRUE(output.find("Modulus=") != std::string::npos);
  EXPECT_TRUE(output.find("\n") != std::string::npos);

  // Verify the modulus hex value is present and uppercase
  const BIGNUM *n = RSA_get0_n(rsa.get());
  ASSERT_TRUE(n);
  char *hex_modulus = BN_bn2hex(n);
  ASSERT_TRUE(hex_modulus);

  // Convert to uppercase for comparison
  std::string expected_hex(hex_modulus);
  for (char &c : expected_hex) {
    c = toupper(c);
  }

  EXPECT_TRUE(output.find(expected_hex) != std::string::npos);
  OPENSSL_free(hex_modulus);
}

// Test noout option prevents key output
TEST_F(RSAFunctionalTest, NooutPreventsKeyOutput) {
  args_list_t args = {"-in", in_path, "-noout", "-out", out_path};
  ASSERT_TRUE(rsaTool(args));

  // Output file should be empty or not contain a key
  std::string output = ReadFileToString(out_path);
  EXPECT_TRUE(output.empty() || output.find("-----BEGIN") == std::string::npos);
}

// Test combined modulus and key output
TEST_F(RSAFunctionalTest, ModulusAndKeyOutput) {
  args_list_t args = {"-in", in_path, "-modulus", "-out", out_path};
  ASSERT_TRUE(rsaTool(args));

  std::string output = ReadFileToString(out_path);

  // Should contain both modulus and key
  EXPECT_TRUE(output.find("Modulus=") != std::string::npos);
  EXPECT_TRUE(output.find("-----BEGIN") != std::string::npos);
  EXPECT_TRUE(output.find("-----END") != std::string::npos);
}

// Test DER output with public key
TEST_F(RSAFunctionalTest, PublicKeyDEROutput) {
  args_list_t args = {"-in", in_path, "-pubout", "-outform", "DER", "-out", out_path};
  ASSERT_TRUE(rsaTool(args));

  ScopedFILE out_file(fopen(out_path, "rb"));
  ASSERT_TRUE(out_file);
  bssl::UniquePtr<EVP_PKEY> pkey(d2i_PUBKEY_fp(out_file.get(), nullptr));
  ASSERT_TRUE(pkey);
  bssl::UniquePtr<RSA> parsed_rsa(EVP_PKEY_get1_RSA(pkey.get()));
  ASSERT_TRUE(parsed_rsa);

  // Verify modulus matches
  EXPECT_EQ(BN_cmp(RSA_get0_n(rsa.get()), RSA_get0_n(parsed_rsa.get())), 0);
}

// Test invalid inform value
TEST_F(RSAFunctionalTest, InvalidInformValue) {
  args_list_t args = {"-in", in_path, "-inform", "INVALID", "-out", out_path};
  ASSERT_FALSE(rsaTool(args));
}

// Test invalid outform value
TEST_F(RSAFunctionalTest, InvalidOutformValue) {
  args_list_t args = {"-in", in_path, "-outform", "INVALID", "-out", out_path};
  ASSERT_FALSE(rsaTool(args));
}

// Test help option
TEST_F(RSAFunctionalTest, HelpOption) {
  args_list_t args = {"-help"};
  ASSERT_TRUE(rsaTool(args));
}

// Test case insensitive format arguments
TEST_F(RSAFunctionalTest, CaseInsensitiveFormats) {
  args_list_t args1 = {"-in", in_path, "-out", out_path, "-outform", "der"};
  ASSERT_TRUE(rsaTool(args1));

  args_list_t args2 = {"-in", in_path, "-out", out_path, "-outform", "pem"};
  ASSERT_TRUE(rsaTool(args2));

  args_list_t args3 = {"-in", in_path, "-out", out_path, "-outform", "DeR"};
  ASSERT_TRUE(rsaTool(args3));
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

// ---------------------- RSA Format Conversion Tests -------------------------

class RSAFormatComparisonTest : public ::testing::Test {
protected:
  void SetUp() override {
    // Skip gtests if env variables not set
    tool_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
    if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
      GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH environment variables are not set";
    }

    ASSERT_GT(createTempFILEpath(priv_pem_path), 0u);
    ASSERT_GT(createTempFILEpath(priv_der_path), 0u);
    ASSERT_GT(createTempFILEpath(pub_pem_path), 0u);
    ASSERT_GT(createTempFILEpath(pub_der_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);

    rsa.reset(CreateRSAKey());
    ASSERT_TRUE(rsa);

    // Create private key PEM
    ScopedFILE priv_pem_file(fopen(priv_pem_path, "wb"));
    ASSERT_TRUE(priv_pem_file);
    ASSERT_TRUE(PEM_write_RSAPrivateKey(priv_pem_file.get(), rsa.get(), nullptr, nullptr, 0, nullptr, nullptr));
    priv_pem_file.reset();

    // Create private key DER
    ScopedFILE priv_der_file(fopen(priv_der_path, "wb"));
    ASSERT_TRUE(priv_der_file);
    bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
    ASSERT_TRUE(pkey);
    ASSERT_TRUE(EVP_PKEY_set1_RSA(pkey.get(), rsa.get()));
    ASSERT_TRUE(i2d_PrivateKey_fp(priv_der_file.get(), pkey.get()));
    priv_der_file.reset();

    // Create public key PEM
    ScopedFILE pub_pem_file(fopen(pub_pem_path, "wb"));
    ASSERT_TRUE(pub_pem_file);
    ASSERT_TRUE(PEM_write_RSA_PUBKEY(pub_pem_file.get(), rsa.get()));
    pub_pem_file.reset();

    // Create public key DER
    ScopedFILE pub_der_file(fopen(pub_der_path, "wb"));
    ASSERT_TRUE(pub_der_file);
    ASSERT_TRUE(i2d_RSA_PUBKEY_fp(pub_der_file.get(), rsa.get()));
  }

  void TearDown() override {
    if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
      RemoveFile(priv_pem_path);
      RemoveFile(priv_der_path);
      RemoveFile(pub_pem_path);
      RemoveFile(pub_der_path);
      RemoveFile(out_path_tool);
      RemoveFile(out_path_openssl);
    }
  }

  char priv_pem_path[PATH_MAX];
  char priv_der_path[PATH_MAX];
  char pub_pem_path[PATH_MAX];
  char pub_der_path[PATH_MAX];
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  bssl::UniquePtr<RSA> rsa;
  const char* tool_executable_path;
  const char* openssl_executable_path;
  std::string tool_output_str;
  std::string openssl_output_str;
};

const std::string RSA_PUBLIC_BEGIN = "-----BEGIN RSA PUBLIC KEY-----";
const std::string RSA_PUBLIC_END = "-----END RSA PUBLIC KEY-----";
const std::string PUBLIC_BEGIN = "-----BEGIN PUBLIC KEY-----";
const std::string PUBLIC_END = "-----END PUBLIC KEY-----";

// Test -pubin with PEM input (default format)
TEST_F(RSAFormatComparisonTest, RSAToolPubinPEMTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + pub_pem_path + " -pubin -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + pub_pem_path + " -pubin -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Read and verify output files contain valid public keys
  ScopedFILE tool_out(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out);
  bssl::UniquePtr<RSA> tool_rsa(PEM_read_RSA_PUBKEY(tool_out.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(tool_rsa);

  ScopedFILE openssl_out(fopen(out_path_openssl, "rb"));
  ASSERT_TRUE(openssl_out);
  bssl::UniquePtr<RSA> openssl_rsa(PEM_read_RSA_PUBKEY(openssl_out.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(openssl_rsa);

  // Compare moduli
  const BIGNUM *tool_n = RSA_get0_n(tool_rsa.get());
  const BIGNUM *openssl_n = RSA_get0_n(openssl_rsa.get());
  ASSERT_EQ(BN_cmp(tool_n, openssl_n), 0);
}

// Test -pubin with DER input using -inform DER
TEST_F(RSAFormatComparisonTest, RSAToolPubinDERInputTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + pub_der_path + " -pubin -inform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + pub_der_path + " -pubin -inform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Verify both outputs are valid public keys
  ScopedFILE tool_out(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out);
  bssl::UniquePtr<RSA> tool_rsa(PEM_read_RSA_PUBKEY(tool_out.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(tool_rsa);

  ScopedFILE openssl_out(fopen(out_path_openssl, "rb"));
  ASSERT_TRUE(openssl_out);
  bssl::UniquePtr<RSA> openssl_rsa(PEM_read_RSA_PUBKEY(openssl_out.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(openssl_rsa);
}

// Test -pubin with -outform DER
TEST_F(RSAFormatComparisonTest, RSAToolPubinDEROutputTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + pub_pem_path + " -pubin -outform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + pub_pem_path + " -pubin -outform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Read DER output and verify it's valid
  ScopedFILE tool_out(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out);
  bssl::UniquePtr<RSA> tool_rsa(d2i_RSA_PUBKEY_fp(tool_out.get(), nullptr));
  ASSERT_TRUE(tool_rsa);

  ScopedFILE openssl_out(fopen(out_path_openssl, "rb"));
  ASSERT_TRUE(openssl_out);
  bssl::UniquePtr<RSA> openssl_rsa(d2i_RSA_PUBKEY_fp(openssl_out.get(), nullptr));
  ASSERT_TRUE(openssl_rsa);

  // Compare file contents should be identical for DER
  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test -inform DER with private key
TEST_F(RSAFormatComparisonTest, RSAToolPrivateKeyDERInputTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_der_path + " -inform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_der_path + " -inform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Verify both outputs are valid private keys
  ScopedFILE tool_out(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out);
  bssl::UniquePtr<RSA> tool_rsa(PEM_read_RSAPrivateKey(tool_out.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(tool_rsa);

  ScopedFILE openssl_out(fopen(out_path_openssl, "rb"));
  ASSERT_TRUE(openssl_out);
  bssl::UniquePtr<RSA> openssl_rsa(PEM_read_RSAPrivateKey(openssl_out.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(openssl_rsa);
}

// Test -outform DER with private key
TEST_F(RSAFormatComparisonTest, RSAToolPrivateKeyDEROutputTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -outform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -outform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Read DER output and verify it's valid
  ScopedFILE tool_out(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out);
  bssl::UniquePtr<EVP_PKEY> tool_pkey(d2i_PrivateKey_fp(tool_out.get(), nullptr));
  ASSERT_TRUE(tool_pkey);
  bssl::UniquePtr<RSA> tool_rsa(EVP_PKEY_get1_RSA(tool_pkey.get()));
  ASSERT_TRUE(tool_rsa);

  ScopedFILE openssl_out(fopen(out_path_openssl, "rb"));
  ASSERT_TRUE(openssl_out);
  bssl::UniquePtr<EVP_PKEY> openssl_pkey(d2i_PrivateKey_fp(openssl_out.get(), nullptr));
  ASSERT_TRUE(openssl_pkey);
  bssl::UniquePtr<RSA> openssl_rsa(EVP_PKEY_get1_RSA(openssl_pkey.get()));
  ASSERT_TRUE(openssl_rsa);

  // Compare moduli to ensure keys are equivalent (DER encoding may differ slightly)
  const BIGNUM *tool_n = RSA_get0_n(tool_rsa.get());
  const BIGNUM *openssl_n = RSA_get0_n(openssl_rsa.get());
  ASSERT_EQ(BN_cmp(tool_n, openssl_n), 0);
}

// Test DER to DER conversion (private key)
TEST_F(RSAFormatComparisonTest, RSAToolPrivateKeyDERtoDERTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_der_path + " -inform DER -outform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_der_path + " -inform DER -outform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Parse and verify both outputs are valid private keys with same modulus
  ScopedFILE tool_out(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out);
  bssl::UniquePtr<EVP_PKEY> tool_pkey(d2i_PrivateKey_fp(tool_out.get(), nullptr));
  ASSERT_TRUE(tool_pkey);
  bssl::UniquePtr<RSA> tool_rsa(EVP_PKEY_get1_RSA(tool_pkey.get()));
  ASSERT_TRUE(tool_rsa);

  ScopedFILE openssl_out(fopen(out_path_openssl, "rb"));
  ASSERT_TRUE(openssl_out);
  bssl::UniquePtr<EVP_PKEY> openssl_pkey(d2i_PrivateKey_fp(openssl_out.get(), nullptr));
  ASSERT_TRUE(openssl_pkey);
  bssl::UniquePtr<RSA> openssl_rsa(EVP_PKEY_get1_RSA(openssl_pkey.get()));
  ASSERT_TRUE(openssl_rsa);

  // Compare moduli to ensure keys are equivalent
  const BIGNUM *tool_n = RSA_get0_n(tool_rsa.get());
  const BIGNUM *openssl_n = RSA_get0_n(openssl_rsa.get());
  ASSERT_EQ(BN_cmp(tool_n, openssl_n), 0);
}

// Test DER to PEM conversion (private key)
TEST_F(RSAFormatComparisonTest, RSAToolPrivateKeyDERtoPEMTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_der_path + " -inform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_der_path + " -inform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Verify PEM output
  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  trim(tool_output_str);
  ASSERT_TRUE(CheckBoundaries(tool_output_str, RSA_BEGIN, RSA_END, BEGIN, END));
  trim(openssl_output_str);
  ASSERT_TRUE(CheckBoundaries(openssl_output_str, RSA_BEGIN, RSA_END, BEGIN, END));
}

// Test PEM to DER conversion (private key)
TEST_F(RSAFormatComparisonTest, RSAToolPrivateKeyPEMtoDERTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -outform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -outform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Parse and verify both outputs are valid private keys with same modulus
  ScopedFILE tool_out(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out);
  bssl::UniquePtr<EVP_PKEY> tool_pkey(d2i_PrivateKey_fp(tool_out.get(), nullptr));
  ASSERT_TRUE(tool_pkey);
  bssl::UniquePtr<RSA> tool_rsa(EVP_PKEY_get1_RSA(tool_pkey.get()));
  ASSERT_TRUE(tool_rsa);

  ScopedFILE openssl_out(fopen(out_path_openssl, "rb"));
  ASSERT_TRUE(openssl_out);
  bssl::UniquePtr<EVP_PKEY> openssl_pkey(d2i_PrivateKey_fp(openssl_out.get(), nullptr));
  ASSERT_TRUE(openssl_pkey);
  bssl::UniquePtr<RSA> openssl_rsa(EVP_PKEY_get1_RSA(openssl_pkey.get()));
  ASSERT_TRUE(openssl_rsa);

  // Compare moduli to ensure keys are equivalent
  const BIGNUM *tool_n = RSA_get0_n(tool_rsa.get());
  const BIGNUM *openssl_n = RSA_get0_n(openssl_rsa.get());
  ASSERT_EQ(BN_cmp(tool_n, openssl_n), 0);
}

// Test DER to DER conversion (public key with -pubin)
TEST_F(RSAFormatComparisonTest, RSAToolPublicKeyDERtoDERTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + pub_der_path + " -pubin -inform DER -outform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + pub_der_path + " -pubin -inform DER -outform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // DER output should be identical
  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test DER to PEM conversion (public key with -pubin)
TEST_F(RSAFormatComparisonTest, RSAToolPublicKeyDERtoPEMTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + pub_der_path + " -pubin -inform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + pub_der_path + " -pubin -inform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Verify PEM output
  ScopedFILE tool_out(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out);
  bssl::UniquePtr<RSA> tool_rsa(PEM_read_RSA_PUBKEY(tool_out.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(tool_rsa);

  ScopedFILE openssl_out(fopen(out_path_openssl, "rb"));
  ASSERT_TRUE(openssl_out);
  bssl::UniquePtr<RSA> openssl_rsa(PEM_read_RSA_PUBKEY(openssl_out.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(openssl_rsa);
}

// Test PEM to DER conversion (public key with -pubin)
TEST_F(RSAFormatComparisonTest, RSAToolPublicKeyPEMtoDERTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + pub_pem_path + " -pubin -outform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + pub_pem_path + " -pubin -outform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // DER output should be identical
  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test -pubin with -modulus and PEM input
TEST_F(RSAFormatComparisonTest, RSAToolPubinModulusTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + pub_pem_path + " -pubin -modulus -noout > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + pub_pem_path + " -pubin -modulus -noout > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test -pubin with -modulus and DER input
TEST_F(RSAFormatComparisonTest, RSAToolPubinModulusDERInputTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + pub_der_path + " -pubin -inform DER -modulus -noout > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + pub_der_path + " -pubin -inform DER -modulus -noout > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test -inform with modulus
TEST_F(RSAFormatComparisonTest, RSAToolInformDERWithModulusTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_der_path + " -inform DER -modulus -noout > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_der_path + " -inform DER -modulus -noout > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test -pubout with private key PEM input (extract public key)
TEST_F(RSAFormatComparisonTest, RSAToolPuboutFromPrivateKeyPEMTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -pubout -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -pubout -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Verify both outputs are valid public keys
  ScopedFILE tool_out(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out);
  bssl::UniquePtr<RSA> tool_rsa(PEM_read_RSA_PUBKEY(tool_out.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(tool_rsa);

  ScopedFILE openssl_out(fopen(out_path_openssl, "rb"));
  ASSERT_TRUE(openssl_out);
  bssl::UniquePtr<RSA> openssl_rsa(PEM_read_RSA_PUBKEY(openssl_out.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(openssl_rsa);

  // Compare moduli
  const BIGNUM *tool_n = RSA_get0_n(tool_rsa.get());
  const BIGNUM *openssl_n = RSA_get0_n(openssl_rsa.get());
  ASSERT_EQ(BN_cmp(tool_n, openssl_n), 0);
}

// Test -pubout with private key DER input using -inform DER
TEST_F(RSAFormatComparisonTest, RSAToolPuboutFromPrivateKeyDERInputTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_der_path + " -inform DER -pubout -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_der_path + " -inform DER -pubout -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Verify both outputs are valid public keys
  ScopedFILE tool_out(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out);
  bssl::UniquePtr<RSA> tool_rsa(PEM_read_RSA_PUBKEY(tool_out.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(tool_rsa);

  ScopedFILE openssl_out(fopen(out_path_openssl, "rb"));
  ASSERT_TRUE(openssl_out);
  bssl::UniquePtr<RSA> openssl_rsa(PEM_read_RSA_PUBKEY(openssl_out.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(openssl_rsa);

  // Compare moduli
  const BIGNUM *tool_n = RSA_get0_n(tool_rsa.get());
  const BIGNUM *openssl_n = RSA_get0_n(openssl_rsa.get());
  ASSERT_EQ(BN_cmp(tool_n, openssl_n), 0);
}

// Test -pubout with -outform DER (extract public key as DER)
TEST_F(RSAFormatComparisonTest, RSAToolPuboutDEROutputTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -pubout -outform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -pubout -outform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Read DER output and verify it's valid
  ScopedFILE tool_out(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out);
  bssl::UniquePtr<RSA> tool_rsa(d2i_RSA_PUBKEY_fp(tool_out.get(), nullptr));
  ASSERT_TRUE(tool_rsa);

  ScopedFILE openssl_out(fopen(out_path_openssl, "rb"));
  ASSERT_TRUE(openssl_out);
  bssl::UniquePtr<RSA> openssl_rsa(d2i_RSA_PUBKEY_fp(openssl_out.get(), nullptr));
  ASSERT_TRUE(openssl_rsa);

  // Compare file contents should be identical for DER
  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test -pubout with -inform DER and -outform DER (DER private to DER public)
TEST_F(RSAFormatComparisonTest, RSAToolPuboutDERtoDERTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_der_path + " -inform DER -pubout -outform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_der_path + " -inform DER -pubout -outform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // DER output should be identical
  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test -pubout with -modulus
TEST_F(RSAFormatComparisonTest, RSAToolPuboutWithModulusTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -pubout -modulus -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -pubout -modulus -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Read output files and verify they contain modulus and public key
  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);

  // Both should contain "Modulus=" at the start
  ASSERT_TRUE(tool_output_str.find("Modulus=") != std::string::npos);
  ASSERT_TRUE(openssl_output_str.find("Modulus=") != std::string::npos);

  trim(tool_output_str);
  ASSERT_TRUE(CheckBoundaries(tool_output_str, MODULUS, PUBLIC_END, MODULUS, PUBLIC_END));
  trim(openssl_output_str);
  ASSERT_TRUE(CheckBoundaries(openssl_output_str, MODULUS, PUBLIC_END, MODULUS, PUBLIC_END));
}

// Test -pubout with -modulus and -noout (only modulus from private key)
TEST_F(RSAFormatComparisonTest, RSAToolPuboutWithModulusNooutTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -pubout -modulus -noout > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -pubout -modulus -noout > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test -pubout with DER to PEM conversion
TEST_F(RSAFormatComparisonTest, RSAToolPuboutDERtoPEMTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_der_path + " -inform DER -pubout -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_der_path + " -inform DER -pubout -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Verify PEM output with public key boundaries
  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  trim(tool_output_str);
  ASSERT_TRUE(tool_output_str.find(PUBLIC_BEGIN) != std::string::npos || tool_output_str.find(RSA_PUBLIC_BEGIN) != std::string::npos);
  trim(openssl_output_str);
  ASSERT_TRUE(openssl_output_str.find(PUBLIC_BEGIN) != std::string::npos || openssl_output_str.find(RSA_PUBLIC_BEGIN) != std::string::npos);
}

// Test -pubout with PEM to DER conversion
TEST_F(RSAFormatComparisonTest, RSAToolPuboutPEMtoDERTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -pubout -outform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -pubout -outform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // DER output should be identical
  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test modulus output with -outform DER (should still output modulus as text)
TEST_F(RSAFormatComparisonTest, RSAToolModulusWithOutformDERTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -modulus -outform DER -noout > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -modulus -outform DER -noout > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Modulus output should be identical regardless of outform when using -noout
  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test modulus with -inform DER and -outform DER, writing key to file
TEST_F(RSAFormatComparisonTest, RSAToolModulusInformOutformDERTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_der_path + " -inform DER -modulus -outform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_der_path + " -inform DER -modulus -outform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);
}

// Test modulus with public key and various format combinations
TEST_F(RSAFormatComparisonTest, RSAToolPubinModulusInformDERTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + pub_der_path + " -pubin -inform DER -modulus -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + pub_der_path + " -pubin -inform DER -modulus -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Read output files and verify they contain modulus and public key
  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);

  // Both should contain "Modulus=" at the start
  ASSERT_TRUE(tool_output_str.find("Modulus=") != std::string::npos);
  ASSERT_TRUE(openssl_output_str.find("Modulus=") != std::string::npos);
}

// Test modulus output to file (not stdout) with PEM input
TEST_F(RSAFormatComparisonTest, RSAToolModulusToFileTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -modulus -out " + out_path_tool + " -noout";
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -modulus -out " + out_path_openssl + " -noout";

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Read files directly - they should contain only the modulus
  tool_output_str = ReadFileToString(out_path_tool);
  openssl_output_str = ReadFileToString(out_path_openssl);
  trim(tool_output_str);
  trim(openssl_output_str);
  ASSERT_EQ(tool_output_str, openssl_output_str);
  ASSERT_TRUE(tool_output_str.find("Modulus=") == 0);
}

// Test modulus with -pubout and -outform DER
TEST_F(RSAFormatComparisonTest, RSAToolModulusPuboutOutformDERTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -pubout -modulus -outform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -pubout -modulus -outform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);
}

// Test case-insensitive -inform option (pem, Pem, PEM)
TEST_F(RSAFormatComparisonTest, RSAToolInformCaseInsensitiveTest) {
  std::vector<std::string> formats = {"pem", "Pem", "PEM"};

  for (const auto& format : formats) {
    std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -inform " + format + " -out " + out_path_tool;
    std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -out " + out_path_openssl;

    RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

    // Verify output is valid
    ScopedFILE tool_out(fopen(out_path_tool, "rb"));
    ASSERT_TRUE(tool_out);
    bssl::UniquePtr<RSA> tool_rsa(PEM_read_RSAPrivateKey(tool_out.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(tool_rsa);
  }
}

// Test case-insensitive -inform DER option (der, Der, DER)
TEST_F(RSAFormatComparisonTest, RSAToolInformDERCaseInsensitiveTest) {
  std::vector<std::string> formats = {"der", "Der", "DER"};

  for (const auto& format : formats) {
    std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_der_path + " -inform " + format + " -out " + out_path_tool;
    std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_der_path + " -inform DER -out " + out_path_openssl;

    RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

    // Verify output is valid
    ScopedFILE tool_out(fopen(out_path_tool, "rb"));
    ASSERT_TRUE(tool_out);
    bssl::UniquePtr<RSA> tool_rsa(PEM_read_RSAPrivateKey(tool_out.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(tool_rsa);
  }
}

// Test case-insensitive -outform option (pem, Pem, PEM)
TEST_F(RSAFormatComparisonTest, RSAToolOutformCaseInsensitiveTest) {
  std::vector<std::string> formats = {"pem", "Pem", "PEM"};

  for (const auto& format : formats) {
    std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -outform " + format + " -out " + out_path_tool;
    std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -out " + out_path_openssl;

    RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

    // Verify output is valid PEM
    tool_output_str = ReadFileToString(out_path_tool);
    trim(tool_output_str);
    ASSERT_TRUE(CheckBoundaries(tool_output_str, RSA_BEGIN, RSA_END, BEGIN, END));
  }
}

// Test case-insensitive -outform DER option (der, Der, DER)
TEST_F(RSAFormatComparisonTest, RSAToolOutformDERCaseInsensitiveTest) {
  std::vector<std::string> formats = {"der", "Der", "DER"};

  for (const auto& format : formats) {
    std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -outform " + format + " -out " + out_path_tool;
    std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -outform DER -out " + out_path_openssl;

    RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

    // Verify output is valid DER
    ScopedFILE tool_out(fopen(out_path_tool, "rb"));
    ASSERT_TRUE(tool_out);
    bssl::UniquePtr<EVP_PKEY> tool_pkey(d2i_PrivateKey_fp(tool_out.get(), nullptr));
    ASSERT_TRUE(tool_pkey);
  }
}

// Test case-insensitive formats with -pubin
TEST_F(RSAFormatComparisonTest, RSAToolPubinCaseInsensitiveTest) {
  std::vector<std::string> inform_formats = {"der", "Der", "DER"};
  std::vector<std::string> outform_formats = {"pem", "Pem", "PEM"};

  for (const auto& inform : inform_formats) {
    for (const auto& outform : outform_formats) {
      std::string tool_command = std::string(tool_executable_path) + " rsa -in " + pub_der_path + " -pubin -inform " + inform + " -outform " + outform + " -out " + out_path_tool;
      std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + pub_der_path + " -pubin -inform DER -out " + out_path_openssl;

      RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

      // Verify output is valid public key
      ScopedFILE tool_out(fopen(out_path_tool, "rb"));
      ASSERT_TRUE(tool_out);
      bssl::UniquePtr<RSA> tool_rsa(PEM_read_RSA_PUBKEY(tool_out.get(), nullptr, nullptr, nullptr));
      ASSERT_TRUE(tool_rsa);
    }
  }
}

// Test various parameter orderings with -modulus and -noout
TEST_F(RSAFormatComparisonTest, RSAToolParameterOrderingTest1) {
  // Test: -modulus before -noout
  std::string tool_command1 = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -modulus -noout > " + out_path_tool;
  std::string openssl_command1 = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -modulus -noout > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command1, openssl_command1, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);
  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test various parameter orderings with -out before other flags
TEST_F(RSAFormatComparisonTest, RSAToolParameterOrderingTest2) {
  // Test: -out before -pubout
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -out " + out_path_tool + " -pubout";
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -out " + out_path_openssl + " -pubout";

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Verify both are valid public keys
  ScopedFILE tool_out(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out);
  bssl::UniquePtr<RSA> tool_rsa(PEM_read_RSA_PUBKEY(tool_out.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(tool_rsa);
}

// Test parameter ordering with all format flags
TEST_F(RSAFormatComparisonTest, RSAToolParameterOrderingTest3) {
  // Test: -outform before -inform
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -outform DER -inform PEM -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -inform PEM -outform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Verify DER output
  ScopedFILE tool_out(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out);
  bssl::UniquePtr<EVP_PKEY> tool_pkey(d2i_PrivateKey_fp(tool_out.get(), nullptr));
  ASSERT_TRUE(tool_pkey);
}

// Test stdout output with modulus (no -out flag)
TEST_F(RSAFormatComparisonTest, RSAToolStdoutWithModulusTest) {
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + priv_pem_path + " -modulus > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -modulus > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Both should contain modulus and key
  tool_output_str = ReadFileToString(out_path_tool);
  ASSERT_TRUE(tool_output_str.find("Modulus=") != std::string::npos);
  trim(tool_output_str);
  ASSERT_TRUE(CheckBoundaries(tool_output_str, MODULUS, RSA_END, MODULUS, END));
}

// Test complex parameter ordering with all flags
TEST_F(RSAFormatComparisonTest, RSAToolComplexParameterOrderingTest) {
  // Test: flags in unusual order
  std::string tool_command = std::string(tool_executable_path) + " rsa -modulus -in " + priv_der_path + " -pubout -inform DER -out " + out_path_tool + " -outform PEM";
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_der_path + " -inform DER -pubout -modulus -outform PEM -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Verify output contains both modulus and public key
  tool_output_str = ReadFileToString(out_path_tool);
  ASSERT_TRUE(tool_output_str.find("Modulus=") != std::string::npos);
  trim(tool_output_str);
  ASSERT_TRUE(CheckBoundaries(tool_output_str, MODULUS, PUBLIC_END, MODULUS, PUBLIC_END));
}

// Test -in flag at different positions
TEST_F(RSAFormatComparisonTest, RSAToolInFlagPositionTest) {
  // Test: -in at the end
  std::string tool_command = std::string(tool_executable_path) + " rsa -pubout -out " + out_path_tool + " -in " + priv_pem_path;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + priv_pem_path + " -pubout -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Verify output is valid public key
  ScopedFILE tool_out(fopen(out_path_tool, "rb"));
  ASSERT_TRUE(tool_out);
  bssl::UniquePtr<RSA> tool_rsa(PEM_read_RSA_PUBKEY(tool_out.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(tool_rsa);
}

// Test -pubin with -modulus in different order
TEST_F(RSAFormatComparisonTest, RSAToolPubinModulusOrderingTest) {
  // Test: -pubin after -modulus
  std::string tool_command = std::string(tool_executable_path) + " rsa -in " + pub_pem_path + " -modulus -pubin -noout > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " rsa -in " + pub_pem_path + " -pubin -modulus -noout > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

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
