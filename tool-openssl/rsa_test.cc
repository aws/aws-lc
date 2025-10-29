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
