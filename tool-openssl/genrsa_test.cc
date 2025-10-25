// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/bio.h>
#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <sys/stat.h>
#include <cstdio>
#include <string>
#include "../crypto/test/test_util.h"
#include "internal.h"
#include "test_util.h"


const std::vector<unsigned> kStandardKeySizes = {1024, 2048, 3072, 4096};

struct CipherTestCase {
  const char* cipher_flag;    // "-aes128", "-des3", etc.
  const char* cipher_name;    // "AES-128-CBC", "DES3-CBC", etc.
  bool test_openssl_compat;   // whether to test OpenSSL compatibility
};

static const CipherTestCase kCipherTestCases[] = {
  {"-des3", "DES3-CBC", true},
  {"-aes128", "AES-128-CBC", true},
  {"-aes192", "AES-192-CBC", true},
  {"-aes256", "AES-256-CBC", true},
  {"-des", "DES-CBC", true},
};


class GenRSATestBase : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u)
        << "Failed to create temporary file path for tool output";
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u)
        << "Failed to create temporary file path for OpenSSL output";

    awslc_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
  }

  void TearDown() override {
    RemoveFile(out_path_tool);
    RemoveFile(out_path_openssl);
  }

  bool ValidateKeyFile(const char *path, unsigned expected_bits = 0) {
    if (!path) {
      ADD_FAILURE() << "Path parameter is null";
      return false;
    }

    bssl::UniquePtr<BIO> bio(BIO_new_file(path, "rb"));
    if (!bio) {
      ADD_FAILURE() << "Failed to open key file: " << path;
      return false;
    }

    bssl::UniquePtr<RSA> rsa(
        PEM_read_bio_RSAPrivateKey(bio.get(), nullptr, nullptr, nullptr));
    if (!rsa) {
      ADD_FAILURE() << "Failed to parse RSA key from PEM file";
      return false;
    }

    if (RSA_check_key(rsa.get()) != 1) {
      ADD_FAILURE() << "RSA key failed consistency check";
      return false;
    }

    if (expected_bits > 0) {
      unsigned actual_bits = RSA_bits(rsa.get());
      if (actual_bits != expected_bits) {
        ADD_FAILURE() << "Key size mismatch. Expected: " << expected_bits
                     << " bits, Got: " << actual_bits << " bits";
        return false;
      }
    }

    return true;
  }

  bool ValidateEncryptedKeyFile(const char *path, const char *password, unsigned expected_bits = 0) {
    if (!path) {
      ADD_FAILURE() << "Path parameter is null";
      return false;
    }

    if (!password) {
      ADD_FAILURE() << "Password parameter is null";
      return false;
    }

    bssl::UniquePtr<BIO> bio(BIO_new_file(path, "rb"));
    if (!bio) {
      ADD_FAILURE() << "Failed to open encrypted key file: " << path;
      return false;
    }

    bssl::UniquePtr<RSA> rsa(
        PEM_read_bio_RSAPrivateKey(bio.get(), nullptr, nullptr, 
                                  const_cast<char*>(password)));
    if (!rsa) {
      ADD_FAILURE() << "Failed to parse encrypted RSA key from PEM file";
      return false;
    }

    if (RSA_check_key(rsa.get()) != 1) {
      ADD_FAILURE() << "Encrypted RSA key failed consistency check";
      return false;
    }

    if (expected_bits > 0) {
      unsigned actual_bits = RSA_bits(rsa.get());
      if (actual_bits != expected_bits) {
        ADD_FAILURE() << "Key size mismatch. Expected: " << expected_bits
                     << " bits, Got: " << actual_bits << " bits";
        return false;
      }
    }

    return true;
  }

  bool GenerateKey(unsigned key_size, const char *output_path = nullptr) {
    args_list_t args;
    if (output_path) {
      args = {"-out", output_path, std::to_string(key_size)};
    } else {
      args = {std::to_string(key_size)};
    }
    return genrsaTool(args);
  }

  bool HasCrossCompatibilityTools() {
    return awslc_executable_path != nullptr &&
           openssl_executable_path != nullptr;
  }

  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  const char *awslc_executable_path = nullptr;
  const char *openssl_executable_path = nullptr;
};


class GenRSATest : public GenRSATestBase {};


class GenRSAParamTest : public GenRSATestBase,
                        public ::testing::WithParamInterface<unsigned> {};


class GenRSACipherParamTest : public GenRSATestBase,
                              public ::testing::WithParamInterface<CipherTestCase> {};


TEST_P(GenRSAParamTest, GeneratesKeyFile) {
  unsigned key_size = GetParam();
  
  // FIPS builds require 2048-bit minimum - check both compile-time and runtime
  bool is_fips = false;
#if defined(BORINGSSL_FIPS)
  is_fips = true;
#endif
  is_fips = is_fips || FIPS_mode();
  
  if (is_fips && key_size < 2048) {
    GTEST_SKIP() << "Skipping " << key_size << "-bit key test in FIPS build/mode (minimum 2048 bits required)";
  }
  
  EXPECT_TRUE(GenerateKey(key_size, out_path_tool)) << "Key generation failed";
  EXPECT_TRUE(ValidateKeyFile(out_path_tool, key_size))
      << "Generated key file validation failed";
}


TEST_P(GenRSAParamTest, OpenSSLCompatibility) {
  unsigned key_size = GetParam();
  
  // FIPS builds require 2048-bit minimum - check both compile-time and runtime
  bool is_fips = false;
#if defined(BORINGSSL_FIPS)
  is_fips = true;
#endif
  is_fips = is_fips || FIPS_mode();
  
  if (is_fips && key_size < 2048) {
    GTEST_SKIP() << "Skipping " << key_size << "-bit key test in FIPS build/mode (minimum 2048 bits required)";
  }
  
  if (!HasCrossCompatibilityTools()) {
    GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH "
                    "environment variables are not set";
    return;
  }

  EXPECT_TRUE(GenerateKey(key_size, out_path_tool))
      << "AWS-LC key generation failed";

  std::string verify_cmd = std::string(openssl_executable_path) + " rsa -in " +
                           out_path_tool + " -check -noout";
  EXPECT_EQ(system(verify_cmd.c_str()), 0) << "OpenSSL verification failed";
}

INSTANTIATE_TEST_SUITE_P(StandardKeySizes, GenRSAParamTest,
                         ::testing::ValuesIn(kStandardKeySizes));

TEST_P(GenRSACipherParamTest, EncryptedKeyGeneration) {
  const CipherTestCase& cipher_test = GetParam();
  
  args_list_t args{cipher_test.cipher_flag, "-passout", "pass:testpassword", "-out", out_path_tool, "2048"};
  EXPECT_TRUE(genrsaTool(args)) << cipher_test.cipher_name << " encrypted key generation should work";
  EXPECT_TRUE(ValidateEncryptedKeyFile(out_path_tool, "testpassword"))
      << cipher_test.cipher_name << " encrypted key should be valid";
}

TEST_P(GenRSACipherParamTest, OpenSSLCompatibility) {
  const CipherTestCase& cipher_test = GetParam();
  
  if (!cipher_test.test_openssl_compat) {
    GTEST_SKIP() << "OpenSSL compatibility test disabled for " << cipher_test.cipher_name;
  }
  
  if (!HasCrossCompatibilityTools()) {
    GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH "
                    "environment variables are not set";
    return;
  }

  args_list_t args{cipher_test.cipher_flag, "-passout", "pass:testpassword", "-out", out_path_tool, "2048"};
  EXPECT_TRUE(genrsaTool(args)) << "AWS-LC " << cipher_test.cipher_name << " key generation failed";

  std::string verify_cmd = std::string(openssl_executable_path) + 
                         " rsa -in " + out_path_tool + 
                         " -passin pass:testpassword -check -noout";
  EXPECT_EQ(system(verify_cmd.c_str()), 0) << "OpenSSL verification of AWS-LC " << cipher_test.cipher_name << " key failed";
}

INSTANTIATE_TEST_SUITE_P(AllCiphers, GenRSACipherParamTest,
                         ::testing::ValuesIn(kCipherTestCases));

TEST_F(GenRSATest, DefaultKeyGeneration) {
  args_list_t args{"-out", out_path_tool};
  EXPECT_TRUE(genrsaTool(args)) << "Default key generation failed";
  EXPECT_TRUE(ValidateKeyFile(out_path_tool))
      << "Default key file validation failed";
}

TEST_F(GenRSATest, HelpOption) {
  args_list_t args{"-help"};
  EXPECT_TRUE(genrsaTool(args)) << "Help command failed";
}

TEST_F(GenRSATest, StdoutOutput) {
  // This test verifies the CLI can output to stdout
  // We can't easily capture stdout in this test framework,
  // but we can verify the command succeeds
  EXPECT_TRUE(GenerateKey(2048)) << "Stdout key generation failed";
}

TEST_F(GenRSATest, FileOutput) {
  // Test file output
  args_list_t file_args{"-out", out_path_tool, "2048"};
  EXPECT_TRUE(genrsaTool(file_args)) << "File output failed";
  EXPECT_TRUE(ValidateKeyFile(out_path_tool))
      << "File output validation failed";
}

TEST_F(GenRSATest, ArgumentParsingErrors) {
  // Test incorrect argument order
  {
    args_list_t args{"2048", "-out", out_path_tool};
    EXPECT_FALSE(genrsaTool(args))
        << "Command should fail with incorrect argument order";
  }

  // Test invalid key size
  {
    args_list_t args{"-out", out_path_tool, "invalid"};
    EXPECT_FALSE(genrsaTool(args))
        << "Command should fail with invalid key size";
  }

  // Test zero key size
  {
    args_list_t args{"-out", out_path_tool, "0"};
    EXPECT_FALSE(genrsaTool(args)) << "Command should fail with zero key size";
  }
}

TEST_F(GenRSATest, FileIOErrors) {
  // Test invalid output path
  {
    args_list_t args{"-out", "/nonexistent/directory/key.pem", "2048"};
    EXPECT_FALSE(genrsaTool(args))
        << "Command should fail with invalid output path";
  }
}

TEST_F(GenRSATest, ArgumentValidation) {
  // Test help takes precedence
  {
    args_list_t args{"-help", "-out", out_path_tool, "2048"};
    EXPECT_TRUE(genrsaTool(args)) << "Help should work even with other args";
  }
}

TEST_F(GenRSATest, CipherMutualExclusionValidation) {
  // Test that multiple cipher options are rejected
  {
    args_list_t args{"-aes128", "-aes256", "-passout", "pass:testpassword", "-out", out_path_tool, "2048"};
    EXPECT_FALSE(genrsaTool(args)) << "Command should fail with multiple cipher options";
  }

  {
    args_list_t args{"-des", "-des3", "-passout", "pass:testpassword", "-out", out_path_tool, "2048"};
    EXPECT_FALSE(genrsaTool(args)) << "Command should fail with multiple cipher options";
  }

  {
    args_list_t args{"-aes192", "-des3", "-passout", "pass:testpassword", "-out", out_path_tool, "2048"};
    EXPECT_FALSE(genrsaTool(args)) << "Command should fail with multiple cipher options";
  }
}
