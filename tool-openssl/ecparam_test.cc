// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/ec.h>
#include <openssl/pem.h>
#include <openssl/err.h>
#include <openssl/bio.h>
#include "internal.h"
#include "test_util.h"
#include "../crypto/test/test_util.h"

// -------------------- Basic Ecparam Tests ------------------------------------

class EcparamTest : public ::testing::Test {
protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(out_path), 0u);
    ASSERT_GT(createTempFILEpath(key_path), 0u);
  }

  void TearDown() override {
    RemoveFile(out_path);
    RemoveFile(key_path);
  }

  char out_path[PATH_MAX];
  char key_path[PATH_MAX];
};

// Test basic functionality
TEST_F(EcparamTest, EcparamToolBasicTest) {
  args_list_t args = {"-name", "prime256v1"};
  
  EXPECT_TRUE(ecparamTool(args)) << "Basic ecparam functionality failed";
}

TEST_F(EcparamTest, EcparamToolNooutTest) {
  args_list_t args = {"-name", "prime256v1", "-noout"};
  
  EXPECT_TRUE(ecparamTool(args)) << "Ecparam -noout failed";
}

TEST_F(EcparamTest, EcparamToolGenkeyTest) {
  args_list_t args = {"-name", "prime256v1", "-genkey", "-out", out_path};
  
  EXPECT_TRUE(ecparamTool(args)) << "Ecparam -genkey failed";
  
  // Verify key file was created
  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "r"));
  EXPECT_TRUE(bio) << "Key file not created";
}

TEST_F(EcparamTest, EcparamToolConvFormTest) {
  args_list_t args = {"-name", "prime256v1", "-genkey", "-conv_form", "compressed", "-out", out_path};
  
  EXPECT_TRUE(ecparamTool(args)) << "Ecparam -conv_form failed";
}

TEST_F(EcparamTest, EcparamToolOutformTest) {
  args_list_t args = {"-name", "prime256v1", "-outform", "DER", "-out", out_path};
  
  EXPECT_TRUE(ecparamTool(args)) << "Ecparam -outform failed";
}

// Error handling tests
class EcparamOptionUsageErrorsTest : public ::testing::Test {
protected:
  void TestOptionUsageErrors(const args_list_t& args) {
    EXPECT_FALSE(ecparamTool(args));
  }
};

TEST_F(EcparamOptionUsageErrorsTest, InvalidCurveTest) {
  args_list_t args = {"-name", "invalid_curve"};
  TestOptionUsageErrors(args);
}

TEST_F(EcparamOptionUsageErrorsTest, InvalidConvFormTest) {
  args_list_t args = {"-name", "prime256v1", "-conv_form", "invalid"};
  TestOptionUsageErrors(args);
}

TEST_F(EcparamOptionUsageErrorsTest, InvalidOutformTest) {
  args_list_t args = {"-name", "prime256v1", "-outform", "INVALID"};
  TestOptionUsageErrors(args);
}

// -------------------- Ecparam OpenSSL Comparison Tests -----------------------

// Comparison tests cannot run without set up of environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.

class EcparamComparisonTest : public ::testing::Test {
protected:
  void SetUp() override {
    // Skip gtests if env variables not set
    tool_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
    if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
      GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH environment variables are not set";
    }

    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);
    ASSERT_GT(createTempFILEpath(key_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(key_path_openssl), 0u);
  }

  void TearDown() override {
    RemoveFile(out_path_tool);
    RemoveFile(out_path_openssl);
    RemoveFile(key_path_tool);
    RemoveFile(key_path_openssl);
  }

  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  char key_path_tool[PATH_MAX];
  char key_path_openssl[PATH_MAX];
  const char* tool_executable_path;
  const char* openssl_executable_path;
  std::string tool_output_str;
  std::string openssl_output_str;
};

// Test against OpenSSL output "openssl ecparam -name prime256v1"
TEST_F(EcparamComparisonTest, EcparamToolCompareParametersOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " ecparam -name prime256v1 > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " ecparam -name prime256v1 > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl ecparam -name secp384r1"
TEST_F(EcparamComparisonTest, EcparamToolCompareParametersSecp384r1OpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " ecparam -name secp384r1 > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " ecparam -name secp384r1 > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl ecparam -name secp256k1"
TEST_F(EcparamComparisonTest, EcparamToolCompareParametersSecp256k1OpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " ecparam -name secp256k1 > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " ecparam -name secp256k1 > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl ecparam -name prime256v1 -noout"
TEST_F(EcparamComparisonTest, EcparamToolCompareNooutOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " ecparam -name prime256v1 -noout > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " ecparam -name prime256v1 -noout > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  // Both should be empty
  ASSERT_TRUE(tool_output_str.empty());
  ASSERT_TRUE(openssl_output_str.empty());
}

// Test against OpenSSL output "openssl ecparam -name prime256v1 -outform DER"
TEST_F(EcparamComparisonTest, EcparamToolCompareDERFormatOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " ecparam -name prime256v1 -outform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " ecparam -name prime256v1 -outform DER -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl ecparam -name prime256v1 -out file"
TEST_F(EcparamComparisonTest, EcparamToolCompareFileOutputOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " ecparam -name prime256v1 -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " ecparam -name prime256v1 -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test key generation structure (content will differ due to randomness)
TEST_F(EcparamComparisonTest, EcparamToolCompareKeyGenStructureOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " ecparam -name prime256v1 -genkey -out " + key_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " ecparam -name prime256v1 -genkey -out " + key_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, key_path_tool, key_path_openssl, tool_output_str, openssl_output_str);

  // Both files should exist and contain valid EC private keys
  bssl::UniquePtr<BIO> tool_bio(BIO_new_file(key_path_tool, "r"));
  bssl::UniquePtr<BIO> openssl_bio(BIO_new_file(key_path_openssl, "r"));
  ASSERT_TRUE(tool_bio && openssl_bio) << "Key files not created";

  // Parse both keys
  bssl::UniquePtr<EVP_PKEY> tool_pkey(
    PEM_read_bio_PrivateKey(tool_bio.get(), nullptr, nullptr, nullptr));
  bssl::UniquePtr<EVP_PKEY> openssl_pkey(
    PEM_read_bio_PrivateKey(openssl_bio.get(), nullptr, nullptr, nullptr));

  ASSERT_TRUE(tool_pkey && openssl_pkey) << "Failed to parse generated keys";
  ASSERT_EQ(EVP_PKEY_EC, EVP_PKEY_id(tool_pkey.get()));
  ASSERT_EQ(EVP_PKEY_EC, EVP_PKEY_id(openssl_pkey.get()));

  // Both should use the same curve
  EC_KEY* tool_ec = EVP_PKEY_get0_EC_KEY(tool_pkey.get());
  EC_KEY* openssl_ec = EVP_PKEY_get0_EC_KEY(openssl_pkey.get());
  ASSERT_TRUE(tool_ec && openssl_ec);

  const EC_GROUP* tool_group = EC_KEY_get0_group(tool_ec);
  const EC_GROUP* openssl_group = EC_KEY_get0_group(openssl_ec);
  ASSERT_EQ(EC_GROUP_get_curve_name(tool_group), 
            EC_GROUP_get_curve_name(openssl_group));
}

// Test key generation with compressed point format
TEST_F(EcparamComparisonTest, EcparamToolCompareKeyGenCompressedOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " ecparam -name prime256v1 -genkey -conv_form compressed -out " + key_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " ecparam -name prime256v1 -genkey -conv_form compressed -out " + key_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, key_path_tool, key_path_openssl, tool_output_str, openssl_output_str);

  // Both should be valid keys
  bssl::UniquePtr<BIO> tool_bio(BIO_new_file(key_path_tool, "r"));
  bssl::UniquePtr<BIO> openssl_bio(BIO_new_file(key_path_openssl, "r"));
  ASSERT_TRUE(tool_bio && openssl_bio);

  bssl::UniquePtr<EVP_PKEY> tool_pkey(
    PEM_read_bio_PrivateKey(tool_bio.get(), nullptr, nullptr, nullptr));
  bssl::UniquePtr<EVP_PKEY> openssl_pkey(
    PEM_read_bio_PrivateKey(openssl_bio.get(), nullptr, nullptr, nullptr));

  ASSERT_TRUE(tool_pkey && openssl_pkey) << "Failed to parse compressed keys";
  ASSERT_EQ(EVP_PKEY_EC, EVP_PKEY_id(tool_pkey.get()));
  ASSERT_EQ(EVP_PKEY_EC, EVP_PKEY_id(openssl_pkey.get()));
}

// Test key generation with uncompressed point format
TEST_F(EcparamComparisonTest, EcparamToolCompareKeyGenUncompressedOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " ecparam -name secp384r1 -genkey -conv_form uncompressed -out " + key_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " ecparam -name secp384r1 -genkey -conv_form uncompressed -out " + key_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, key_path_tool, key_path_openssl, tool_output_str, openssl_output_str);

  bssl::UniquePtr<BIO> tool_bio(BIO_new_file(key_path_tool, "r"));
  bssl::UniquePtr<BIO> openssl_bio(BIO_new_file(key_path_openssl, "r"));
  ASSERT_TRUE(tool_bio && openssl_bio);

  bssl::UniquePtr<EVP_PKEY> tool_pkey(
    PEM_read_bio_PrivateKey(tool_bio.get(), nullptr, nullptr, nullptr));
  bssl::UniquePtr<EVP_PKEY> openssl_pkey(
    PEM_read_bio_PrivateKey(openssl_bio.get(), nullptr, nullptr, nullptr));

  ASSERT_TRUE(tool_pkey && openssl_pkey) << "Failed to parse uncompressed keys";
}

// Test DER format key generation
TEST_F(EcparamComparisonTest, EcparamToolCompareKeyGenDEROpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " ecparam -name secp256k1 -genkey -outform DER -out " + key_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " ecparam -name secp256k1 -genkey -outform DER -out " + key_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, key_path_tool, key_path_openssl, tool_output_str, openssl_output_str);

  // Both files should exist and be reasonable size for DER keys
  bssl::UniquePtr<BIO> tool_bio(BIO_new_file(key_path_tool, "rb"));
  bssl::UniquePtr<BIO> openssl_bio(BIO_new_file(key_path_openssl, "rb"));
  ASSERT_TRUE(tool_bio && openssl_bio);

  // Check file sizes using BIO
  BIO_seek(tool_bio.get(), 0);
  BIO_seek(openssl_bio.get(), 0);
  
  // Read entire files to check size
  char buffer[1000];
  int tool_size = BIO_read(tool_bio.get(), buffer, sizeof(buffer));
  int openssl_size = BIO_read(openssl_bio.get(), buffer, sizeof(buffer));

  ASSERT_GT(tool_size, 50) << "AWS-LC DER key too small";
  ASSERT_GT(openssl_size, 50) << "OpenSSL DER key too small";
  ASSERT_LT(tool_size, 500) << "AWS-LC DER key too large";
  ASSERT_LT(openssl_size, 500) << "OpenSSL DER key too large";

  // Parse DER keys to verify they're valid
  BIO_seek(tool_bio.get(), 0);
  BIO_seek(openssl_bio.get(), 0);
  bssl::UniquePtr<EVP_PKEY> tool_pkey(d2i_PrivateKey_bio(tool_bio.get(), nullptr));
  bssl::UniquePtr<EVP_PKEY> openssl_pkey(d2i_PrivateKey_bio(openssl_bio.get(), nullptr));

  ASSERT_TRUE(tool_pkey && openssl_pkey) << "Failed to parse DER keys";
  ASSERT_EQ(EVP_PKEY_EC, EVP_PKEY_id(tool_pkey.get()));
  ASSERT_EQ(EVP_PKEY_EC, EVP_PKEY_id(openssl_pkey.get()));
}

// Test combined options
TEST_F(EcparamComparisonTest, EcparamToolCompareCombinedOptionsOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " ecparam -name prime256v1 -genkey -conv_form compressed -outform DER -out " + key_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " ecparam -name prime256v1 -genkey -conv_form compressed -outform DER -out " + key_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, key_path_tool, key_path_openssl, tool_output_str, openssl_output_str);

  // Verify both files exist and contain valid DER keys
  bssl::UniquePtr<BIO> tool_bio(BIO_new_file(key_path_tool, "rb"));
  bssl::UniquePtr<BIO> openssl_bio(BIO_new_file(key_path_openssl, "rb"));
  ASSERT_TRUE(tool_bio && openssl_bio);

  bssl::UniquePtr<EVP_PKEY> tool_pkey(d2i_PrivateKey_bio(tool_bio.get(), nullptr));
  bssl::UniquePtr<EVP_PKEY> openssl_pkey(d2i_PrivateKey_bio(openssl_bio.get(), nullptr));

  ASSERT_TRUE(tool_pkey && openssl_pkey) << "Failed to parse combined option keys";
  ASSERT_EQ(EVP_PKEY_EC, EVP_PKEY_id(tool_pkey.get()));
  ASSERT_EQ(EVP_PKEY_EC, EVP_PKEY_id(openssl_pkey.get()));
}
