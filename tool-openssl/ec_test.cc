// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/ec.h>
#include <openssl/pem.h>
#include "../crypto/test/test_util.h"
#include "internal.h"
#include "test_util.h"

static EC_KEY *CreateTestECKey() {
  bssl::UniquePtr<EC_KEY> ec_key(
      EC_KEY_new_by_curve_name(NID_X9_62_prime256v1));
  if (!ec_key || !EC_KEY_generate_key(ec_key.get())) {
    return nullptr;
  }
  return ec_key.release();
}

class ECTest : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(pem_key_path), 0u);
    ASSERT_GT(createTempFILEpath(der_key_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);

    tool_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");

    if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
      ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);

      // Use OpenSSL to generate test keys for better cross-compatibility
      std::string pem_cmd = std::string(openssl_executable_path) +
                            " ecparam -genkey -name prime256v1 -out " +
                            pem_key_path;
      std::string der_cmd = std::string(openssl_executable_path) +
                            " ecparam -genkey -name prime256v1 | " +
                            std::string(openssl_executable_path) +
                            " ec -outform DER -out " + der_key_path;

      ASSERT_EQ(system(pem_cmd.c_str()), 0)
          << "Failed to generate PEM key with OpenSSL";
      ASSERT_EQ(system(der_cmd.c_str()), 0)
          << "Failed to generate DER key with OpenSSL";
    } else {
      // Fallback to AWS-LC key generation
      ec_key.reset(CreateTestECKey());
      ASSERT_TRUE(ec_key);

      bssl::UniquePtr<BIO> pem_bio(BIO_new_file(pem_key_path, "wb"));
      ASSERT_TRUE(pem_bio);
      ASSERT_TRUE(PEM_write_bio_ECPrivateKey(
          pem_bio.get(), ec_key.get(), nullptr, nullptr, 0, nullptr, nullptr));
      BIO_flush(pem_bio.get());

      bssl::UniquePtr<BIO> der_bio(BIO_new_file(der_key_path, "wb"));
      ASSERT_TRUE(der_bio);
      ASSERT_TRUE(i2d_ECPrivateKey_bio(der_bio.get(), ec_key.get()));
      BIO_flush(der_bio.get());
    }
  }

  void TearDown() override {
    RemoveFile(pem_key_path);
    RemoveFile(der_key_path);
    RemoveFile(out_path);
    if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
      RemoveFile(out_path_openssl);
    }
  }

  char pem_key_path[PATH_MAX];
  char der_key_path[PATH_MAX];
  char out_path[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  const char *tool_executable_path;
  const char *openssl_executable_path;
  bssl::UniquePtr<EC_KEY> ec_key;
};

TEST_F(ECTest, ReadPEMOutputPEM) {
  args_list_t args = {"-in", pem_key_path, "-out", out_path};
  ASSERT_TRUE(ecTool(args));

  bssl::UniquePtr<BIO> out_bio(BIO_new_file(out_path, "rb"));
  ASSERT_TRUE(out_bio);
  bssl::UniquePtr<EC_KEY> parsed_key(
      PEM_read_bio_ECPrivateKey(out_bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(parsed_key);
}

TEST_F(ECTest, ReadPEMOutputDER) {
  args_list_t args = {"-in", pem_key_path, "-outform", "DER", "-out", out_path};
  ASSERT_TRUE(ecTool(args));

  bssl::UniquePtr<BIO> out_bio(BIO_new_file(out_path, "rb"));
  ASSERT_TRUE(out_bio);
  bssl::UniquePtr<EC_KEY> parsed_key(
      d2i_ECPrivateKey_bio(out_bio.get(), nullptr));
  ASSERT_TRUE(parsed_key);
}

TEST_F(ECTest, ReadDEROutputPEM) {
  args_list_t args = {"-in", der_key_path, "-inform", "DER", "-out", out_path};
  ASSERT_TRUE(ecTool(args));

  bssl::UniquePtr<BIO> out_bio(BIO_new_file(out_path, "rb"));
  ASSERT_TRUE(out_bio);
  bssl::UniquePtr<EC_KEY> parsed_key(
      PEM_read_bio_ECPrivateKey(out_bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(parsed_key);
}

TEST_F(ECTest, ReadDEROutputDER) {
  args_list_t args = {"-in",      der_key_path, "-inform", "DER",
                      "-outform", "DER",        "-out",    out_path};
  ASSERT_TRUE(ecTool(args));

  bssl::UniquePtr<BIO> out_bio(BIO_new_file(out_path, "rb"));
  ASSERT_TRUE(out_bio);
  bssl::UniquePtr<EC_KEY> parsed_key(
      d2i_ECPrivateKey_bio(out_bio.get(), nullptr));
  ASSERT_TRUE(parsed_key);
}

TEST_F(ECTest, PublicKeyExtractionPEM) {
  args_list_t args = {"-in", pem_key_path, "-pubout", "-out", out_path};
  ASSERT_TRUE(ecTool(args));

  bssl::UniquePtr<BIO> out_bio(BIO_new_file(out_path, "rb"));
  ASSERT_TRUE(out_bio);
  bssl::UniquePtr<EC_KEY> parsed_key(
      PEM_read_bio_EC_PUBKEY(out_bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(parsed_key);
}

TEST_F(ECTest, PublicKeyExtractionDER) {
  args_list_t args = {"-in",      der_key_path, "-inform", "DER",   "-pubout",
                      "-outform", "DER",        "-out",    out_path};
  ASSERT_TRUE(ecTool(args));

  bssl::UniquePtr<BIO> out_bio(BIO_new_file(out_path, "rb"));
  ASSERT_TRUE(out_bio);
  bssl::UniquePtr<EC_KEY> parsed_key(d2i_EC_PUBKEY_bio(out_bio.get(), nullptr));
  ASSERT_TRUE(parsed_key);
}

TEST_F(ECTest, RoundTripPEMtoDERtoPEM) {
  char temp_der[PATH_MAX];
  ASSERT_GT(createTempFILEpath(temp_der), 0u);

  // Load original key for comparison
  bssl::UniquePtr<BIO> orig_bio(BIO_new_file(pem_key_path, "rb"));
  ASSERT_TRUE(orig_bio);
  bssl::UniquePtr<EC_KEY> orig_key(
      PEM_read_bio_ECPrivateKey(orig_bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(orig_key);

  args_list_t args1 = {"-in", pem_key_path, "-outform",
                       "DER", "-out",       temp_der};
  ASSERT_TRUE(ecTool(args1));

  args_list_t args2 = {"-in", temp_der, "-inform", "DER", "-out", out_path};
  ASSERT_TRUE(ecTool(args2));

  bssl::UniquePtr<BIO> out_bio(BIO_new_file(out_path, "rb"));
  ASSERT_TRUE(out_bio);
  bssl::UniquePtr<EC_KEY> parsed_key(
      PEM_read_bio_ECPrivateKey(out_bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(parsed_key);

  // Validate key content matches
  const BIGNUM *orig_priv = EC_KEY_get0_private_key(orig_key.get());
  const BIGNUM *parsed_priv = EC_KEY_get0_private_key(parsed_key.get());
  ASSERT_EQ(BN_cmp(orig_priv, parsed_priv), 0);

  RemoveFile(temp_der);
}

TEST_F(ECTest, RoundTripDERtoPEMtoDER) {
  char temp_pem[PATH_MAX];
  ASSERT_GT(createTempFILEpath(temp_pem), 0u);

  // Load original key for comparison
  bssl::UniquePtr<BIO> orig_bio(BIO_new_file(der_key_path, "rb"));
  ASSERT_TRUE(orig_bio);
  bssl::UniquePtr<EC_KEY> orig_key(
      d2i_ECPrivateKey_bio(orig_bio.get(), nullptr));
  ASSERT_TRUE(orig_key);

  args_list_t args1 = {"-in", der_key_path, "-inform", "DER", "-out", temp_pem};
  ASSERT_TRUE(ecTool(args1));

  args_list_t args2 = {"-in", temp_pem, "-outform", "DER", "-out", out_path};
  ASSERT_TRUE(ecTool(args2));

  bssl::UniquePtr<BIO> out_bio(BIO_new_file(out_path, "rb"));
  ASSERT_TRUE(out_bio);
  bssl::UniquePtr<EC_KEY> parsed_key(
      d2i_ECPrivateKey_bio(out_bio.get(), nullptr));
  ASSERT_TRUE(parsed_key);

  // Validate key content matches
  const BIGNUM *orig_priv = EC_KEY_get0_private_key(orig_key.get());
  const BIGNUM *parsed_priv = EC_KEY_get0_private_key(parsed_key.get());
  ASSERT_EQ(BN_cmp(orig_priv, parsed_priv), 0);

  RemoveFile(temp_pem);
}

TEST_F(ECTest, HelpOption) {
  args_list_t args = {"-help"};
  ASSERT_TRUE(ecTool(args));
}

TEST_F(ECTest, InvalidInputFile) {
  args_list_t args = {"-in", "/nonexistent/file.pem", "-out", out_path};
  ASSERT_FALSE(ecTool(args));
}

TEST_F(ECTest, InvalidOutputPath) {
  args_list_t args = {"-in", pem_key_path, "-out",
                      "/nonexistent/dir/output.pem"};
  ASSERT_FALSE(ecTool(args));
}

TEST_F(ECTest, CompareWithOpenSSLPEMOutput) {
  if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
    GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH "
                    "environment variables are not set";
  }

  std::string tool_cmd = std::string(tool_executable_path) + " ec -in " +
                         pem_key_path + " -out " + out_path;
  std::string openssl_cmd = std::string(openssl_executable_path) + " ec -in " +
                            pem_key_path + " -out " + out_path_openssl;

  ASSERT_EQ(system(tool_cmd.c_str()), 0);
  ASSERT_EQ(system(openssl_cmd.c_str()), 0);

  bssl::UniquePtr<BIO> tool_bio(BIO_new_file(out_path, "rb"));
  bssl::UniquePtr<BIO> openssl_bio(BIO_new_file(out_path_openssl, "rb"));
  ASSERT_TRUE(tool_bio);
  ASSERT_TRUE(openssl_bio);

  bssl::UniquePtr<EC_KEY> tool_key(
      PEM_read_bio_ECPrivateKey(tool_bio.get(), nullptr, nullptr, nullptr));
  bssl::UniquePtr<EC_KEY> openssl_key(
      PEM_read_bio_ECPrivateKey(openssl_bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(tool_key);
  ASSERT_TRUE(openssl_key);
}

TEST_F(ECTest, CompareWithOpenSSLDEROutput) {
  if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
    GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH "
                    "environment variables are not set";
  }

  std::string tool_cmd = std::string(tool_executable_path) + " ec -in " +
                         pem_key_path + " -outform DER -out " + out_path;
  std::string openssl_cmd = std::string(openssl_executable_path) + " ec -in " +
                            pem_key_path + " -outform DER -out " +
                            out_path_openssl;

  ASSERT_EQ(system(tool_cmd.c_str()), 0);
  ASSERT_EQ(system(openssl_cmd.c_str()), 0);

  bssl::UniquePtr<BIO> tool_bio(BIO_new_file(out_path, "rb"));
  bssl::UniquePtr<BIO> openssl_bio(BIO_new_file(out_path_openssl, "rb"));
  ASSERT_TRUE(tool_bio);
  ASSERT_TRUE(openssl_bio);

  bssl::UniquePtr<EC_KEY> tool_key(
      d2i_ECPrivateKey_bio(tool_bio.get(), nullptr));
  bssl::UniquePtr<EC_KEY> openssl_key(
      d2i_ECPrivateKey_bio(openssl_bio.get(), nullptr));
  ASSERT_TRUE(tool_key);
  ASSERT_TRUE(openssl_key);
}
