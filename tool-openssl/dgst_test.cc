// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "../crypto/test/test_util.h"
#include "internal.h"
#include "test_util.h"

class DgstComparisonTest : public ::testing::Test {
 protected:
  void SetUp() override {
    // Skip gtests if env variables not set
    awslc_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");

    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path_awslc), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);
    ASSERT_GT(createTempFILEpath(sig_path_awslc), 0u);
    ASSERT_GT(createTempFILEpath(sig_path_openssl), 0u);
    ASSERT_GT(createTempFILEpath(key_path), 0u);
    ASSERT_GT(createTempFILEpath(pubkey_path), 0u);
    ASSERT_GT(createTempFILEpath(protected_key_path),
              0u);  // TODO: update this to test passin

    // Create and save a private key in PEM format
    bssl::UniquePtr<EVP_PKEY> pkey(CreateTestKey(2048));
    ASSERT_TRUE(pkey);

    ScopedFILE key_file(fopen(key_path, "wb"));
    ASSERT_TRUE(key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(key_file.get(), pkey.get(), nullptr,
                                     nullptr, 0, nullptr, nullptr));

    // Create a public key file
    ScopedFILE pubkey_file(fopen(pubkey_path, "wb"));
    ASSERT_TRUE(pubkey_file);
    ASSERT_TRUE(PEM_write_PUBKEY(pubkey_file.get(), pkey.get()));

    // Create a test input file with some data
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    const char *test_data = "AWS_LC_TEST_STRING_INPUT";
    ASSERT_EQ(fwrite(test_data, 1, strlen(test_data), in_file.get()),
              strlen(test_data));

    if (awslc_executable_path == nullptr ||
        openssl_executable_path == nullptr) {
      GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH "
                      "environment variables are not set";
    }
  }

  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(out_path_awslc);
    RemoveFile(out_path_openssl);
    RemoveFile(sig_path_awslc);
    RemoveFile(sig_path_openssl);
    RemoveFile(key_path);
    RemoveFile(pubkey_path);
    RemoveFile(protected_key_path);
  }

  char in_path[PATH_MAX];
  char out_path_awslc[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  char sig_path_awslc[PATH_MAX];
  char sig_path_openssl[PATH_MAX];
  char key_path[PATH_MAX];
  char pubkey_path[PATH_MAX];
  char protected_key_path[PATH_MAX];
  const char *awslc_executable_path;
  const char *openssl_executable_path;
  std::string awslc_output_str;
  std::string openssl_output_str;
};

// OpenSSL versions 3.1.0 and later change from "(stdin)= " to "MD5(stdin) ="
std::string GetHash(const std::string &str) {
  size_t pos = str.find('=');
  if (pos == std::string::npos) {
    return "";
  }
  std::string result = str.substr(pos + 1);

  // OpenSSL has inconsistent leading white space
  size_t start = result.find_first_not_of(" ");
  if (start == std::string::npos) {
    return "";
  }

  if (start == 0) {
    return result;
  }

  return result.substr(start);
}

// -------------------- Dgst Options Test ---------------------------
TEST_F(DgstComparisonTest, HMAC) {
  std::string awslc_command = std::string(awslc_executable_path) +
                              " dgst -hmac test_key_string -out " +
                              out_path_awslc + " " + in_path;

  std::string openssl_command = std::string(openssl_executable_path) +
                                " dgst -hmac test_key_string -out " +
                                out_path_openssl + " " + in_path;

  RunCommandsAndCompareOutput(awslc_command, openssl_command, out_path_awslc,
                              out_path_openssl, awslc_output_str,
                              openssl_output_str);

  std::string awslc_hash = GetHash(awslc_output_str);
  std::string openssl_hash = GetHash(openssl_output_str);

  EXPECT_EQ(awslc_hash, openssl_hash);

  // binary output
  awslc_command = std::string(awslc_executable_path) +
                  " dgst -hmac test_key_string -binary -out " + out_path_awslc +
                  " " + in_path;
  openssl_command = std::string(openssl_executable_path) +
                    " dgst -hmac test_key_string -binary -out " +
                    out_path_openssl + " " + in_path;

  RunCommandsAndCompareOutput(awslc_command, openssl_command, out_path_awslc,
                              out_path_openssl, awslc_output_str,
                              openssl_output_str);

  EXPECT_EQ(awslc_output_str, openssl_output_str);
}

TEST_F(DgstComparisonTest, Digest) {
  // default digest
  std::string awslc_command = std::string(awslc_executable_path) +
                              " dgst -out " + out_path_awslc + " " + in_path;

  std::string openssl_command = std::string(openssl_executable_path) +
                                " dgst -out " + out_path_openssl + " " +
                                in_path;

  RunCommandsAndCompareOutput(awslc_command, openssl_command, out_path_awslc,
                              out_path_openssl, awslc_output_str,
                              openssl_output_str);

  std::string awslc_hash = GetHash(awslc_output_str);
  std::string openssl_hash = GetHash(openssl_output_str);

  EXPECT_EQ(awslc_hash, openssl_hash);

  // non-default digest + binary
  awslc_command = std::string(awslc_executable_path) +
                  " dgst -sha1 -binary -out " + out_path_awslc + " " + in_path;
  openssl_command = std::string(openssl_executable_path) +
                    " dgst -sha1 -binary -out " + out_path_openssl + " " +
                    in_path;

  RunCommandsAndCompareOutput(awslc_command, openssl_command, out_path_awslc,
                              out_path_openssl, awslc_output_str,
                              openssl_output_str);

  EXPECT_EQ(awslc_output_str, openssl_output_str);
}

TEST_F(DgstComparisonTest, SignAndVerify) {
  // default binary output
  std::string awslc_command = std::string(awslc_executable_path) +
                              " dgst -sign " + key_path + " -out " +
                              sig_path_awslc + " " + in_path;

  std::string openssl_command = std::string(openssl_executable_path) +
                                " dgst -sign " + key_path + " -out " +
                                sig_path_openssl + " " + in_path;

  RunCommandsAndCompareOutput(awslc_command, openssl_command, sig_path_awslc,
                              sig_path_openssl, awslc_output_str,
                              openssl_output_str);

  EXPECT_EQ(awslc_output_str, openssl_output_str);

  awslc_command = std::string(awslc_executable_path) + " dgst -verify " +
                  pubkey_path + " -signature " + sig_path_awslc +
                  " -keyform PEM -out " + out_path_awslc + " " + in_path;

  openssl_command = std::string(openssl_executable_path) + " dgst -verify " +
                    pubkey_path + " -signature " + sig_path_openssl +
                    " -keyform PEM -out " + out_path_openssl + " " + in_path;

  RunCommandsAndCompareOutput(awslc_command, openssl_command, out_path_awslc,
                              out_path_openssl, awslc_output_str,
                              openssl_output_str);

  EXPECT_EQ(awslc_output_str, openssl_output_str);

  // sigopts
  awslc_command =
      std::string(awslc_executable_path) + " dgst -sign " + key_path +
      " -sigopt rsa_padding_mode:pss -sigopt rsa_pss_saltlen:0 -out " +
      sig_path_awslc + " " + in_path;

  openssl_command =
      std::string(openssl_executable_path) + " dgst -sign " + key_path +
      " -sigopt rsa_padding_mode:pss -sigopt rsa_pss_saltlen:0 -out " +
      sig_path_openssl + " " + in_path;

  RunCommandsAndCompareOutput(awslc_command, openssl_command, sig_path_awslc,
                              sig_path_openssl, awslc_output_str,
                              openssl_output_str);

  EXPECT_EQ(awslc_output_str, openssl_output_str);

  awslc_command =
      std::string(awslc_executable_path) + " dgst -verify " + pubkey_path +
      " -signature " + sig_path_awslc +
      " -sigopt rsa_padding_mode:pss -sigopt rsa_pss_saltlen:0 -out " +
      out_path_awslc + " " + in_path;

  openssl_command =
      std::string(openssl_executable_path) + " dgst -verify " + pubkey_path +
      " -signature " + sig_path_openssl +
      " -sigopt rsa_padding_mode:pss -sigopt rsa_pss_saltlen:0 -out " +
      out_path_openssl + " " + in_path;

  RunCommandsAndCompareOutput(awslc_command, openssl_command, out_path_awslc,
                              out_path_openssl, awslc_output_str,
                              openssl_output_str);

  EXPECT_EQ(awslc_output_str, openssl_output_str);

  // hex output
  awslc_command = std::string(awslc_executable_path) + " dgst -sign " +
                  key_path + " -hex -out " + sig_path_awslc + " " + in_path;

  openssl_command = std::string(openssl_executable_path) + " dgst -sign " +
                    key_path + " -hex -out " + sig_path_openssl + " " + in_path;

  RunCommandsAndCompareOutput(awslc_command, openssl_command, sig_path_awslc,
                              sig_path_openssl, awslc_output_str,
                              openssl_output_str);

  std::string awslc_hash = GetHash(awslc_output_str);
  std::string openssl_hash = GetHash(openssl_output_str);

  EXPECT_EQ(awslc_hash, openssl_hash);
}

class DgstTest : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);
    ASSERT_GT(createTempFILEpath(sig_path), 0u);
    ASSERT_GT(createTempFILEpath(key_path), 0u);
    ASSERT_GT(createTempFILEpath(pubkey_path), 0u);
    ASSERT_GT(createTempFILEpath(protected_key_path), 0u);

    // Create and save a private key in PEM format
    bssl::UniquePtr<EVP_PKEY> pkey(CreateTestKey(2048));
    ASSERT_TRUE(pkey);

    ScopedFILE key_file(fopen(key_path, "wb"));
    ASSERT_TRUE(key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(key_file.get(), pkey.get(), nullptr,
                                     nullptr, 0, nullptr, nullptr));

    // Create a public key file
    ScopedFILE pubkey_file(fopen(pubkey_path, "wb"));
    ASSERT_TRUE(pubkey_file);
    ASSERT_TRUE(PEM_write_PUBKEY(pubkey_file.get(), pkey.get()));

    // Create a test input file with some data
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    const char *test_data = "Test data for signing and verification";
    ASSERT_EQ(fwrite(test_data, 1, strlen(test_data), in_file.get()),
              strlen(test_data));
  }

  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(out_path);
    RemoveFile(sig_path);
    RemoveFile(key_path);
    RemoveFile(pubkey_path);
    RemoveFile(protected_key_path);
  }

  char in_path[PATH_MAX];
  char out_path[PATH_MAX];
  char sig_path[PATH_MAX];
  char key_path[PATH_MAX];
  char pubkey_path[PATH_MAX];
  char protected_key_path[PATH_MAX];
  std::string awslc_output_str;
  std::string openssl_output_str;
};

TEST_F(DgstTest, HMAC) {
  args_list_t args = {"-hmac", "test_key_string", in_path};
  EXPECT_TRUE(dgstTool(args));
}

TEST_F(DgstTest, Sign) {
  args_list_t args = {"-sign", key_path, "-out", sig_path, in_path};
  EXPECT_TRUE(dgstTool(args));
}

TEST_F(DgstTest, Verify) {
  // First create signature
  args_list_t sign_args = {"-sign", key_path, "-out", sig_path, in_path};
  EXPECT_TRUE(dgstTool(sign_args));

  // Then verify
  args_list_t verify_args = {"-verify", pubkey_path, "-signature", sig_path,
                             in_path};
  EXPECT_TRUE(dgstTool(verify_args));
}

TEST_F(DgstTest, DigestSHA256) {
  std::ofstream ofs(in_path);
  ofs << "test data";
  ofs.close();

  args_list_t args = {"-sha256", in_path};
  EXPECT_TRUE(dgstTool(args));
}

TEST_F(DgstTest, DigestSHA1) {
  std::ofstream ofs(in_path);
  ofs << "test data";
  ofs.close();

  args_list_t args = {"-sha1", in_path};
  EXPECT_TRUE(dgstTool(args));
}

TEST_F(DgstTest, FileInput) {
  // Single file input
  args_list_t single_args = {in_path};
  EXPECT_TRUE(dgstTool(single_args));

  // Multiple file inputs
  char in_path2[PATH_MAX];
  ASSERT_GT(createTempFILEpath(in_path2), 0u);
  std::ofstream ofs2(in_path2);
  ofs2 << "AWS_LC_TEST_STRING_INPUT_2";
  ofs2.close();

  args_list_t multi_args = {in_path, in_path2};
  EXPECT_TRUE(dgstTool(multi_args));

  RemoveFile(in_path2);
}

class DgstOptionUsageErrorsTest : public DgstTest {
 protected:
  void TestOptionUsageErrors(const std::vector<std::string> &args) {
    args_list_t c_args;
    for (const auto &arg : args) {
      c_args.push_back(arg.c_str());
    }
    bool result = dgstTool(c_args);
    ASSERT_FALSE(result);
  }
};

TEST_F(DgstOptionUsageErrorsTest, InvalidCombinations) {
  std::vector<std::vector<std::string>> invalid_combos = {
      // unsupported keyform
      {"-verify", key_path, "-signature", sig_path, "-keyform", "ENGINE",
       in_path},
      // verify without sig file
      {"-verify", key_path, "-keyform", "ENGINE", in_path},
      // hmac, verify, and sign used together
      {"-hmac", "test_key_string", "-verify", key_path, "-signature", sig_path,
       in_path},
      {"-hmac", "test_key_string", "-sign", pubkey_path, in_path},
      {"-verify", key_path, "-sign", pubkey_path, in_path},
      // wrong use of sigopt
      {"-sign", pubkey_path, "-sigopt", "abc:xyz", in_path},
      // unsupported digest
      {"-sha3224", in_path},
      // hex and binary both specified
      {"-hex", "-binary", in_path}};

  for (const auto &args : invalid_combos) {
    TestOptionUsageErrors(args);
  }
}
