// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/rsa.h>
#include <stdio.h>
#include <string.h>
#include "../tool/internal.h"

#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "../crypto/test/test_util.h"
#include "internal.h"
#include "test_util.h"

static void setup_config(char *openssl_config_path) {
  ScopedFILE config_file(fopen(openssl_config_path, "w"));
  if (!config_file) {
    fprintf(stderr, "Error opening config file for writing\n");
    return;
  }

  // Write the OpenSSL configuration content
  fprintf(config_file.get(),
          "[ req ]\n"
          "default_bits           = 2048\n"
          "default_keyfile        = keyfile.pem\n"
          "distinguished_name     = req_distinguished_name\n"
          "attributes             = req_attributes\n"
          "prompt                 = no\n"
          "output_password        = mypass\n"
          "x509_extensions        = v3_ca\n"
          "\n"
          "[ req_distinguished_name ]\n"
          "C                      = GB\n"
          "ST                     = Test State or Province\n"
          "L                      = Test Locality\n"
          "O                      = Organization Name\n"
          "OU                     = Organizational Unit Name\n"
          "CN                     = Common Name\n"
          "emailAddress           = test@email.address\n"
          "\n"
          "[ req_attributes ]\n"
          "challengePassword      = A challenge password\n"
          "\n"
          "[ v3_ca ]\n"
          "subjectKeyIdentifier    = hash\n"
          "authorityKeyIdentifier  = keyid:always,issuer:always\n"
          "basicConstraints        = critical, CA:true\n");
}

class ReqComparisonTest : public ::testing::Test {
 protected:
  void SetUp() override {
    // Skip gtests if env variables not set
    tool_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
    if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
      GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH "
                      "environment variables are not set";
    }

    ASSERT_GT(createTempFILEpath(cert_path_openssl), 0u);
    ASSERT_GT(createTempFILEpath(cert_path_awslc), 0u);
    ASSERT_GT(createTempFILEpath(csr_path_openssl), 0u);
    ASSERT_GT(createTempFILEpath(csr_path_awslc), 0u);
    ASSERT_GT(createTempFILEpath(key_path_openssl), 0u);
    ASSERT_GT(createTempFILEpath(key_path_awslc), 0u);
    ASSERT_GT(createTempFILEpath(openssl_config_path), 0u);

    setup_config(openssl_config_path);

    // Create shared key files for signing
    ASSERT_GT(createTempFILEpath(sign_key_path), 0u);
    ASSERT_GT(createTempFILEpath(protected_sign_key_path), 0u);

    bssl::UniquePtr<EVP_PKEY> test_key(CreateTestKey(2048));
    ASSERT_TRUE(test_key);

    // Create unencrypted key file
    ScopedFILE key_file(fopen(sign_key_path, "wb"));
    ASSERT_TRUE(key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(key_file.get(), test_key.get(), nullptr,
                                     nullptr, 0, nullptr, nullptr));
    key_file.reset();

    // Create encrypted key file
    ScopedFILE encrypted_key_file(fopen(protected_sign_key_path, "wb"));
    ASSERT_TRUE(encrypted_key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(
        encrypted_key_file.get(), test_key.get(), EVP_aes_256_cbc(),
        (unsigned char *)"testpassword", 12, nullptr, nullptr));
  }

  void TearDown() override {
    if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
      RemoveFile(cert_path_openssl);
      RemoveFile(cert_path_awslc);
      RemoveFile(csr_path_openssl);
      RemoveFile(csr_path_awslc);
      RemoveFile(key_path_openssl);
      RemoveFile(key_path_awslc);
      RemoveFile(openssl_config_path);
      RemoveFile(sign_key_path);
      RemoveFile(protected_sign_key_path);
    }
  }

  char cert_path_openssl[PATH_MAX];
  char cert_path_awslc[PATH_MAX];
  char csr_path_openssl[PATH_MAX];
  char csr_path_awslc[PATH_MAX];
  char key_path_openssl[PATH_MAX];
  char key_path_awslc[PATH_MAX];
  char openssl_config_path[PATH_MAX];
  char sign_key_path[PATH_MAX];
  char protected_sign_key_path[PATH_MAX];
  const char *tool_executable_path;
  const char *openssl_executable_path;
};

TEST_F(ReqComparisonTest, GenerateBasicCSR) {
  std::string subject =
      "/C=US/ST=Washington/L=Seattle/O=Example Inc/CN=example.com";

  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-newkey rsa:2048 -nodes -keyout " +
                              key_path_awslc + " -out " + csr_path_awslc +
                              " -subj \"" + subject + "\"";

  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new " +
      "-newkey rsa:2048 -nodes -config " + openssl_config_path + " -keyout " +
      key_path_openssl + " -out " + csr_path_openssl + " -subj \"" + subject +
      "\"";

  ExecuteCommand(awslc_command);
  ExecuteCommand(openssl_command);

  // Cross-check CSR attributes
  auto csr_tool = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);

  ASSERT_TRUE(csr_tool != nullptr) << "Failed to load CSR generated by tool";
  ASSERT_TRUE(csr_openssl != nullptr)
      << "Failed to load CSR generated by OpenSSL";

  // Compare CSR attributes
  ASSERT_TRUE(CompareCSRs(csr_tool.get(), csr_openssl.get()))
      << "CSR attributes don't match";
}

// Test for generating a self-signed certificate
TEST_F(ReqComparisonTest, GenerateSelfSignedCertificate) {
  std::string subject =
      "/C=US/ST=Washington/L=Seattle/O=Example Inc/CN=example.com";

  std::string tool_command =
      std::string(tool_executable_path) + " req -x509 -new " +
      "-newkey rsa:2048 -nodes -days 365 -keyout " + key_path_awslc + " -out " +
      cert_path_awslc + " -subj \"" + subject + "\"";

  std::string openssl_command =
      std::string(openssl_executable_path) + " req -x509 -new " +
      "-newkey rsa:2048 -nodes -config " + openssl_config_path +
      " -days 365 -keyout " + key_path_openssl + " -out " + cert_path_openssl +
      " -subj \"" + subject + "\"";

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  // Load certificates
  auto cert_tool = LoadPEMCertificate(cert_path_awslc);
  auto cert_openssl = LoadPEMCertificate(cert_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr)
      << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl != nullptr)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 365 days validity period
  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 365))
      << "Certificates generated by tool and OpenSSL have different attributes";
}

// Test config file key length parsing
TEST_F(ReqComparisonTest, FileKeyLengthFromConfig) {
  // Create config with custom key length
  ScopedFILE config_file(fopen(openssl_config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[ req ]\n"
          "default_bits = 4096\n"
          "distinguished_name = req_distinguished_name\n"
          "prompt = no\n"
          "\n"
          "[ req_distinguished_name ]\n"
          "CN = test.example.com\n");
  fclose(config_file.release());

  std::string subject = "/CN=test.example.com";
  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-config " + openssl_config_path +
                              " -nodes -keyout " + key_path_awslc + " -out " +
                              csr_path_awslc + " -subj \"" + subject + "\"";
  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new " + "-config " +
      openssl_config_path + " -nodes -keyout " + key_path_openssl + " -out " +
      csr_path_openssl + " -subj \"" + subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);
  ASSERT_TRUE(csr_awslc != nullptr);
  ASSERT_TRUE(csr_openssl != nullptr);
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));
}

// Test no-prompt mode from config
TEST_F(ReqComparisonTest, NoPromptConfig) {
  // Create config with prompt = no
  ScopedFILE config_file(fopen(openssl_config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[ req ]\n"
          "prompt = no\n"
          "distinguished_name = req_distinguished_name\n"
          "\n"
          "[ req_distinguished_name ]\n"
          "CN = config.example.com\n"
          "C = US\n");
  fclose(config_file.release());

  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-config " + openssl_config_path +
                              " -newkey rsa:2048 -nodes -keyout " +
                              key_path_awslc + " -out " + csr_path_awslc;
  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new " + "-config " +
      openssl_config_path + " -newkey rsa:2048 -nodes -keyout " +
      key_path_openssl + " -out " + csr_path_openssl;

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);
  ASSERT_TRUE(csr_awslc != nullptr);
  ASSERT_TRUE(csr_openssl != nullptr);
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));
}

// Test interactive prompting with input
TEST_F(ReqComparisonTest, InteractivePrompting) {
  std::string input =
      "US\\nSeattle\\nWashington\\nTest Corp\\nTest "
      "Unit\\ntest.example.com\\ntest@example.com\\n\\n\\n";

  std::string awslc_command = "echo -e '" + input + "' | " +
                              std::string(tool_executable_path) + " req -new " +
                              "-newkey rsa:2048 -nodes -keyout " +
                              key_path_awslc + " -out " + csr_path_awslc;

  std::string openssl_command =
      "echo -e '" + input + "' | " + std::string(openssl_executable_path) +
      " req -new " + "-newkey rsa:2048 -nodes -keyout " + key_path_openssl +
      " -out " + csr_path_openssl;

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);

  ASSERT_TRUE(csr_awslc != nullptr);
  ASSERT_TRUE(csr_openssl != nullptr);
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));
}

// Test key length validation
TEST_F(ReqComparisonTest, KeyLengthValidation) {
  std::string subject = "/CN=test.example.com";

  // Test minimum key length rejection
  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-newkey rsa:256 -nodes -keyout " +
                              key_path_awslc + " -out " + csr_path_awslc +
                              " -subj \"" + subject + "\"";
  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new " +
      "-newkey rsa:256 -nodes -keyout " + key_path_openssl + " -out " +
      csr_path_openssl + " -subj \"" + subject + "\"";

  EXPECT_NE(ExecuteCommand(awslc_command), 0);
  EXPECT_NE(ExecuteCommand(openssl_command), 0);
}

// Test config file digest selection
TEST_F(ReqComparisonTest, ConfigDigestSelection) {
  // Create config with custom digest
  ScopedFILE config_file(fopen(openssl_config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[ req ]\n"
          "default_md = sha384\n"
          "distinguished_name = req_distinguished_name\n"
          "prompt = no\n"
          "\n"
          "[ req_distinguished_name ]\n"
          "CN = test.example.com\n");
  fclose(config_file.release());

  std::string subject = "/CN=test.example.com";
  std::string awslc_command =
      std::string(tool_executable_path) + " req -new " + "-config " +
      openssl_config_path + " -newkey rsa:2048 -nodes -keyout " +
      key_path_awslc + " -out " + csr_path_awslc + " -subj \"" + subject + "\"";
  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new " + "-config " +
      openssl_config_path + " -newkey rsa:2048 -nodes -keyout " +
      key_path_openssl + " -out " + csr_path_openssl + " -subj \"" + subject +
      "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);

  ASSERT_TRUE(csr_awslc != nullptr) << "Failed to load AWS-LC CSR";
  ASSERT_TRUE(csr_openssl != nullptr) << "Failed to load OpenSSL CSR";
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));
}

// Test BuildSubject function with config fallback
TEST_F(ReqComparisonTest, SubjectConfigFallback) {
  // Create config with subject fields using both long and short names
  ScopedFILE config_file(fopen(openssl_config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[ req ]\n"
          "distinguished_name = req_distinguished_name\n"
          "prompt = no\n"
          "\n"
          "[ req_distinguished_name ]\n"
          "countryName = US\n"
          "ST = California\n"  // Test short name fallback
          "organizationName = Test Org\n"
          "CN = config.example.com\n");
  fclose(config_file.release());

  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-config " + openssl_config_path +
                              " -newkey rsa:2048 -nodes -keyout " +
                              key_path_awslc + " -out " + csr_path_awslc;
  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new " + "-config " +
      openssl_config_path + " -newkey rsa:2048 -nodes -keyout " +
      key_path_openssl + " -out " + csr_path_openssl;

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);

  ASSERT_TRUE(csr_awslc != nullptr) << "Failed to load AWS-LC CSR";
  ASSERT_TRUE(csr_openssl != nullptr) << "Failed to load OpenSSL CSR";
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));
}

// Test -key option with existing private key
TEST_F(ReqComparisonTest, ExistingPrivateKey) {
  std::string subject = "/CN=existing-key.example.com";
  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-key " + sign_key_path + " -out " +
                              csr_path_awslc + " -subj \"" + subject + "\"";
  std::string openssl_command = std::string(openssl_executable_path) +
                                " req -new " + "-key " + sign_key_path +
                                " -out " + csr_path_openssl + " -subj \"" +
                                subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);

  ASSERT_TRUE(csr_awslc != nullptr) << "Failed to load AWS-LC CSR";
  ASSERT_TRUE(csr_openssl != nullptr) << "Failed to load OpenSSL CSR";
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));
}

// Test -outform DER option
TEST_F(ReqComparisonTest, DEROutputFormat) {
  std::string subject = "/CN=der-test.example.com";
  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-newkey rsa:2048 -nodes -keyout " +
                              key_path_awslc + " -out " + csr_path_awslc +
                              " -outform DER" + " -subj \"" + subject + "\"";
  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new " +
      "-newkey rsa:2048 -nodes -keyout " + key_path_openssl + " -out " +
      csr_path_openssl + " -outform DER" + " -subj \"" + subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadDERCSR(csr_path_awslc);
  auto csr_openssl = LoadDERCSR(csr_path_openssl);

  ASSERT_TRUE(csr_awslc != nullptr) << "Failed to load AWS-LC CSR";
  ASSERT_TRUE(csr_openssl != nullptr) << "Failed to load OpenSSL CSR";
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));

  awslc_command = std::string(tool_executable_path) + " req -x509 -new " +
                  "-newkey rsa:2048 -nodes -days 365 -keyout " +
                  key_path_awslc + " -out " + cert_path_awslc +
                  " -outform DER -subj \"" + subject + "\"";

  openssl_command = std::string(openssl_executable_path) + " req -x509 -new " +
                    "-newkey rsa:2048 -nodes -days 365 -keyout " +
                    key_path_openssl + " -out " + cert_path_openssl +
                    " -outform DER -subj \"" + subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto cert_awslc = LoadDERCertificate(cert_path_awslc);
  auto cert_openssl = LoadDERCertificate(cert_path_openssl);

  ASSERT_TRUE(cert_awslc != nullptr) << "Failed to load AWS-LC DER certificate";
  ASSERT_TRUE(cert_openssl != nullptr)
      << "Failed to load OpenSSL DER certificate";

  // Compare certificates with 365 days validity period
  ASSERT_TRUE(
      CompareCertificates(cert_awslc.get(), cert_openssl.get(), nullptr, 365))
      << "DER certificates generated by AWS-LC and OpenSSL have different "
         "attributes";
}

// Test digest algorithm selection
TEST_F(ReqComparisonTest, DigestAlgorithmSelection) {
  std::string subject = "/CN=sha384-test.example.com";
  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-sha384 -newkey rsa:2048 -nodes -keyout " +
                              key_path_awslc + " -out " + csr_path_awslc +
                              " -subj \"" + subject + "\"";
  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new " +
      "-sha384 -newkey rsa:2048 -nodes -keyout " + key_path_openssl + " -out " +
      csr_path_openssl + " -subj \"" + subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);

  ASSERT_TRUE(csr_awslc != nullptr) << "Failed to load AWS-LC CSR";
  ASSERT_TRUE(csr_openssl != nullptr) << "Failed to load OpenSSL CSR";
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));
}

// Test -newkey and -key conflict warning
TEST_F(ReqComparisonTest, NewkeyKeyConflictWarning) {
  // Generate keys first
  std::string subject = "/CN=conflict-test.example.com";
  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-newkey rsa:4096 -key " + sign_key_path +
                              " -nodes -out " + csr_path_awslc + " -subj \"" +
                              subject + "\"";
  std::string openssl_command = std::string(openssl_executable_path) +
                                " req -new " + "-newkey rsa:4096 -key " +
                                sign_key_path + " -nodes -out " +
                                csr_path_openssl + " -subj \"" + subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);

  ASSERT_TRUE(csr_awslc != nullptr) << "Failed to load AWS-LC CSR";
  ASSERT_TRUE(csr_openssl != nullptr) << "Failed to load OpenSSL CSR";
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));
}

// Test certificate generation with custom validity period
TEST_F(ReqComparisonTest, CustomValidityPeriod) {
  std::string subject = "/CN=custom-validity.example.com";

  std::string awslc_command =
      std::string(tool_executable_path) + " req -x509 -new " +
      "-newkey rsa:2048 -nodes -days 180 -keyout " + key_path_awslc + " -out " +
      cert_path_awslc + " -subj \"" + subject + "\"";

  std::string openssl_command =
      std::string(openssl_executable_path) + " req -x509 -new " +
      "-newkey rsa:2048 -nodes -days 180 -keyout " + key_path_openssl +
      " -out " + cert_path_openssl + " -subj \"" + subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto cert_awslc = LoadPEMCertificate(cert_path_awslc);
  auto cert_openssl = LoadPEMCertificate(cert_path_openssl);

  ASSERT_TRUE(cert_awslc != nullptr) << "Failed to load AWS-LC certificate";
  ASSERT_TRUE(cert_openssl != nullptr) << "Failed to load OpenSSL certificate";

  // Compare certificates with 180 days validity period
  ASSERT_TRUE(
      CompareCertificates(cert_awslc.get(), cert_openssl.get(), nullptr, 180))
      << "Certificates generated by AWS-LC and OpenSSL have different "
         "attributes";
}

TEST_F(ReqComparisonTest, CustomSigningKey) {
  std::string subject = "/CN=key-loading-test.example.com";
  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-key " + sign_key_path + " -out " +
                              csr_path_awslc + " -subj \"" + subject + "\"";
  std::string openssl_command = std::string(openssl_executable_path) +
                                " req -new " + "-key " + sign_key_path +
                                " -out " + csr_path_openssl + " -subj \"" +
                                subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);

  ASSERT_TRUE(csr_awslc != nullptr) << "Failed to load AWS-LC CSR";
  ASSERT_TRUE(csr_openssl != nullptr) << "Failed to load OpenSSL CSR";
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));
}

// Test -passin option with password-protected key
TEST_F(ReqComparisonTest, ProtectedSigningKey) {
  std::string subject = "/CN=passin-test.example.com";
  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-key " + protected_sign_key_path +
                              " -passin pass:testpassword " + "-out " +
                              csr_path_awslc + " -subj \"" + subject + "\"";
  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new " + "-key " +
      protected_sign_key_path + " -passin pass:testpassword " + "-out " +
      csr_path_openssl + " -subj \"" + subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);

  ASSERT_TRUE(csr_awslc != nullptr);
  ASSERT_TRUE(csr_openssl != nullptr);
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));
}

// Test -extensions option with -x509
TEST_F(ReqComparisonTest, X509Extensions) {
  // Create config file with custom extension section
  ScopedFILE config_file(fopen(openssl_config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[ req ]\n"
          "distinguished_name = req_distinguished_name\n"
          "prompt = no\n"
          "\n"
          "[ req_distinguished_name ]\n"
          "CN = extensions-test.example.com\n"
          "\n"
          "[ custom_ext ]\n"
          "basicConstraints = CA:FALSE\n"
          "keyUsage = digitalSignature, keyEncipherment\n"
          "subjectAltName = DNS:alt.example.com\n");
  fclose(config_file.release());

  std::string subject = "/CN=extensions-test.example.com";
  std::string awslc_command =
      std::string(tool_executable_path) + " req -x509 -new " + "-config " +
      openssl_config_path + " -extensions custom_ext " +
      "-newkey rsa:2048 -nodes -days 365 -keyout " + key_path_awslc + " -out " +
      cert_path_awslc + " -subj \"" + subject + "\"";

  std::string openssl_command =
      std::string(openssl_executable_path) + " req -x509 -new " + "-config " +
      openssl_config_path + " -extensions custom_ext " +
      "-newkey rsa:2048 -nodes -days 365 -keyout " + key_path_openssl +
      " -out " + cert_path_openssl + " -subj \"" + subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto cert_awslc = LoadPEMCertificate(cert_path_awslc);
  auto cert_openssl = LoadPEMCertificate(cert_path_openssl);

  ASSERT_TRUE(cert_awslc != nullptr)
      << "Failed to load AWS-LC certificate with custom extensions";
  ASSERT_TRUE(cert_openssl != nullptr)
      << "Failed to load OpenSSL certificate with custom extensions";

  // Compare certificates with custom extensions
  ASSERT_TRUE(
      CompareCertificates(cert_awslc.get(), cert_openssl.get(), nullptr, 365))
      << "Certificates with custom extensions have different attributes";
}

// Test -extensions option without -x509
TEST_F(ReqComparisonTest, ReqExtensions) {
  // Create config file with extension section
  ScopedFILE config_file(fopen(openssl_config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[ req ]\n"
          "distinguished_name = req_distinguished_name\n"
          "prompt = no\n"
          "\n"
          "[ req_distinguished_name ]\n"
          "CN = extensions-test.example.com\n"
          "\n"
          "[ test_ext ]\n"
          "basicConstraints = CA:FALSE\n"
          "keyUsage = digitalSignature, keyEncipherment\n");
  fclose(config_file.release());

  std::string subject = "/CN=extensions-test.example.com";
  std::string awslc_command =
      std::string(tool_executable_path) + " req -new " + "-config " +
      openssl_config_path + " -extensions test_ext " +
      "-newkey rsa:2048 -nodes -keyout " + key_path_awslc + " -out " +
      csr_path_awslc + " -subj \"" + subject + "\"";

  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new " + "-config " +
      openssl_config_path + " -extensions test_ext " +
      "-newkey rsa:2048 -nodes -keyout " + key_path_openssl + " -out " +
      csr_path_openssl + " -subj \"" + subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);
  ASSERT_TRUE(csr_awslc != nullptr);
  ASSERT_TRUE(csr_openssl != nullptr);
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));
}

// Test req extensions obtained from config
TEST_F(ReqComparisonTest, ReqExtensionsFromConfig) {
  ScopedFILE config_file(fopen(openssl_config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[ req ]\n"
          "distinguished_name = req_distinguished_name\n"
          "req_extensions = v3_req\n"
          "prompt = no\n"
          "\n"
          "[ req_distinguished_name ]\n"
          "CN = req-ext-test.example.com\n"
          "\n"
          "[ v3_req ]\n"
          "subjectAltName = DNS:alt1.example.com,DNS:alt2.example.com\n"
          "keyUsage = digitalSignature, keyEncipherment\n");
  fclose(config_file.release());

  std::string subject = "/CN=req-ext-test.example.com";
  std::string awslc_command =
      std::string(tool_executable_path) + " req -new " + "-config " +
      openssl_config_path + " -newkey rsa:2048 -nodes -keyout " +
      key_path_awslc + " -out " + csr_path_awslc + " -subj \"" + subject + "\"";

  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new " + "-config " +
      openssl_config_path + " -newkey rsa:2048 -nodes -keyout " +
      key_path_openssl + " -out " + csr_path_openssl + " -subj \"" + subject +
      "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);
  ASSERT_TRUE(csr_awslc != nullptr);
  ASSERT_TRUE(csr_openssl != nullptr);
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));
}

// Test x509 extensions obtained from config
TEST_F(ReqComparisonTest, X509ExtensionsFromConfig) {
  ScopedFILE config_file(fopen(openssl_config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[ req ]\n"
          "distinguished_name = req_distinguished_name\n"
          "x509_extensions = v3_ca\n"
          "prompt = no\n"
          "\n"
          "[ req_distinguished_name ]\n"
          "CN = x509-ext-test.example.com\n"
          "\n"
          "[ v3_ca ]\n"
          "basicConstraints = critical,CA:true\n"
          "keyUsage = critical,keyCertSign,cRLSign\n"
          "subjectKeyIdentifier = hash\n");
  fclose(config_file.release());

  std::string subject = "/CN=x509-ext-test.example.com";
  std::string awslc_command =
      std::string(tool_executable_path) + " req -x509 -new " + "-config " +
      openssl_config_path + " -newkey rsa:2048 -nodes -days 365 -keyout " +
      key_path_awslc + " -out " + cert_path_awslc + " -subj \"" + subject +
      "\"";

  std::string openssl_command =
      std::string(openssl_executable_path) + " req -x509 -new " + "-config " +
      openssl_config_path + " -newkey rsa:2048 -nodes -days 365 -keyout " +
      key_path_openssl + " -out " + cert_path_openssl + " -subj \"" + subject +
      "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto cert_awslc = LoadPEMCertificate(cert_path_awslc);
  auto cert_openssl = LoadPEMCertificate(cert_path_openssl);
  ASSERT_TRUE(cert_awslc != nullptr);
  ASSERT_TRUE(cert_openssl != nullptr);
  ASSERT_TRUE(
      CompareCertificates(cert_awslc.get(), cert_openssl.get(), nullptr, 365));
}

struct SubjectNameTestCase {
  std::string input;
  bool expect_success;
  int expected_entry_count;
  std::vector<std::string> expected_values;

  SubjectNameTestCase(const std::string &input_, bool expect_success_,
                      int expected_entry_count_,
                      const std::vector<std::string> &expected_values_)
      : input(input_),
        expect_success(expect_success_),
        expected_entry_count(expected_entry_count_),
        expected_values(expected_values_) {}
};

void PrintTo(const SubjectNameTestCase &test_case, std::ostream *os);

class SubjectNameTest : public testing::TestWithParam<SubjectNameTestCase> {
 protected:
  static std::string GetEntryValue(X509_NAME *name, int index) {
    unsigned char *tmp;
    X509_NAME_ENTRY *entry = X509_NAME_get_entry(name, index);
    int len = ASN1_STRING_to_UTF8(&tmp, X509_NAME_ENTRY_get_data(entry));
    std::string result = "";
    if (len > 0) {
      result.assign(reinterpret_cast<char *>(tmp), len);
    }
    OPENSSL_free(tmp);
    return result;
  }
};

void PrintTo(const SubjectNameTestCase &test_case, std::ostream *os) {
  *os << "SubjectNameTestCase{"
      << "input: \"" << test_case.input << "\", "
      << "expect_success: " << (test_case.expect_success ? "true" : "false")
      << ", "
      << "expected_entry_count: " << test_case.expected_entry_count << ", "
      << "expected_values: [";

  for (size_t i = 0; i < test_case.expected_values.size(); ++i) {
    if (i > 0)
      *os << ", ";
    *os << "\"" << test_case.expected_values[i] << "\"";
  }

  *os << "]}";
}

static const SubjectNameTestCase kSubjectNameTestCases[] = {
    // Valid subject with multiple fields
    SubjectNameTestCase("/C=US/ST=California/O=Example/CN=test.com", true, 4,
                        {"US", "California", "Example", "test.com"}),
    // Escaped characters
    SubjectNameTestCase("/CN=test\\/example\\.com", true, 1,
                        {"test/example.com"}),
    // Missing leading slash
    SubjectNameTestCase("CN=test.com", false, 0, {""}),
    // Missing equals sign
    SubjectNameTestCase("/CNtest.com", false, 0, {""}),
    // Empty value
    SubjectNameTestCase("/CN=/O=test", true, 1, {"test"}),
    // Unknown attribute
    SubjectNameTestCase("/UNKNOWN=test/CN=example.com", true, 1,
                        {"example.com"}),
    // Empty subject
    SubjectNameTestCase("/", true, 0, {""})};

INSTANTIATE_TEST_SUITE_P(SubjectNameTests, SubjectNameTest,
                         testing::ValuesIn(kSubjectNameTestCases));

TEST_P(SubjectNameTest, ParseSubjectName) {
  const SubjectNameTestCase &test_case = GetParam();
  std::string mutable_input = test_case.input;  // Create mutable copy

  bssl::UniquePtr<X509_NAME> name = ParseSubjectName(mutable_input);

  if (!test_case.expect_success) {
    EXPECT_EQ(name, nullptr);
    return;
  }

  ASSERT_NE(name, nullptr);
  EXPECT_EQ(X509_NAME_entry_count(name.get()), test_case.expected_entry_count);

  for (size_t i = 0; i < test_case.expected_values.size(); ++i) {
    if (!test_case.expected_values[i].empty()) {
      EXPECT_EQ(GetEntryValue(name.get(), i), test_case.expected_values[i]);
    }
  }
}
