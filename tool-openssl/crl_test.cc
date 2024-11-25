// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "openssl/x509.h"
#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "internal.h"
#include "test_util.h"
#include "../crypto/test/test_util.h"
#include <cctype>

static X509_CRL* createTestCRL() {
  bssl::UniquePtr<X509_CRL> crl(X509_CRL_new());
  if (!crl) {
    ERR_print_errors_fp(stderr);
    return nullptr;
  }

  // Set issuer name
  bssl::UniquePtr<X509_NAME> issuer(X509_NAME_new());
  if (!issuer ||
  !X509_NAME_add_entry_by_txt(issuer.get(), "CN", MBSTRING_ASC, (unsigned char *)"Test CA", -1, -1, 0) ||
  !X509_CRL_set_issuer_name(crl.get(), issuer.get())) {
    return nullptr;
  }

  // Set times
  bssl::UniquePtr<ASN1_TIME> lastUpdate(ASN1_TIME_new());
  bssl::UniquePtr<ASN1_TIME> nextUpdate(ASN1_TIME_new());
  if (!lastUpdate || !nextUpdate || !X509_gmtime_adj(lastUpdate.get(), 0) ||
  !X509_gmtime_adj(nextUpdate.get(), 86400L) || // 24 hours from now
  !X509_CRL_set1_lastUpdate(crl.get(), lastUpdate.get()) ||
  !X509_CRL_set1_nextUpdate(crl.get(), nextUpdate.get())) {
    return nullptr;
  }

  // Add a revoked certificate
  X509_REVOKED *revoked = X509_REVOKED_new();
  bssl::UniquePtr<ASN1_INTEGER> serialNumber(ASN1_INTEGER_new());
  if (!revoked || !serialNumber || !ASN1_INTEGER_set(serialNumber.get(), 1) || // Serial number of revoked cert
  !X509_REVOKED_set_serialNumber(revoked, serialNumber.get()) ||
  !X509_REVOKED_set_revocationDate(revoked, lastUpdate.get()) ||
  !X509_CRL_add0_revoked(crl.get(), revoked)) {
    return nullptr;
  }

  // Generate a key pair for signing
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  RSA *rsa = RSA_generate_key(2048, RSA_F4, NULL, NULL);
  if (!pkey || !rsa || !EVP_PKEY_assign_RSA(pkey.get(), rsa)) {
    return nullptr;
  }

  // Sign the CRL
  if (!X509_CRL_sign(crl.get(), pkey.get(), EVP_sha256())) {
    return nullptr;
  }
  return crl.release();
}

class CRLTest : public ::testing::Test {
protected:
    void SetUp() override {
      ASSERT_GT(createTempFILEpath(in_path), 0u);

      // Create a test CRL
      crl.reset(createTestCRL());
      ASSERT_TRUE(crl);


      ScopedFILE in_file(fopen(in_path, "wb"));
      ASSERT_TRUE(in_file);
      PEM_write_X509_CRL(in_file.get(), crl.get());
    }

    void TearDown() override {
      RemoveFile(in_path);
    }

    char in_path[PATH_MAX];
    bssl::UniquePtr<X509_CRL> crl;
};


// ----------------------------- CRL Option Tests -----------------------------

// Test -in
TEST_F(CRLTest, CRLTestIn) {
  args_list_t args = {"-in", in_path};
  bool result = CRLTool(args);
  ASSERT_TRUE(result);
}

// Test -hash
TEST_F(CRLTest, CRLTestHash) {
  args_list_t args = {"-in", in_path, "-hash"};
  bool result = CRLTool(args);
  ASSERT_TRUE(result);
}

// Test -fingerprint
TEST_F(CRLTest, CRLTestFingerprint) {
  args_list_t args = {"-in", in_path, "-fingerprint"};
  bool result = CRLTool(args);
  ASSERT_TRUE(result);
}

// Test -noout
TEST_F(CRLTest, CRLTestNoout) {
  args_list_t args = {"-in", in_path, "-noout"};
  bool result = CRLTool(args);
  ASSERT_TRUE(result);
}

// -------------------- CRL OpenSSL Comparison Tests --------------------------

// Comparison tests cannot run without set up of environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.

class CRLComparisonTest : public ::testing::Test {
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

      // Create a test CRL
      crl.reset(createTestCRL());
      ASSERT_TRUE(crl);

      ScopedFILE in_file(fopen(in_path, "wb"));
      ASSERT_TRUE(in_file);
      PEM_write_X509_CRL(in_file.get(), crl.get());
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
    const char* tool_executable_path;
    const char* openssl_executable_path;
    std::string tool_output_str;
    std::string openssl_output_str;
    bssl::UniquePtr<X509_CRL> crl;
};

// Test against OpenSSL output "openssl crl -in file"
TEST_F(CRLComparisonTest, CRLToolCompareOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " crl -in " + in_path + " > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " crl -in " + in_path + " > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl crl -in file -hash -fingerprint"
TEST_F(CRLComparisonTest, CRLToolCompareHashFingerprintOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " crl -in " + in_path + " -hash -fingerprint > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " crl -in " + in_path + " -hash -fingerprint > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl crl -in file -hash -fingerprint -noout"
TEST_F(CRLComparisonTest, CRLToolCompareHashFingerprintNoOutOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " crl -in " + in_path + " -hash -fingerprint -noout > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) + " crl -in " + in_path + " -hash -fingerprint -noout > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool, out_path_openssl, tool_output_str, openssl_output_str);
}
