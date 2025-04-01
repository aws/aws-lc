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
  FILE *config_file = fopen(openssl_config_path, "w");
  if (config_file == NULL) {
    fprintf(stderr, "Error opening config file for writing\n");
    return;
  }

  // Write the OpenSSL configuration content
  fprintf(config_file,
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

  fclose(config_file);
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
    }
  }

 public:
  int ExecuteCommand(const std::string &command) {
    return system(command.c_str());
  }

  // Load a CSR from a PEM file
  bssl::UniquePtr<X509_REQ> LoadCSR(const char *path) {
    bssl::UniquePtr<BIO> bio(BIO_new_file(path, "r"));
    if (!bio) {
      return NULL;
    }

    bssl::UniquePtr<X509_REQ> csr(
        PEM_read_bio_X509_REQ(bio.get(), nullptr, nullptr, nullptr));
    return csr;
  }

  // Load an X509 certificate from a PEM file
  bssl::UniquePtr<X509> LoadCertificate(const char *path) {
    bssl::UniquePtr<BIO> bio(BIO_new_file(path, "r"));
    if (!bio) {
      return NULL;
    }

    bssl::UniquePtr<X509> cert(
        PEM_read_bio_X509(bio.get(), nullptr, nullptr, nullptr));
    return cert;
  }

  bool CompareCSRs(X509_REQ *csr1, X509_REQ *csr2) {
    if (!csr1 || !csr2)
      return false;

    // 1. Compare subjects
    X509_NAME *name1 = X509_REQ_get_subject_name(csr1);
    X509_NAME *name2 = X509_REQ_get_subject_name(csr2);
    if (X509_NAME_cmp(name1, name2) != 0)
      return false;

    // 2. Compare signature algorithms
    int sig_nid1 = X509_REQ_get_signature_nid(csr1);
    int sig_nid2 = X509_REQ_get_signature_nid(csr2);
    if (sig_nid1 != sig_nid2)
      return false;

    // 3. Compare public key type and parameters
    EVP_PKEY *pkey1 = X509_REQ_get0_pubkey(csr1);
    EVP_PKEY *pkey2 = X509_REQ_get0_pubkey(csr2);
    if (!pkey1 || !pkey2) {
      return false;
    }
    if (EVP_PKEY_id(pkey1) != EVP_PKEY_id(pkey2)) {
      return false;
    }

    // For RSA keys, check key size
    if (EVP_PKEY_id(pkey1) == EVP_PKEY_RSA) {
      RSA *rsa1 = EVP_PKEY_get0_RSA(pkey1);
      RSA *rsa2 = EVP_PKEY_get0_RSA(pkey2);
      if (!rsa1 || !rsa2) {
        return false;
      }
      if (RSA_size(rsa1) != RSA_size(rsa2)) {
        return false;
      }
    }

    // 4. Verify that both CSRs have valid signatures
    if (X509_REQ_verify(csr1, pkey1) != 1) {
      return false;
    }
    if (X509_REQ_verify(csr2, pkey2) != 1) {
      return false;
    }

    return true;
  }

  bool CheckCertificateValidityPeriod(X509 *cert, int expected_days) {
    if (!cert)
      return false;

    const ASN1_TIME *not_before = X509_get0_notBefore(cert);
    const ASN1_TIME *not_after = X509_get0_notAfter(cert);
    if (!not_before || !not_after)
      return false;

    // Get the difference in days between not_before and not_after
    int days, seconds;
    if (!ASN1_TIME_diff(&days, &seconds, not_before, not_after)) {
      return false;
    }

    return (days == expected_days);
  }

  // Improved certificate comparison function
  bool CompareCertificates(X509 *cert1, X509 *cert2, int expected_days) {
    if (!cert1 || !cert2) {
      return false;
    }

    // 1. Compare subjects
    X509_NAME *subj1 = X509_get_subject_name(cert1);
    X509_NAME *subj2 = X509_get_subject_name(cert2);
    if (X509_NAME_cmp(subj1, subj2) != 0) {
      return false;
    }

    // 2. Compare issuers
    X509_NAME *issuer1 = X509_get_issuer_name(cert1);
    X509_NAME *issuer2 = X509_get_issuer_name(cert2);
    if (X509_NAME_cmp(issuer1, issuer2) != 0) {
      return false;
    }

    // 3. Both certificates should be self-signed
    if (X509_NAME_cmp(subj1, issuer1) != 0) {
      return false;
    }
    if (X509_NAME_cmp(subj2, issuer2) != 0) {
      return false;
    }

    // 4. Compare signature algorithms
    int sig_nid1 = X509_get_signature_nid(cert1);
    int sig_nid2 = X509_get_signature_nid(cert2);
    if (sig_nid1 != sig_nid2) {
      return false;
    }

    // 5. Check validity periods
    if (!CheckCertificateValidityPeriod(cert1, expected_days)) {
      return false;
    }
    if (!CheckCertificateValidityPeriod(cert2, expected_days)) {
      return false;
    }

    // 6. Check public key type and parameters
    EVP_PKEY *pkey1 = X509_get0_pubkey(cert1);
    EVP_PKEY *pkey2 = X509_get0_pubkey(cert2);
    if (!pkey1 || !pkey2) {
      return false;
    }

    if (EVP_PKEY_id(pkey1) != EVP_PKEY_id(pkey2)) {
      return false;
    }

    // For RSA keys, check key size
    if (EVP_PKEY_id(pkey1) == EVP_PKEY_RSA) {
      RSA *rsa1 = EVP_PKEY_get0_RSA(pkey1);
      RSA *rsa2 = EVP_PKEY_get0_RSA(pkey2);
      if (!rsa1 || !rsa2) {
        return false;
      }

      if (RSA_size(rsa1) != RSA_size(rsa2)) {
        return false;
      }
    }

    // 7. Verify signatures (self-signed)
    if (X509_verify(cert1, pkey1) != 1) {
      return false;
    }
    if (X509_verify(cert2, pkey2) != 1) {
      return false;
    }

    // 8. Compare extensions - simplified approach
    int ext_count1 = X509_get_ext_count(cert1);
    int ext_count2 = X509_get_ext_count(cert2);
    if (ext_count1 != ext_count2) {
      return false;
    }

    // Compare each extension by index (assuming same order)
    for (int i = 0; i < ext_count1; i++) {
      X509_EXTENSION *ext1 = X509_get_ext(cert1, i);
      X509_EXTENSION *ext2 = X509_get_ext(cert2, i);
      if (!ext1 || !ext2) {
        return false;
      }

      // Compare extension OIDs
      ASN1_OBJECT *obj1 = X509_EXTENSION_get_object(ext1);
      ASN1_OBJECT *obj2 = X509_EXTENSION_get_object(ext2);
      if (!obj1 || !obj2) {
        return false;
      }

      if (OBJ_cmp(obj1, obj2) != 0) {
        return false;
      }

      // Compare critical flags
      if (X509_EXTENSION_get_critical(ext1) !=
          X509_EXTENSION_get_critical(ext2)) {
        return false;
      }
    }

    return true;
  }

  char cert_path_openssl[PATH_MAX];
  char cert_path_awslc[PATH_MAX];
  char csr_path_openssl[PATH_MAX];
  char csr_path_awslc[PATH_MAX];
  char key_path_openssl[PATH_MAX];
  char key_path_awslc[PATH_MAX];
  char openssl_config_path[PATH_MAX];
  const char *tool_executable_path;
  const char *openssl_executable_path;
};

TEST_F(ReqComparisonTest, GenerateBasicCSR) {
  // Subject for certificate
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

  // Execute both commands, return values may not match due to missing conf
  // support
  ExecuteCommand(awslc_command);
  ExecuteCommand(openssl_command);

  // Cross-check CSR attributes
  auto csr_tool = LoadCSR(csr_path_awslc);
  auto csr_openssl = LoadCSR(csr_path_openssl);

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

  // Execute both commands, return values may not match due to missing conf
  // support
  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  // Load certificates
  auto cert_tool = LoadCertificate(cert_path_awslc);
  auto cert_openssl = LoadCertificate(cert_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr)
      << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl != nullptr)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 365 days validity period
  ASSERT_TRUE(CompareCertificates(cert_tool.get(), cert_openssl.get(), 365))
      << "Certificates generated by tool and OpenSSL have different attributes";
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

  bssl::UniquePtr<X509_NAME> name = parse_subject_name(mutable_input);

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
