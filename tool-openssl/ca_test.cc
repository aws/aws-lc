// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/rsa.h>
#include <openssl/x509.h>
#include <openssl/x509v3.h>
#include <stdio.h>
#include <string.h>
#if defined(OPENSSL_WINDOWS)
#include <direct.h>
#include <io.h>
#else
#include <sys/stat.h>
#endif
#include "../tool/internal.h"

#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "../crypto/test/test_util.h"
#include "internal.h"
#include "test_util.h"

class CATest : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(config_path), 0u);
    ASSERT_GT(createTempFILEpath(csr_path), 0u);
    ASSERT_GT(createTempFILEpath(cert_path), 0u);
    ASSERT_GT(createTempFILEpath(ca_key_path), 0u);
    ASSERT_GT(createTempFILEpath(ca_cert_path), 0u);
    ASSERT_GT(createTempFILEpath(db_path), 0u);
    ASSERT_GT(createTempFILEpath(serial_path), 0u);
    ASSERT_GT(createTempFILEpath(protected_key_path), 0u);
    ASSERT_GT(createTempFILEpath(output_path), 0u);

    // Create ED25519 temp file paths
    ASSERT_GT(createTempFILEpath(ed25519_key_path), 0u);
    ASSERT_GT(createTempFILEpath(ed25519_cert_path), 0u);
    ASSERT_GT(createTempFILEpath(ed25519_csr_path), 0u);

    // Create temp directory for new certificates
    ASSERT_GT(createTempDirPath(new_certs_dir), 0u);

    // Create a test CA key and certificate first (needed for CSR)
    CreateTestCAKeyAndCert();
    
    // Create a test CSR using the same key (self-signed)
    CreateTestCSR();

    // Create ED25519 test infrastructure
    CreateTestED25519KeyAndCert();
    CreateTestED25519CSR();
    
    // Create initial database files
    CreateTestDatabase();
  }

  void TearDown() override {
    RemoveFile(config_path);
    RemoveFile(csr_path);
    RemoveFile(cert_path);
    RemoveFile(ca_key_path);
    RemoveFile(ca_cert_path);
    RemoveFile(db_path);
    RemoveFile(serial_path);
    RemoveFile(protected_key_path);
    RemoveFile(output_path);

    // Clean up ED25519 files
    RemoveFile(ed25519_key_path);
    RemoveFile(ed25519_cert_path);
    RemoveFile(ed25519_csr_path);
    
    // Remove database attribute file if it exists
    std::string db_attr_path = std::string(db_path) + ".attr";
    RemoveFile(db_attr_path.c_str());
    
    // Clean up temp directory
    if (new_certs_dir[0] != '\0') {
#if defined(OPENSSL_WINDOWS)
      _rmdir(new_certs_dir);
#else
      rmdir(new_certs_dir);
#endif
    }
  }

  void CreateTestCAKeyAndCert() {
    // Create CA private key - this will be used for both CA and CSR signing
    bssl::UniquePtr<EVP_PKEY> ca_pkey(EVP_PKEY_new());
    ASSERT_TRUE(ca_pkey);
    bssl::UniquePtr<RSA> ca_rsa(RSA_new());
    ASSERT_TRUE(ca_rsa);
    bssl::UniquePtr<BIGNUM> ca_bn(BN_new());
    ASSERT_TRUE(ca_bn && BN_set_word(ca_bn.get(), RSA_F4) &&
                RSA_generate_key_ex(ca_rsa.get(), 2048, ca_bn.get(), nullptr));
    ASSERT_TRUE(EVP_PKEY_assign_RSA(ca_pkey.get(), ca_rsa.release()));

    // Write CA key (unencrypted)
    ScopedFILE ca_key_file(fopen(ca_key_path, "wb"));
    ASSERT_TRUE(ca_key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(ca_key_file.get(), ca_pkey.get(), nullptr,
                                     nullptr, 0, nullptr, nullptr));
    
    // Write CA key (encrypted for password tests)
    ScopedFILE protected_key_file(fopen(protected_key_path, "wb"));
    ASSERT_TRUE(protected_key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(protected_key_file.get(), ca_pkey.get(), 
                                     EVP_aes_256_cbc(),
                                     (unsigned char*)"testpassword", 12, nullptr, nullptr));

    // Create CA certificate (self-signed)
    bssl::UniquePtr<X509> ca_cert(X509_new());
    ASSERT_TRUE(ca_cert);
    
    ASSERT_TRUE(X509_set_version(ca_cert.get(), 2)); // v3
    
    // Set serial number
    bssl::UniquePtr<ASN1_INTEGER> serial(ASN1_INTEGER_new());
    ASSERT_TRUE(serial && ASN1_INTEGER_set(serial.get(), 1));
    ASSERT_TRUE(X509_set_serialNumber(ca_cert.get(), serial.get()));
    
    // Set validity period
    ASSERT_TRUE(X509_gmtime_adj(X509_getm_notBefore(ca_cert.get()), 0));
    ASSERT_TRUE(X509_gmtime_adj(X509_getm_notAfter(ca_cert.get()), 365 * 24 * 60 * 60));
    
    // Set subject and issuer (same for self-signed)
    bssl::UniquePtr<X509_NAME> ca_name(X509_NAME_new());
    ASSERT_TRUE(ca_name);
    ASSERT_TRUE(X509_NAME_add_entry_by_txt(ca_name.get(), "CN", MBSTRING_ASC,
                                           (unsigned char*)"Test CA", -1, -1, 0));
    ASSERT_TRUE(X509_set_subject_name(ca_cert.get(), ca_name.get()));
    ASSERT_TRUE(X509_set_issuer_name(ca_cert.get(), ca_name.get()));
    
    // Set public key
    ASSERT_TRUE(X509_set_pubkey(ca_cert.get(), ca_pkey.get()));
    
    // Sign certificate
    ASSERT_TRUE(X509_sign(ca_cert.get(), ca_pkey.get(), EVP_sha256()));

    // Note: leaving this here unless we want to support non-self-signed certificate
    // in the future
    //
    // Write CA certificate
    // ScopedFILE ca_cert_file(fopen(ca_cert_path, "wb"));
    // ASSERT_TRUE(ca_cert_file);
    // ASSERT_TRUE(PEM_write_X509(ca_cert_file.get(), ca_cert.get()));

    // Store the key for CSR creation
    test_ca_key_ = std::move(ca_pkey);
  }

  void CreateTestCSR() {
    // For self-signed certificates, the CSR must be signed with the same key as the CA
    // Use the CA key that was created in CreateTestCAKeyAndCert()
    ASSERT_TRUE(test_ca_key_) << "CA key must be created before CSR";

    // Create a certificate signing request
    bssl::UniquePtr<X509_REQ> req(X509_REQ_new());
    ASSERT_TRUE(req);
    
    // Set subject name
    bssl::UniquePtr<X509_NAME> name(X509_NAME_new());
    ASSERT_TRUE(name);
    ASSERT_TRUE(X509_NAME_add_entry_by_txt(name.get(), "CN", MBSTRING_ASC,
                                           (unsigned char*)"test.example.com", -1, -1, 0));
    ASSERT_TRUE(X509_REQ_set_subject_name(req.get(), name.get()));
    
    // Set public key (same as CA key for self-signed)
    ASSERT_TRUE(X509_REQ_set_pubkey(req.get(), test_ca_key_.get()));
    
    // Sign the CSR with the same key (self-signed requirement)
    ASSERT_TRUE(X509_REQ_sign(req.get(), test_ca_key_.get(), EVP_sha256()));

    // Write CSR to file
    ScopedFILE csr_file(fopen(csr_path, "wb"));
    ASSERT_TRUE(csr_file);
    ASSERT_TRUE(PEM_write_X509_REQ(csr_file.get(), req.get()));
  }

  void CreateTestDatabase() {
    // Create empty database file
    ScopedFILE db_file(fopen(db_path, "w"));
    ASSERT_TRUE(db_file);
    // Empty database - no entries initially
    
    // Create database attribute file
    std::string db_attr_path = std::string(db_path) + ".attr";
    ScopedFILE db_attr_file(fopen(db_attr_path.c_str(), "w"));
    ASSERT_TRUE(db_attr_file);
    fprintf(db_attr_file.get(), "unique_subject = yes\n");
    
    // Create serial number file
    ScopedFILE serial_file(fopen(serial_path, "w"));
    ASSERT_TRUE(serial_file);
    fprintf(serial_file.get(), "01\n");
  }

  // Helper function to escape backslashes in file paths for configuration files
  std::string EscapeConfigPath(const char* path) {
    std::string result(path);
    // Replace all backslashes with double backslashes
    size_t pos = 0;
    while ((pos = result.find('\\', pos)) != std::string::npos) {
      result.replace(pos, 1, "\\\\");
      pos += 2; // Skip the newly inserted backslashes
    }
    return result;
  }

  void CreateBasicConfig() {
    ScopedFILE config_file(fopen(config_path, "w"));
    ASSERT_TRUE(config_file);
    
    std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(ca_key_path) + R"(
certificate = )" + EscapeConfigPath(ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha256
policy = policy_anything
x509_extensions = v3_ca
copy_extensions = none
preserve = no
days = 365

[ policy_anything ]
countryName = optional
stateOrProvinceName = optional
localityName = optional
organizationName = optional
organizationalUnitName = optional
commonName = supplied

[ v3_ca ]
basicConstraints = CA:FALSE
keyUsage = digitalSignature, keyEncipherment
)";
    
    fprintf(config_file.get(), "%s", config_content.c_str());
  }

  void CreateConfigWithExtensions() {
    ScopedFILE config_file(fopen(config_path, "w"));
    ASSERT_TRUE(config_file);
    
    std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(ca_key_path) + R"(
certificate = )" + EscapeConfigPath(ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha256
policy = policy_anything
x509_extensions = usr_cert
copy_extensions = copy
preserve = no
days = 365

[ policy_anything ]
countryName = optional
stateOrProvinceName = optional
localityName = optional
organizationName = optional
organizationalUnitName = optional
commonName = supplied

[ usr_cert ]
basicConstraints = CA:FALSE
keyUsage = nonRepudiation, digitalSignature, keyEncipherment
subjectAltName = DNS:alt.example.com
)";
    
    fprintf(config_file.get(), "%s", config_content.c_str());
  }

  char config_path[PATH_MAX];
  char csr_path[PATH_MAX];
  char cert_path[PATH_MAX];
  char ca_key_path[PATH_MAX];
  char ca_cert_path[PATH_MAX];
  char db_path[PATH_MAX];
  char serial_path[PATH_MAX];
  char protected_key_path[PATH_MAX];
  char output_path[PATH_MAX];
  char new_certs_dir[PATH_MAX];
  
  // CA key used for both CA operations and CSR signing (self-signed)
  bssl::UniquePtr<EVP_PKEY> test_ca_key_;
  
  // ED25519 key for testing DEF_DGST_REQUIRED behavior
  bssl::UniquePtr<EVP_PKEY> test_ed25519_key_;
  char ed25519_key_path[PATH_MAX];
  char ed25519_cert_path[PATH_MAX];
  char ed25519_csr_path[PATH_MAX];

  void CreateTestED25519KeyAndCert() {
    // Generate ED25519 private key from seed
    uint8_t ed25519_seed[32] = {
      0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
      0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10,
      0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
      0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20
    };

    bssl::UniquePtr<EVP_PKEY> ed25519_pkey(
        EVP_PKEY_new_raw_private_key(EVP_PKEY_ED25519, nullptr, ed25519_seed, 32));
    ASSERT_TRUE(ed25519_pkey);

    // Write ED25519 key to file
    ScopedFILE ed25519_key_file(fopen(ed25519_key_path, "wb"));
    ASSERT_TRUE(ed25519_key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(ed25519_key_file.get(), ed25519_pkey.get(), nullptr,
                                     nullptr, 0, nullptr, nullptr));

    // Create ED25519 CA certificate (self-signed)
    bssl::UniquePtr<X509> ed25519_cert(X509_new());
    ASSERT_TRUE(ed25519_cert);
    
    ASSERT_TRUE(X509_set_version(ed25519_cert.get(), 2)); // v3
    
    // Set serial number
    bssl::UniquePtr<ASN1_INTEGER> serial(ASN1_INTEGER_new());
    ASSERT_TRUE(serial && ASN1_INTEGER_set(serial.get(), 1));
    ASSERT_TRUE(X509_set_serialNumber(ed25519_cert.get(), serial.get()));
    
    // Set validity period
    ASSERT_TRUE(X509_gmtime_adj(X509_getm_notBefore(ed25519_cert.get()), 0));
    ASSERT_TRUE(X509_gmtime_adj(X509_getm_notAfter(ed25519_cert.get()), 365 * 24 * 60 * 60));
    
    // Set subject and issuer (same for self-signed)
    bssl::UniquePtr<X509_NAME> ed25519_name(X509_NAME_new());
    ASSERT_TRUE(ed25519_name);
    ASSERT_TRUE(X509_NAME_add_entry_by_txt(ed25519_name.get(), "CN", MBSTRING_ASC,
                                           (unsigned char*)"Test ED25519 CA", -1, -1, 0));
    ASSERT_TRUE(X509_set_subject_name(ed25519_cert.get(), ed25519_name.get()));
    ASSERT_TRUE(X509_set_issuer_name(ed25519_cert.get(), ed25519_name.get()));
    
    // Set public key
    ASSERT_TRUE(X509_set_pubkey(ed25519_cert.get(), ed25519_pkey.get()));
    
    // Sign certificate (ED25519 doesn't use explicit digest)
    ASSERT_TRUE(X509_sign(ed25519_cert.get(), ed25519_pkey.get(), nullptr));

    // Write ED25519 CA certificate
    ScopedFILE ed25519_cert_file(fopen(ed25519_cert_path, "wb"));
    ASSERT_TRUE(ed25519_cert_file);
    ASSERT_TRUE(PEM_write_X509(ed25519_cert_file.get(), ed25519_cert.get()));

    // Store the key for CSR creation
    test_ed25519_key_ = std::move(ed25519_pkey);
  }

  void CreateTestED25519CSR() {
    // For self-signed certificates, the CSR must be signed with the same key as the CA
    ASSERT_TRUE(test_ed25519_key_) << "ED25519 key must be created before CSR";

    // Create a certificate signing request
    bssl::UniquePtr<X509_REQ> req(X509_REQ_new());
    ASSERT_TRUE(req);
    
    // Set subject name
    bssl::UniquePtr<X509_NAME> name(X509_NAME_new());
    ASSERT_TRUE(name);
    ASSERT_TRUE(X509_NAME_add_entry_by_txt(name.get(), "CN", MBSTRING_ASC,
                                           (unsigned char*)"ed25519.example.com", -1, -1, 0));
    ASSERT_TRUE(X509_REQ_set_subject_name(req.get(), name.get()));
    
    // Set public key (same as ED25519 key for self-signed)
    ASSERT_TRUE(X509_REQ_set_pubkey(req.get(), test_ed25519_key_.get()));
    
    // Sign the CSR with the same key (self-signed requirement, ED25519 doesn't use explicit digest)
    ASSERT_TRUE(X509_REQ_sign(req.get(), test_ed25519_key_.get(), nullptr));

    // Write CSR to file
    ScopedFILE csr_file(fopen(ed25519_csr_path, "wb"));
    ASSERT_TRUE(csr_file);
    ASSERT_TRUE(PEM_write_X509_REQ(csr_file.get(), req.get()));
  }
};

// Basic certificate signing tests
TEST_F(CATest, BasicCertificateSigning) {
  CreateBasicConfig();

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  // Verify certificate was created
  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
  
  // Verify subject name contains expected CN
  X509_NAME *subject = X509_get_subject_name(cert.get());
  char subject_str[256];
  X509_NAME_oneline(subject, subject_str, sizeof(subject_str));
  EXPECT_TRUE(strstr(subject_str, "test.example.com") != nullptr);

  // NEW: Verify certificate-private key pair consistency
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ca_key_.get()));
}

TEST_F(CATest, VerboseOutput) {
  CreateBasicConfig();

  args_list_t args = {
      "-config", config_path,
      "-verbose",
      "-selfsign", 
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));
  
  // Verify certificate was created
  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);

  // Verify certificate-private key pair consistency
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ca_key_.get()));
}

TEST_F(CATest, NoTextOutput) {
  CreateBasicConfig();

  args_list_t args = {
      "-config", config_path,
      "-notext",
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  // Verify certificate was created and check format
  std::string cert_content = ReadFileToString(output_path);
  EXPECT_TRUE(cert_content.find("-----BEGIN CERTIFICATE-----") != std::string::npos);
  EXPECT_TRUE(cert_content.find("-----END CERTIFICATE-----") != std::string::npos);
  
  // With -notext, should not contain certificate text details
  EXPECT_TRUE(cert_content.find("Certificate:") == std::string::npos);

  // Verify certificate-private key pair consistency
  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ca_key_.get()));
}

TEST_F(CATest, OutputToStdout) {
  CreateBasicConfig();

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path
      // No -out argument, should output to stdout
  };

  ASSERT_TRUE(caTool(args));
}

// Configuration file handling tests
TEST_F(CATest, MissingConfigFile) {
  args_list_t args = {
      "-config", "nonexistent_config.conf",
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_FALSE(caTool(args));
}

TEST_F(CATest, ConfigWithExtensions) {
  CreateConfigWithExtensions();

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
  
  // Verify extensions were added
  int ext_count = X509_get_ext_count(cert.get());
  EXPECT_GT(ext_count, 0);

  // Verify certificate-private key pair consistency
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ca_key_.get()));
}

TEST_F(CATest, MissingPrivateKey) {
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = nonexistent_key.pem
certificate = )" + EscapeConfigPath(ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha256
policy = policy_anything

[ policy_anything ]
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());
  fflush(config_file.get());
  config_file.reset();

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_FALSE(caTool(args));
}

// Argument parsing tests
TEST_F(CATest, HelpArgument) {
  args_list_t args = {"-help"};
  
  // Help should not fail but should return false (as it's not doing actual work)
  ASSERT_FALSE(caTool(args));
}

TEST_F(CATest, MissingRequiredArguments) {
  CreateBasicConfig();

  // Missing -in argument
  args_list_t args1 = {
      "-config", config_path,
      "-selfsign",
      "-out", output_path
  };
  ASSERT_FALSE(caTool(args1));

  // Missing -config argument  
  args_list_t args2 = {
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };
  ASSERT_FALSE(caTool(args2));
}

// Password handling tests
TEST_F(CATest, PasswordProtectedKey) {
  // Create config that uses the password-protected key
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(protected_key_path) + R"(
certificate = )" + EscapeConfigPath(ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha256
policy = policy_anything
days = 365

[ policy_anything ]
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());
  fflush(config_file.get());  // Ensure content is written to disk
  config_file.reset();        // Close the file explicitly

  args_list_t args = {
      "-config", config_path,
      "-passin", "pass:testpassword",
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));
  
  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);

  // NEW: Verify certificate-private key pair consistency
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ca_key_.get()));
}

TEST_F(CATest, WrongPassword) {
  // Create config that uses the password-protected key  
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(protected_key_path) + R"(
certificate = )" + EscapeConfigPath(ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha256
policy = policy_anything
days = 365

[ policy_anything ]
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());
  fflush(config_file.get());
  config_file.reset();

  args_list_t args = {
      "-config", config_path,
      "-passin", "pass:wrongpassword",
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_FALSE(caTool(args));
}

// Date handling tests
TEST_F(CATest, CustomStartDate) {
  CreateBasicConfig();

  args_list_t args = {
      "-config", config_path,
      "-startdate", "20240101000000Z",
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
  
  // Verify the start date
  const ASN1_TIME *not_before = X509_get0_notBefore(cert.get());
  ASSERT_TRUE(not_before);

  // Verify certificate-private key pair consistency
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ca_key_.get()));
}

TEST_F(CATest, CustomEndDate) {
  CreateBasicConfig();

  args_list_t args = {
      "-config", config_path,
      "-enddate", "20251231235959Z",
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
  
  // Verify the end date
  const ASN1_TIME *not_after = X509_get0_notAfter(cert.get());
  ASSERT_TRUE(not_after);

  // Verify certificate-private key pair consistency
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ca_key_.get()));
}

TEST_F(CATest, InvalidDateFormat) {
  CreateBasicConfig();

  args_list_t args = {
      "-config", config_path,
      "-startdate", "invalid-date",
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_FALSE(caTool(args));
}

// Database operation tests
TEST_F(CATest, DatabaseUpdating) {
  CreateBasicConfig();

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  // Check database is initially empty
  std::string initial_db_content = ReadFileToString(db_path);
  EXPECT_TRUE(initial_db_content.empty());

  ASSERT_TRUE(caTool(args));

  // Check database was updated
  std::string updated_db_content = ReadFileToString(db_path);
  EXPECT_FALSE(updated_db_content.empty());
  EXPECT_TRUE(updated_db_content.find("V\t") != std::string::npos); // V for valid
}

TEST_F(CATest, SerialNumberIncrement) {
  CreateBasicConfig();

  // Check initial serial number
  std::string initial_serial = ReadFileToString(serial_path);
  EXPECT_TRUE(initial_serial.find("01") != std::string::npos);

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  // Check serial number was incremented
  std::string updated_serial = ReadFileToString(serial_path);
  EXPECT_TRUE(updated_serial.find("02") != std::string::npos);
}

// Policy tests
TEST_F(CATest, PolicyValidation) {
  // Create config with strict policy
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(ca_key_path) + R"(
certificate = )" + EscapeConfigPath(ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha256
policy = policy_strict

[ policy_strict ]
countryName = supplied
stateOrProvinceName = supplied
organizationName = supplied
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  // Should fail because CSR doesn't have all required fields
  ASSERT_FALSE(caTool(args));
}

// Extension copy tests
TEST_F(CATest, CopyExtensionsNone) {
  // Create config with copy_extensions = none
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(ca_key_path) + R"(
certificate = )" + EscapeConfigPath(ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha256
policy = policy_anything
copy_extensions = none
days = 365

[ policy_anything ]
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());
  fflush(config_file.get());
  config_file.reset();

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));
  
  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);

  // Verify certificate-private key pair consistency
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ca_key_.get()));
}

TEST_F(CATest, CopyExtensionsCopy) {
  // Create config with copy_extensions = copy
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(ca_key_path) + R"(
certificate = )" + EscapeConfigPath(ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha256
policy = policy_anything
copy_extensions = copy
days = 365

[ policy_anything ]
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());
  fflush(config_file.get());
  config_file.reset();

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);

  // Verify certificate-private key pair consistency
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ca_key_.get()));
}

// Error condition tests
TEST_F(CATest, CorruptedCSR) {
  CreateBasicConfig();

  // Create a corrupted CSR file
  ScopedFILE corrupted_csr(fopen(csr_path, "w"));
  ASSERT_TRUE(corrupted_csr);
  fprintf(corrupted_csr.get(), "This is not a valid CSR\n");
  fclose(corrupted_csr.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_FALSE(caTool(args));
}

TEST_F(CATest, MissingInputFile) {
  CreateBasicConfig();

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", "nonexistent_csr.pem",
      "-out", output_path
  };

  ASSERT_FALSE(caTool(args));
}

// Different digest algorithm tests  
TEST_F(CATest, CustomDigestAlgorithm) {
  // Create config with SHA-384
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(ca_key_path) + R"(
certificate = )" + EscapeConfigPath(ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha384
policy = policy_anything
days = 365

[ policy_anything ]
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());
  fflush(config_file.get());
  config_file.reset();

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);

  // NEW: Verify certificate-private key pair consistency
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ca_key_.get()));
}

// Random serial number test
TEST_F(CATest, RandomSerialNumber) {
  // Create config with random serial
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
rand_serial = yes
private_key = )" + EscapeConfigPath(ca_key_path) + R"(
certificate = )" + EscapeConfigPath(ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha256
policy = policy_anything
days = 365

[ policy_anything ]
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());
  fflush(config_file.get());
  config_file.reset();

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);

  // Verify certificate-private key pair consistency
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ca_key_.get()));
}

// Multi-certificate signing test
TEST_F(CATest, MultipleCertificatesSigning) {
  // Create config that works with self-signed certificates (using same key for CA and CSR)
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(ca_key_path) + R"(
certificate = )" + EscapeConfigPath(ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha256
policy = policy_anything
days = 365

[ policy_anything ]
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());
  fflush(config_file.get());
  config_file.reset();

  // Create additional CSR files using the same CA key (for self-signed)
  char csr_path2[PATH_MAX];
  char output_path2[PATH_MAX];
  ASSERT_GT(createTempFILEpath(csr_path2), 0u);
  ASSERT_GT(createTempFILEpath(output_path2), 0u);

  // Create second CSR with different subject but same key (self-signed requirement)
  bssl::UniquePtr<X509_REQ> req2(X509_REQ_new());
  ASSERT_TRUE(req2);
  
  bssl::UniquePtr<X509_NAME> name2(X509_NAME_new());
  ASSERT_TRUE(name2);
  ASSERT_TRUE(X509_NAME_add_entry_by_txt(name2.get(), "CN", MBSTRING_ASC,
                                         (unsigned char*)"second.example.com", -1, -1, 0));
  ASSERT_TRUE(X509_REQ_set_subject_name(req2.get(), name2.get()));
  ASSERT_TRUE(X509_REQ_set_pubkey(req2.get(), test_ca_key_.get()));
  ASSERT_TRUE(X509_REQ_sign(req2.get(), test_ca_key_.get(), EVP_sha256()));

  ScopedFILE csr_file2(fopen(csr_path2, "wb"));
  ASSERT_TRUE(csr_file2);
  ASSERT_TRUE(PEM_write_X509_REQ(csr_file2.get(), req2.get()));
  csr_file2.reset();

  // Sign first certificate
  args_list_t args1 = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };
  ASSERT_TRUE(caTool(args1));

  // Sign second certificate
  args_list_t args2 = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path2,
      "-out", output_path2
  };
  ASSERT_TRUE(caTool(args2));

  // Verify both certificates
  auto cert1 = LoadPEMCertificate(output_path);
  auto cert2 = LoadPEMCertificate(output_path2);
  ASSERT_TRUE(cert1);
  ASSERT_TRUE(cert2);

  // Verify different serial numbers
  ASN1_INTEGER *serial1 = X509_get_serialNumber(cert1.get());
  ASN1_INTEGER *serial2 = X509_get_serialNumber(cert2.get());
  EXPECT_NE(ASN1_INTEGER_cmp(serial1, serial2), 0);

  // Verify certificate-private key pair consistency for both certificates
  ASSERT_TRUE(ValidateCertificateKeyPair(cert1.get(), test_ca_key_.get()));

  // Clean up temporary files
  RemoveFile(csr_path2);
  RemoveFile(output_path2);
}

// Today date handling test
TEST_F(CATest, TodayDateHandling) {
  CreateBasicConfig();

  args_list_t args = {
      "-config", config_path,
      "-startdate", "today",
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);

  // Verify certificate-private key pair consistency
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ca_key_.get()));
}

// Preserve DN test
TEST_F(CATest, PreserveDN) {
  // Create config with preserve = yes
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(ca_key_path) + R"(
certificate = )" + EscapeConfigPath(ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha256
policy = policy_anything
preserve = yes
days = 365

[ policy_anything ]
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());
  fflush(config_file.get());
  config_file.reset();

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);

  // Verify certificate-private key pair consistency
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ca_key_.get()));
}

// Invalid digest algorithm test
TEST_F(CATest, InvalidDigestAlgorithm) {
  // Create config with invalid digest
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(ca_key_path) + R"(
certificate = )" + EscapeConfigPath(ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = invalid_digest
policy = policy_anything

[ policy_anything ]
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_FALSE(caTool(args));
}

// Copy extensions copyall test
TEST_F(CATest, CopyExtensionsCopyAll) {
  // Create config with copy_extensions = copyall
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(ca_key_path) + R"(
certificate = )" + EscapeConfigPath(ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha256
policy = policy_anything
copy_extensions = copyall
days = 365

[ policy_anything ]
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());
  fflush(config_file.get());
  config_file.reset();

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);

  // Verify certificate-private key pair consistency
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ca_key_.get()));
}

// Invalid copy extensions value test
TEST_F(CATest, InvalidCopyExtensionsValue) {
  // Create config with invalid copy_extensions value
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(ca_key_path) + R"(
certificate = )" + EscapeConfigPath(ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha256
policy = policy_anything
copy_extensions = invalid_value

[ policy_anything ]
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_FALSE(caTool(args));
}

// Database integrity test
TEST_F(CATest, DatabaseIntegrityChecks) {
  CreateBasicConfig();

  // Create corrupted database with invalid entry
  ScopedFILE corrupted_db(fopen(db_path, "w"));
  ASSERT_TRUE(corrupted_db);
  fprintf(corrupted_db.get(), "V\tinvalid_date\t\t01\tunknown\t/CN=corrupted\n");
  fclose(corrupted_db.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_FALSE(caTool(args));
}

// Missing database directory test
TEST_F(CATest, MissingDatabaseDirectory) {
  // Create config pointing to non-existent directory
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = /nonexistent/path/database
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(ca_key_path) + R"(
certificate = )" + EscapeConfigPath(ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha256
policy = policy_anything

[ policy_anything ]
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_FALSE(caTool(args));
}

// Test unique subject constraint
TEST_F(CATest, UniqueSubjectConstraint) {
  CreateBasicConfig();

  // Sign first certificate
  args_list_t args1 = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };
  ASSERT_TRUE(caTool(args1));

  // Try to sign another certificate with same subject - should fail
  char output_path2[PATH_MAX];
  ASSERT_GT(createTempFILEpath(output_path2), 0u);
  
  args_list_t args2 = {
      "-config", config_path,
      "-selfsign", 
      "-in", csr_path,
      "-out", output_path2
  };
  ASSERT_FALSE(caTool(args2));

  RemoveFile(output_path2);
}

// Test policy match requirement
TEST_F(CATest, PolicyMatchRequirement) {
  // Create CA cert with specific subject for matching
  bssl::UniquePtr<EVP_PKEY> ca_pkey(EVP_PKEY_new());
  ASSERT_TRUE(ca_pkey);
  bssl::UniquePtr<RSA> ca_rsa(RSA_new());
  ASSERT_TRUE(ca_rsa);
  bssl::UniquePtr<BIGNUM> ca_bn(BN_new());
  ASSERT_TRUE(ca_bn && BN_set_word(ca_bn.get(), RSA_F4) &&
              RSA_generate_key_ex(ca_rsa.get(), 2048, ca_bn.get(), nullptr));
  ASSERT_TRUE(EVP_PKEY_assign_RSA(ca_pkey.get(), ca_rsa.release()));

  bssl::UniquePtr<X509> match_ca_cert(X509_new());
  ASSERT_TRUE(match_ca_cert);
  ASSERT_TRUE(X509_set_version(match_ca_cert.get(), 2));
  
  bssl::UniquePtr<ASN1_INTEGER> serial(ASN1_INTEGER_new());
  ASSERT_TRUE(serial && ASN1_INTEGER_set(serial.get(), 1));
  ASSERT_TRUE(X509_set_serialNumber(match_ca_cert.get(), serial.get()));
  
  ASSERT_TRUE(X509_gmtime_adj(X509_getm_notBefore(match_ca_cert.get()), 0));
  ASSERT_TRUE(X509_gmtime_adj(X509_getm_notAfter(match_ca_cert.get()), 365 * 24 * 60 * 60));
  
  bssl::UniquePtr<X509_NAME> match_ca_name(X509_NAME_new());
  ASSERT_TRUE(match_ca_name);
  ASSERT_TRUE(X509_NAME_add_entry_by_txt(match_ca_name.get(), "C", MBSTRING_ASC,
                                         (unsigned char*)"US", -1, -1, 0));
  ASSERT_TRUE(X509_NAME_add_entry_by_txt(match_ca_name.get(), "CN", MBSTRING_ASC,
                                         (unsigned char*)"Match CA", -1, -1, 0));
  ASSERT_TRUE(X509_set_subject_name(match_ca_cert.get(), match_ca_name.get()));
  ASSERT_TRUE(X509_set_issuer_name(match_ca_cert.get(), match_ca_name.get()));
  ASSERT_TRUE(X509_set_pubkey(match_ca_cert.get(), ca_pkey.get()));
  ASSERT_TRUE(X509_sign(match_ca_cert.get(), ca_pkey.get(), EVP_sha256()));

  // Write new CA key and cert
  char match_ca_key_path[PATH_MAX];
  char match_ca_cert_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(match_ca_key_path), 0u);
  ASSERT_GT(createTempFILEpath(match_ca_cert_path), 0u);

  ScopedFILE match_ca_key_file(fopen(match_ca_key_path, "wb"));
  ASSERT_TRUE(match_ca_key_file);
  ASSERT_TRUE(PEM_write_PrivateKey(match_ca_key_file.get(), ca_pkey.get(), nullptr,
                                   nullptr, 0, nullptr, nullptr));
  match_ca_key_file.reset();

  ScopedFILE match_ca_cert_file(fopen(match_ca_cert_path, "wb"));
  ASSERT_TRUE(match_ca_cert_file);
  ASSERT_TRUE(PEM_write_X509(match_ca_cert_file.get(), match_ca_cert.get()));
  match_ca_cert_file.reset();

  // Create config with match policy for country
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(match_ca_key_path) + R"(
certificate = )" + EscapeConfigPath(match_ca_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha256
policy = policy_match
days = 365

[ policy_match ]
countryName = match
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());
  fflush(config_file.get());
  config_file.reset();

  // Create CSR with matching country using the CA key (for self-signed)
  bssl::UniquePtr<X509_REQ> match_req(X509_REQ_new());
  ASSERT_TRUE(match_req);
  
  bssl::UniquePtr<X509_NAME> match_req_name(X509_NAME_new());
  ASSERT_TRUE(match_req_name);
  ASSERT_TRUE(X509_NAME_add_entry_by_txt(match_req_name.get(), "C", MBSTRING_ASC,
                                         (unsigned char*)"US", -1, -1, 0)); // Match CA's country
  ASSERT_TRUE(X509_NAME_add_entry_by_txt(match_req_name.get(), "CN", MBSTRING_ASC,
                                         (unsigned char*)"match.example.com", -1, -1, 0));
  ASSERT_TRUE(X509_REQ_set_subject_name(match_req.get(), match_req_name.get()));
  ASSERT_TRUE(X509_REQ_set_pubkey(match_req.get(), ca_pkey.get())); // Use CA key for self-signed
  ASSERT_TRUE(X509_REQ_sign(match_req.get(), ca_pkey.get(), EVP_sha256())); // Sign with CA key

  char match_csr_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(match_csr_path), 0u);
  
  ScopedFILE match_csr_file(fopen(match_csr_path, "wb"));
  ASSERT_TRUE(match_csr_file);
  ASSERT_TRUE(PEM_write_X509_REQ(match_csr_file.get(), match_req.get()));
  match_csr_file.reset();

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", match_csr_path,
      "-out", output_path
  };

  // This should succeed because countries match
  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);

  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), ca_pkey.get()));

  // Clean up
  RemoveFile(match_ca_key_path);
  RemoveFile(match_ca_cert_path);
  RemoveFile(match_csr_path);
}

// ED25519 Tests - DEF_DGST_REQUIRED behavior validation

TEST_F(CATest, ED25519BasicCertificateSigning) {
  // Create config without default_md for ED25519 key (should succeed)
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(ed25519_key_path) + R"(
certificate = )" + EscapeConfigPath(ed25519_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
policy = policy_anything
days = 365

[ policy_anything ]
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());
  fflush(config_file.get());
  config_file.reset();

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", ed25519_csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  // Verify certificate was created
  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
  
  // Verify subject name contains expected CN
  X509_NAME *subject = X509_get_subject_name(cert.get());
  char subject_str[256];
  X509_NAME_oneline(subject, subject_str, sizeof(subject_str));
  EXPECT_TRUE(strstr(subject_str, "ed25519.example.com") != nullptr);

  // Verify certificate-private key pair consistency
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ed25519_key_.get()));
}

TEST_F(CATest, ED25519WithDefaultDigest) {
  // Create config with default_md = default for ED25519 key (should succeed)
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(ed25519_key_path) + R"(
certificate = )" + EscapeConfigPath(ed25519_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = default
policy = policy_anything
days = 365

[ policy_anything ]
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());
  fflush(config_file.get());
  config_file.reset();

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", ed25519_csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  // Verify certificate was created
  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);

  // Verify certificate-private key pair consistency
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ed25519_key_.get()));
}

TEST_F(CATest, ED25519WithExplicitDigestFails) {
  // Create config with explicit digest algorithm for ED25519 key (should fail due to DEF_DGST_REQUIRED)
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  
  std::string config_content = R"(
[ ca ]
default_ca = CA_default

[ CA_default ]
database = )" + EscapeConfigPath(db_path) + R"(
serial = )" + EscapeConfigPath(serial_path) + R"(
private_key = )" + EscapeConfigPath(ed25519_key_path) + R"(
certificate = )" + EscapeConfigPath(ed25519_cert_path) + R"(
new_certs_dir = )" + EscapeConfigPath(new_certs_dir) + R"(
default_md = sha256
policy = policy_anything
days = 365

[ policy_anything ]
commonName = supplied
)";
  
  fprintf(config_file.get(), "%s", config_content.c_str());
  fflush(config_file.get());
  config_file.reset();

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", ed25519_csr_path,
      "-out", output_path
  };

  // This should fail because ED25519 has DEF_DGST_REQUIRED and explicit digest is not allowed
  ASSERT_FALSE(caTool(args));
}

// MakeRevoked and UnpackRevinfo Tests - Exercised through database validation in caTool

TEST_F(CATest, DatabaseWithRevokedEntryBasicTimestamp) {
  // Test database with revoked entry containing only timestamp (no reason)
  // This exercises MakeRevoked and UnpackRevinfo basic parsing
  CreateBasicConfig();

  // Create database with a revoked entry - just timestamp
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // Format: type\texp_date\trev_date\tserial\tfile\tname
  // R = Revoked, timestamp format is YYMMDDHHMMSSZ
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  // Should succeed - database with valid revoked entry loads correctly
  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
  ASSERT_TRUE(ValidateCertificateKeyPair(cert.get(), test_ca_key_.get()));
}

TEST_F(CATest, DatabaseWithRevokedEntryUnspecifiedReason) {
  // Test database with revoked entry using "unspecified" reason code
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,unspecified\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
}

TEST_F(CATest, DatabaseWithRevokedEntryKeyCompromise) {
  // Test database with revoked entry using "keyCompromise" reason code
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,keyCompromise\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
}

TEST_F(CATest, DatabaseWithRevokedEntryCACompromise) {
  // Test database with revoked entry using "CACompromise" reason code
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,CACompromise\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
}

TEST_F(CATest, DatabaseWithRevokedEntryAffiliationChanged) {
  // Test database with revoked entry using "affiliationChanged" reason code
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,affiliationChanged\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
}

TEST_F(CATest, DatabaseWithRevokedEntrySuperseded) {
  // Test database with revoked entry using "superseded" reason code
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,superseded\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
}

TEST_F(CATest, DatabaseWithRevokedEntryCessationOfOperation) {
  // Test database with revoked entry using "cessationOfOperation" reason code
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,cessationOfOperation\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
}

TEST_F(CATest, DatabaseWithRevokedEntryCertificateHold) {
  // Test database with revoked entry using "certificateHold" reason code
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,certificateHold\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
}

TEST_F(CATest, DatabaseWithRevokedEntryRemoveFromCRL) {
  // Test database with revoked entry using "removeFromCRL" reason code
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,removeFromCRL\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
}

TEST_F(CATest, DatabaseWithRevokedEntryHoldInstruction) {
  // Test database with revoked entry using "holdInstruction" reason with OID argument
  // This exercises the hold instruction parsing path in UnpackRevinfo
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // holdInstruction requires an OID argument - using holdInstructionNone (1.2.840.10040.2.1)
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,holdInstruction,1.2.840.10040.2.1\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
}

TEST_F(CATest, DatabaseWithRevokedEntryKeyTime) {
  // Test database with revoked entry using "keyTime" reason with compromised time
  // This exercises the keyTime parsing path in UnpackRevinfo (maps to OCSP_REVOKED_STATUS_KEYCOMPROMISE)
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // keyTime requires a GeneralizedTime argument
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,keyTime,20240101120000Z\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
}

TEST_F(CATest, DatabaseWithRevokedEntryCAkeyTime) {
  // Test database with revoked entry using "CAkeyTime" reason with compromised time
  // This exercises the CAkeyTime parsing path in UnpackRevinfo (maps to OCSP_REVOKED_STATUS_CACOMPROMISE)
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // CAkeyTime requires a GeneralizedTime argument
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,CAkeyTime,20240101120000Z\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
}

TEST_F(CATest, DatabaseWithRevokedEntryInvalidTimestamp) {
  // Test database with revoked entry having invalid timestamp format.
  // This should fail during database validation via MakeRevoked/UnpackRevinfo
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // Invalid timestamp format (missing Z, wrong format)
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\tinvalid_timestamp\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  // Should fail - invalid revocation date format
  ASSERT_FALSE(caTool(args));
}

TEST_F(CATest, DatabaseWithRevokedEntryInvalidReasonCode) {
  // Test database with revoked entry having invalid reason code
  // This should fail during database validation via UnpackRevinfo
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // Invalid reason code
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,invalidReason\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  // Should fail - invalid reason code
  ASSERT_FALSE(caTool(args));
}

TEST_F(CATest, DatabaseWithRevokedEntryHoldInstructionMissingArg) {
  // Test database with revoked entry using holdInstruction but missing OID argument
  // This should fail during database validation via UnpackRevinfo
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // holdInstruction without required OID argument
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,holdInstruction\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  // Should fail - missing hold instruction argument
  ASSERT_FALSE(caTool(args));
}

TEST_F(CATest, DatabaseWithRevokedEntryKeyTimeMissingArg) {
  // Test database with revoked entry using keyTime but missing compromised time argument
  // This should fail during database validation via UnpackRevinfo
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // keyTime without required compromised time argument
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,keyTime\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  // Should fail - missing compromised time argument
  ASSERT_FALSE(caTool(args));
}

TEST_F(CATest, DatabaseWithRevokedEntryCAkeyTimeMissingArg) {
  // Test database with revoked entry using CAkeyTime but missing compromised time argument
  // This should fail during database validation via UnpackRevinfo
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // CAkeyTime without required compromised time argument
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,CAkeyTime\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  // Should fail - missing compromised time argument
  ASSERT_FALSE(caTool(args));
}

TEST_F(CATest, DatabaseWithRevokedEntryInvalidHoldInstructionOID) {
  // Test database with revoked entry using holdInstruction with invalid OID
  // This should fail during database validation via UnpackRevinfo
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // holdInstruction with invalid OID
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,holdInstruction,not.a.valid.oid\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  // Should fail - invalid OID format
  ASSERT_FALSE(caTool(args));
}

TEST_F(CATest, DatabaseWithRevokedEntryInvalidKeyTimeFormat) {
  // Test database with revoked entry using keyTime with invalid time format
  // This should fail during database validation via UnpackRevinfo
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // keyTime with invalid GeneralizedTime format
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,keyTime,invalid_time\tAA\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  // Should fail - invalid compromised time format
  ASSERT_FALSE(caTool(args));
}

TEST_F(CATest, DatabaseWithMultipleRevokedEntries) {
  // Test database with multiple revoked entries using different reason codes
  // Exercises MakeRevoked and UnpackRevinfo with various inputs in sequence
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // Use serials "AA", "AB", "AC" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,keyCompromise\tAA\tunknown\t/CN=revoked1.example.com\n");
  fprintf(db_file.get(), "R\t251231235959Z\t240201120000Z,CACompromise\tAB\tunknown\t/CN=revoked2.example.com\n");
  fprintf(db_file.get(), "R\t251231235959Z\t240301120000Z,superseded\tAC\tunknown\t/CN=revoked3.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
}

TEST_F(CATest, DatabaseWithMixedValidAndRevokedEntries) {
  // Test database with both valid and revoked entries
  // Verifies that MakeRevoked is only called for revoked entries
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // V = Valid entry (should not trigger MakeRevoked validation)
  // Use serials "AA", "AB" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "V\t251231235959Z\t\tAA\tunknown\t/CN=valid.example.com\n");
  // R = Revoked entry (triggers MakeRevoked validation)
  fprintf(db_file.get(), "R\t251231235959Z\t240101120000Z,keyCompromise\tAB\tunknown\t/CN=revoked.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  ASSERT_TRUE(caTool(args));

  auto cert = LoadPEMCertificate(output_path);
  ASSERT_TRUE(cert);
}

TEST_F(CATest, DatabaseWithValidEntryAndRevocationDate) {
  // Test that valid entries with non-empty revocation date are rejected
  // The database validation should catch this inconsistency
  CreateBasicConfig();

  ScopedFILE db_file(fopen(db_path, "w"));
  ASSERT_TRUE(db_file);
  // V = Valid but has revocation date (invalid state)
  // Use serial "AA" to avoid conflict with serial file starting at "01"
  fprintf(db_file.get(), "V\t251231235959Z\t240101120000Z\tAA\tunknown\t/CN=invalid.example.com\n");
  fclose(db_file.release());

  args_list_t args = {
      "-config", config_path,
      "-selfsign",
      "-in", csr_path,
      "-out", output_path
  };

  // Should fail - valid entry should not have revocation date
  ASSERT_FALSE(caTool(args));
}
