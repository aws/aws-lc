// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/rsa.h>
#include <stdio.h>
#include <string.h>
#if defined(OPENSSL_WINDOWS)
#include <direct.h>
#include <io.h>
#else
#include <sys/stat.h>
#include <unistd.h>
#endif
#include "../tool/internal.h"

#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "../crypto/test/test_util.h"
#include "internal.h"
#include "test_util.h"

class ReqTest : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(input_key_path), 0u);
    ASSERT_GT(createTempFILEpath(output_key_path), 0u);
    ASSERT_GT(createTempFILEpath(csr_path), 0u);
    ASSERT_GT(createTempFILEpath(cert_path), 0u);
    ASSERT_GT(createTempFILEpath(config_path), 0u);
    ASSERT_GT(createTempFILEpath(protected_key_path), 0u);

    // Create a temporary directory and change to it
    // This allows testing the default "privkey.pem" behavior in an isolated
    // location
    ASSERT_GT(createTempDirPath(temp_dir_path), 0u);
#if defined(OPENSSL_WINDOWS)
    ASSERT_TRUE(_getcwd(original_dir, PATH_MAX) != nullptr);
    ASSERT_EQ(_chdir(temp_dir_path), 0);
#else
    ASSERT_TRUE(getcwd(original_dir, PATH_MAX) != nullptr);
    ASSERT_EQ(chdir(temp_dir_path), 0);
#endif

    // Create a test private key
    bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
    ASSERT_TRUE(pkey);
    bssl::UniquePtr<RSA> rsa(RSA_new());
    ASSERT_TRUE(rsa);
    bssl::UniquePtr<BIGNUM> bn(BN_new());
    ASSERT_TRUE(bn && rsa && BN_set_word(bn.get(), RSA_F4) &&
                RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr));
    ASSERT_TRUE(EVP_PKEY_assign_RSA(pkey.get(), rsa.release()));

    // Write unencrypted key for -key input
    ScopedFILE key_file(fopen(input_key_path, "wb"));
    ASSERT_TRUE(key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(key_file.get(), pkey.get(), nullptr,
                                     nullptr, 0, nullptr, nullptr));

    // Write encrypted key for -key input with -passin
    ScopedFILE protected_key_file(fopen(protected_key_path, "wb"));
    ASSERT_TRUE(protected_key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(
        protected_key_file.get(), pkey.get(), EVP_aes_256_cbc(),
        (unsigned char *)"testpassword", 12, nullptr, nullptr));
  }

  void TearDown() override {
    // Clean up files (note: we're still in temp_dir_path from SetUp)
    RemoveFile(input_key_path);
    RemoveFile(output_key_path);
    RemoveFile(csr_path);
    RemoveFile(cert_path);
    RemoveFile(config_path);
    RemoveFile(protected_key_path);

    // Remove privkey.pem in current directory (temp_dir_path)
    RemoveFile("privkey.pem");

    // Change back to original directory and remove temp directory
    if (original_dir[0] != '\0') {
#if defined(OPENSSL_WINDOWS)
      int ret = _chdir(original_dir);
      if (ret == 0 && temp_dir_path[0] != '\0') {
        _rmdir(temp_dir_path);
      }
#else
      int ret = chdir(original_dir);
      if (ret == 0 && temp_dir_path[0] != '\0') {
        rmdir(temp_dir_path);
      }
#endif
    }
  }

  char input_key_path[PATH_MAX];   // For -key (input)
  char output_key_path[PATH_MAX];  // For -keyout (output)
  char csr_path[PATH_MAX];
  char cert_path[PATH_MAX];
  char config_path[PATH_MAX];
  char protected_key_path[PATH_MAX];
  char temp_dir_path[PATH_MAX];  // Temporary directory for test isolation
  char original_dir[PATH_MAX];   // Original working directory
};

TEST_F(ReqTest, GenerateRSAKey) {
  args_list_t args = {
      "-new",          "-newkey", "rsa:3072", "-nodes", "-keyout",
      output_key_path, "-out",    csr_path,   "-subj",  "/CN=test.example.com"};

  ASSERT_TRUE(reqTool(args));

  bssl::UniquePtr<EVP_PKEY> key(DecryptPrivateKey(output_key_path, nullptr));
  ASSERT_TRUE(key);
  EXPECT_EQ(EVP_PKEY_id(key.get()), EVP_PKEY_RSA);

  const RSA *rsa = EVP_PKEY_get0_RSA(key.get());
  ASSERT_TRUE(rsa);
  EXPECT_EQ(RSA_bits(rsa), 3072u);
}

TEST_F(ReqTest, NewkeyRSADefault) {
  args_list_t args = {"-new",    "-newkey",       "rsa",  "-nodes",
                      "-keyout", output_key_path, "-out", csr_path,
                      "-subj",   "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));

  bssl::UniquePtr<EVP_PKEY> key(DecryptPrivateKey(output_key_path, nullptr));
  ASSERT_TRUE(key);
  EXPECT_EQ(EVP_PKEY_id(key.get()), EVP_PKEY_RSA);

  const RSA *rsa = EVP_PKEY_get0_RSA(key.get());
  ASSERT_TRUE(rsa);
  EXPECT_EQ(RSA_bits(rsa), 2048u);  // Should default to 2048
}

TEST_F(ReqTest, KeyLengthVariations) {
  int key_sizes[] = {2048, 3072, 4096};  // FIPS-compliant sizes
  for (int size : key_sizes) {
    std::string keyspec = "rsa:" + std::to_string(size);
    args_list_t args = {"-new",    "-newkey",       keyspec.c_str(), "-nodes",
                        "-keyout", output_key_path, "-out",          csr_path,
                        "-subj",   "/CN=test.com"};

    ASSERT_TRUE(reqTool(args));

    bssl::UniquePtr<EVP_PKEY> key(DecryptPrivateKey(output_key_path, nullptr));
    ASSERT_TRUE(key);
    const RSA *rsa = EVP_PKEY_get0_RSA(key.get());
    ASSERT_TRUE(rsa);
    EXPECT_EQ(RSA_bits(rsa), static_cast<unsigned int>(size));
  }
}

TEST_F(ReqTest, InvalidKeySizeFallback) {
  // Test that invalid key size (rsa:abc) defaults to default key length
  args_list_t args = {"-new",    "-newkey",       "rsa:abc", "-nodes",
                      "-keyout", output_key_path, "-out",    csr_path,
                      "-subj",   "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));

  bssl::UniquePtr<EVP_PKEY> key(DecryptPrivateKey(output_key_path, nullptr));
  ASSERT_TRUE(key);
  EXPECT_EQ(EVP_PKEY_id(key.get()), EVP_PKEY_RSA);

  const RSA *rsa = EVP_PKEY_get0_RSA(key.get());
  ASSERT_TRUE(rsa);
  EXPECT_EQ(RSA_bits(rsa), 2048u);  // Should default to 2048
}

TEST_F(ReqTest, DigestAlgorithms) {
  std::vector<std::string> digests = {"-sha256", "-sha384", "-sha512", "-sha1"};
  for (const auto &digest : digests) {
    args_list_t args = {"-new",   digest.c_str(), "-newkey",       "rsa:2048",
                        "-nodes", "-keyout",      output_key_path, "-out",
                        csr_path, "-subj",        "/CN=test.com"};

    EXPECT_TRUE(reqTool(args)) << "Failed with digest: " << digest;
  }
}

TEST_F(ReqTest, EncryptedPrivateKey) {
  args_list_t args = {"-new",          "-newkey", "rsa:2048",      "-passout",
                      "pass:testpass", "-keyout", output_key_path, "-out",
                      csr_path,        "-subj",   "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));

  std::string key_content = ReadFileToString(output_key_path);
  EXPECT_TRUE(key_content.find("ENCRYPTED") != std::string::npos);

  bssl::UniquePtr<EVP_PKEY> key(DecryptPrivateKey(output_key_path, "testpass"));
  ASSERT_TRUE(key);
}

TEST_F(ReqTest, DefaultKeyoutPath) {
  // Test that key is written to privkey.pem when -keyout is not specified
  args_list_t args = {"-new", "-newkey", "rsa:2048", "-nodes",
                      "-out", csr_path,  "-subj",    "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));

  // Verify key was written to default privkey.pem
  bssl::UniquePtr<EVP_PKEY> key(DecryptPrivateKey("privkey.pem", nullptr));
  ASSERT_TRUE(key);
  EXPECT_EQ(EVP_PKEY_id(key.get()), EVP_PKEY_RSA);
}

TEST_F(ReqTest, SuppressedKeyWrite) {
  // Verify if default_keyfile is missing from config, no private key write
  // should happen
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[req]\n"
          "distinguished_name = req_dn\n"
          "encrypt_key = yes\n"
          "[req_dn]\n"
          "CN = Common Name\n");
  fclose(config_file.release());

  args_list_t args = {"-new",   "-config", config_path,   "-out",
                      csr_path, "-subj",   "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));

  // Verify that privkey.pem was NOT created
  EXPECT_FALSE(access("privkey.pem", F_OK) == 0)
      << "privkey.pem should not be created";
}

TEST_F(ReqTest, X509SelfSignedCert) {
  args_list_t args = {"-new",          "-x509",    "-days",   "365",
                      "-newkey",       "rsa:2048", "-nodes",  "-keyout",
                      output_key_path, "-out",     cert_path, "-subj",
                      "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));

  auto cert = LoadPEMCertificate(cert_path);
  ASSERT_TRUE(cert);

  bssl::UniquePtr<EVP_PKEY> key(DecryptPrivateKey(output_key_path, nullptr));
  ASSERT_TRUE(key);
  EXPECT_EQ(X509_verify(cert.get(), key.get()), 1);
}

TEST_F(ReqTest, BasicConfig) {
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[req]\n"
          "default_bits = 3072\n"
          "default_md = sha384\n"
          "distinguished_name = req_dn\n"
          "[req_dn]\n"
          "CN = Common Name\n");
  fclose(config_file.release());

  args_list_t args = {"-new",    "-config",       config_path, "-nodes",
                      "-keyout", output_key_path, "-out",      csr_path,
                      "-subj",   "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));

  bssl::UniquePtr<EVP_PKEY> key(DecryptPrivateKey(output_key_path, nullptr));
  ASSERT_TRUE(key);
  const RSA *rsa = EVP_PKEY_get0_RSA(key.get());
  ASSERT_TRUE(rsa);
  EXPECT_EQ(RSA_bits(rsa), 3072u);
}

TEST_F(ReqTest, ExistingKeyFile) {
  // Use existing key for new CSR
  args_list_t use_args = {"-new", "-key",   input_key_path, "-nodes",
                          "-out", csr_path, "-subj",        "/CN=second.com"};
  ASSERT_TRUE(reqTool(use_args));
}

TEST_F(ReqTest, SubjectNameParsing) {
  std::vector<std::string> subjects = {
      "/CN=test.com", "/C=US/ST=CA/L=SF/O=Test/CN=test.com",
      "/CN=test.com/emailAddress=test@example.com"};

  for (const auto &subj : subjects) {
    args_list_t args = {"-new",    "-newkey",       "rsa:2048", "-nodes",
                        "-keyout", output_key_path, "-out",     csr_path,
                        "-subj",   subj.c_str()};

    EXPECT_TRUE(reqTool(args)) << "Failed with subject: " << subj;
  }
}

TEST_F(ReqTest, DigestSelectionFromConfig) {
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[req]\n"
          "default_md = sha512\n"
          "distinguished_name = req_dn\n"
          "[req_dn]\n");
  fclose(config_file.release());

  args_list_t args = {"-new",     "-config", config_path, "-newkey",
                      "rsa:2048", "-nodes",  "-keyout",   output_key_path,
                      "-out",     csr_path,  "-subj",     "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));
}

TEST_F(ReqTest, KeyEncryptionFromConfig) {
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[req]\n"
          "encrypt_key = yes\n"
          "distinguished_name = req_dn\n"
          "[req_dn]\n");
  fclose(config_file.release());

  args_list_t args = {"-new",          "-config",  config_path,     "-newkey",
                      "rsa:2048",      "-passout", "pass:testpass", "-keyout",
                      output_key_path, "-out",     csr_path,        "-subj",
                      "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));

  std::string key_content = ReadFileToString(output_key_path);
  EXPECT_TRUE(key_content.find("ENCRYPTED") != std::string::npos);
}

TEST_F(ReqTest, ReqExtensions) {
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[req]\n"
          "distinguished_name = req_dn\n"
          "[req_dn]\n"
          "[test_ext]\n"
          "basicConstraints = CA:FALSE\n"
          "keyUsage = digitalSignature, keyEncipherment\n");
  fclose(config_file.release());

  args_list_t args = {"-new",     "-config",       config_path, "-extensions",
                      "test_ext", "-newkey",       "rsa:2048",  "-nodes",
                      "-keyout",  output_key_path, "-out",      csr_path,
                      "-subj",    "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));
}

TEST_F(ReqTest, X509Extensions) {
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[req]\n"
          "distinguished_name = req_dn\n"
          "[req_dn]\n"
          "[custom_ext]\n"
          "basicConstraints = CA:FALSE\n"
          "keyUsage = digitalSignature, keyEncipherment\n"
          "subjectAltName = DNS:alt.example.com\n");
  fclose(config_file.release());

  args_list_t args = {"-x509",       "-new",       "-config",       config_path,
                      "-extensions", "custom_ext", "-newkey",       "rsa:2048",
                      "-nodes",      "-keyout",    output_key_path, "-out",
                      cert_path,     "-subj",      "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));
}

TEST_F(ReqTest, ReqExtensionsFromConfig) {
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[req]\n"
          "distinguished_name = req_dn\n"
          "req_extensions = v3_req\n"
          "[req_dn]\n"
          "[v3_req]\n"
          "basicConstraints = CA:FALSE\n"
          "keyUsage = nonRepudiation, digitalSignature, keyEncipherment\n");
  fclose(config_file.release());

  args_list_t args = {"-new",     "-config", config_path, "-newkey",
                      "rsa:2048", "-nodes",  "-keyout",   output_key_path,
                      "-out",     csr_path,  "-subj",     "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));
}

TEST_F(ReqTest, X509ExtensionsFromConfig) {
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[req]\n"
          "distinguished_name = req_dn\n"
          "x509_extensions = v3_ca\n"
          "[req_dn]\n"
          "[v3_ca]\n"
          "basicConstraints = critical,CA:true\n"
          "keyUsage = critical,keyCertSign,cRLSign\n");
  fclose(config_file.release());

  args_list_t args = {"-x509",         "-new",     "-config", config_path,
                      "-newkey",       "rsa:2048", "-nodes",  "-keyout",
                      output_key_path, "-out",     cert_path, "-subj",
                      "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));
}

TEST_F(ReqTest, ReqExtensionsFromEmptyConfig) {
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(), "[req]\n");
  fclose(config_file.release());

  args_list_t args = {"-new",     "-config", config_path, "-newkey",
                      "rsa:2048", "-nodes",  "-keyout",   output_key_path,
                      "-out",     csr_path,  "-subj",     "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));
}

TEST_F(ReqTest, X509ExtensionsFromEmptyConfig) {
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(), "[req]\n");
  fclose(config_file.release());

  args_list_t args = {"-x509",         "-new",     "-config", config_path,
                      "-newkey",       "rsa:2048", "-nodes",  "-keyout",
                      output_key_path, "-out",     cert_path, "-subj",
                      "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));
}

TEST_F(ReqTest, OutformPEM) {
  args_list_t args = {"-new",     "-newkey", "rsa:2048", "-nodes",
                      "-outform", "PEM",     "-keyout",  output_key_path,
                      "-out",     csr_path,  "-subj",    "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));
  std::string csr_content = ReadFileToString(csr_path);
  EXPECT_TRUE(csr_content.find("-----BEGIN CERTIFICATE REQUEST-----") !=
              std::string::npos);
  EXPECT_TRUE(csr_content.find("-----END CERTIFICATE REQUEST-----") !=
              std::string::npos);
}


TEST_F(ReqTest, OutformDER) {
  args_list_t args = {"-new",     "-newkey", "rsa:2048", "-nodes",
                      "-outform", "DER",     "-keyout",  output_key_path,
                      "-out",     csr_path,  "-subj",    "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));

  ScopedFILE file(fopen(csr_path, "rb"));
  ASSERT_TRUE(file);
  bssl::UniquePtr<X509_REQ> req(d2i_X509_REQ_fp(file.get(), nullptr));
  EXPECT_TRUE(req);
}

TEST_F(ReqTest, OutformDERX509) {
  args_list_t args = {"-new",          "-x509",    "-newkey", "rsa:2048",
                      "-nodes",        "-outform", "DER",     "-keyout",
                      output_key_path, "-out",     cert_path, "-subj",
                      "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));

  ScopedFILE file(fopen(cert_path, "rb"));
  ASSERT_TRUE(file);
  bssl::UniquePtr<X509> cert(d2i_X509_fp(file.get(), nullptr));
  EXPECT_TRUE(cert);
}

TEST_F(ReqTest, OutformPEMX509) {
  args_list_t args = {"-new",          "-x509",    "-newkey", "rsa:2048",
                      "-nodes",        "-outform", "PEM",     "-keyout",
                      output_key_path, "-out",     cert_path, "-subj",
                      "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));

  std::string cert_content = ReadFileToString(cert_path);
  EXPECT_TRUE(cert_content.find("-----BEGIN CERTIFICATE-----") !=
              std::string::npos);
  EXPECT_TRUE(cert_content.find("-----END CERTIFICATE-----") !=
              std::string::npos);
}
TEST_F(ReqTest, PassinWithKey) {
  // Use pre-created encrypted key with -passin
  args_list_t args = {"-new",        "-key",    protected_key_path,
                      "-nodes",      "-passin", "pass:testpassword",
                      "-out",        csr_path,  "-subj",
                      "/CN=test.com"};
  ASSERT_TRUE(reqTool(args));
}

TEST_F(ReqTest, PassinX509) {
  // Use pre-created encrypted key for X.509 cert with -passin
  args_list_t args = {"-new",
                      "-x509",
                      "-key",
                      protected_key_path,
                      "-nodes",
                      "-passin",
                      "pass:testpassword",
                      "-out",
                      cert_path,
                      "-subj",
                      "/CN=test.com"};
  ASSERT_TRUE(reqTool(args));

  auto cert = LoadPEMCertificate(cert_path);
  ASSERT_TRUE(cert);
}

TEST_F(ReqTest, StdoutOutput) {
  args_list_t args = {"-new", "-nodes", "-subj", "/CN=test.com"};

  ASSERT_TRUE(reqTool(args));
}

// -------------------- Req Option Usage Error Tests --------------------------

class ReqOptionUsageErrorsTest : public ReqTest {
 protected:
  void TestOptionUsageErrors(const std::vector<std::string> &args) {
    args_list_t c_args;
    for (const auto &arg : args) {
      c_args.push_back(arg.c_str());
    }
    bool result = reqTool(c_args);
    ASSERT_FALSE(result);
  }
};

// Test invalid argument values
TEST_F(ReqOptionUsageErrorsTest, InvalidArgTests) {
  std::vector<std::vector<std::string>> testparams = {
      {"-new", "-newkey", "rsa:256", "-nodes", "-out", csr_path, "-subj",
       "/CN=test.com"},  // Key too small
      {"-new", "-newkey", "rsa:32768", "-nodes", "-out", csr_path, "-subj",
       "/CN=test.com"},  // Key too large
      {"-new", "-newkey", "rsa:2048", "-nodes", "-outform", "INVALID", "-out",
       csr_path, "-subj", "/CN=test.com"},  // Invalid outform
      {"-new", "-newkey", "ec:prime256v1", "-nodes", "-out", csr_path, "-subj",
       "/CN=test.com"},  // Unsupported EC key
      {"-new", "-newkey", "dsa:1024", "-nodes", "-out", csr_path, "-subj",
       "/CN=test.com"},  // Unsupported DSA key
  };

  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// Test -passin with wrong passwords
TEST_F(ReqOptionUsageErrorsTest, InvalidPassinTest) {
  std::vector<std::vector<std::string>> testparams = {
      {"-new", "-key", protected_key_path, "-passin", "pass:wrongpass", "-out",
       csr_path, "-subj", "/CN=test.com"},
  };

  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
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
    ASSERT_GT(createTempFILEpath(config_path), 0u);

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
      RemoveFile(config_path);
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
  char config_path[PATH_MAX];
  char sign_key_path[PATH_MAX];
  char protected_sign_key_path[PATH_MAX];
  const char *tool_executable_path;
  const char *openssl_executable_path;
};

TEST_F(ReqComparisonTest, GenerateBasicCSR) {
  std::string subject =
      "/C=US/ST=Washington/L=Seattle/O=Example Inc/CN=example.com";

  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-newkey rsa:2048 -nodes -out " + csr_path_awslc +
                              " -subj \"" + subject + "\"";

  std::string openssl_command = std::string(openssl_executable_path) +
                                " req -new " + "-newkey rsa:2048 -nodes " +
                                " -keyout " + key_path_openssl + " -out " +
                                csr_path_openssl + " -subj \"" + subject + "\"";

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
      "-newkey rsa:2048 -nodes -days 365 -keyout " + key_path_openssl +
      " -out " + cert_path_openssl + " -subj \"" + subject + "\"";

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

// Test no-prompt mode from config
TEST_F(ReqComparisonTest, NoPromptConfig) {
  ScopedFILE config_file(fopen(config_path, "w"));
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

  std::string awslc_command = std::string(tool_executable_path) +
                              " req -new -config " + config_path +
                              " -newkey rsa:2048 -nodes -keyout " +
                              key_path_awslc + " -out " + csr_path_awslc;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " req -new -config " + config_path +
                                " -newkey rsa:2048 -nodes -keyout " +
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

  std::string awslc_command = "printf '" + input + "' | " +
                              std::string(tool_executable_path) + " req -new " +
                              "-newkey rsa:2048 -nodes -keyout " +
                              key_path_awslc + " -out " + csr_path_awslc;

  std::string openssl_command =
      "printf '" + input + "' | " + std::string(openssl_executable_path) +
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

// Test config private key length parsing
TEST_F(ReqComparisonTest, PrivateKeyLengthFromConfig) {
  // Create config with custom key length
  ScopedFILE config_file(fopen(config_path, "w"));
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
                              "-config " + config_path + " -nodes -keyout " +
                              key_path_awslc + " -out " + csr_path_awslc +
                              " -subj \"" + subject + "\"";
  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new " + "-config " +
      config_path + " -nodes -keyout " + key_path_openssl + " -out " +
      csr_path_openssl + " -subj \"" + subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);
  ASSERT_TRUE(csr_awslc != nullptr);
  ASSERT_TRUE(csr_openssl != nullptr);
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));

  bssl::UniquePtr<EVP_PKEY> awslc_key(
      DecryptPrivateKey(key_path_awslc, "testpassword"));
  bssl::UniquePtr<EVP_PKEY> openssl_key(
      DecryptPrivateKey(key_path_openssl, "testpassword"));

  ASSERT_TRUE(awslc_key) << "Failed to load AWS-LC private key";
  ASSERT_TRUE(openssl_key) << "Failed to load OpenSSL private key";

  ASSERT_TRUE(
      CompareRandomGeneratedKeys(awslc_key.get(), openssl_key.get(), 4096u))
      << "AWS-LC and OpenSSL private keys are different";
}

// Test key length validation
TEST_F(ReqComparisonTest, KeyLengthValidation) {
  std::string subject = "/CN=test.example.com";

  // Test minimum key length constraint
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

  // Note: we do not perform a comparison test for maximum length constraint
  // because some versions of OpenSSL do not have a maximum length constraint.
  // The constraint is covered in our unit test instead.
}

// Test with config fallback
TEST_F(ReqComparisonTest, SubjectConfigFallback) {
  // Create config with subject fields using both long and short names
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[ req ]\n"
          "distinguished_name = req_distinguished_name\n"
          "prompt = no\n"
          "\n"
          "[ req_distinguished_name ]\n"
          "countryName = US\n"
          "ST = California\n"
          "organizationName = Test Org\n"
          "CN = config.example.com\n");
  fclose(config_file.release());

  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-config " + config_path +
                              " -newkey rsa:2048 -nodes -keyout " +
                              key_path_awslc + " -out " + csr_path_awslc;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " req -new " + "-config " + config_path +
                                " -newkey rsa:2048 -nodes -keyout " +
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
                              "-key " + sign_key_path + " -nodes -out " +
                              csr_path_awslc + " -subj \"" + subject + "\"";
  std::string openssl_command = std::string(openssl_executable_path) +
                                " req -new " + "-key " + sign_key_path +
                                " -nodes -out " + csr_path_openssl +
                                " -subj \"" + subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);

  ASSERT_TRUE(csr_awslc != nullptr) << "Failed to load AWS-LC CSR";
  ASSERT_TRUE(csr_openssl != nullptr) << "Failed to load OpenSSL CSR";
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));
}

// Test -outform DER option
TEST_F(ReqComparisonTest, OutformDER) {
  std::string subject = "/CN=der-test.example.com";

  // Test CSR generation
  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-newkey rsa:2048 -nodes" + " -out " +
                              csr_path_awslc + " -outform DER" + " -subj \"" +
                              subject + "\"";
  std::string openssl_command = std::string(openssl_executable_path) +
                                " req -new " + "-newkey rsa:2048 -nodes" +
                                " -out " + csr_path_openssl + " -outform DER" +
                                " -subj \"" + subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadDERCSR(csr_path_awslc);
  auto csr_openssl = LoadDERCSR(csr_path_openssl);

  ASSERT_TRUE(csr_awslc != nullptr) << "Failed to load AWS-LC CSR";
  ASSERT_TRUE(csr_openssl != nullptr) << "Failed to load OpenSSL CSR";
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));

  // Test certificate generation
  awslc_command = std::string(tool_executable_path) + " req -x509 -new " +
                  "-newkey rsa:2048 -nodes -days 365 " + " -out " +
                  cert_path_awslc + " -outform DER -subj \"" + subject + "\"";

  openssl_command = std::string(openssl_executable_path) + " req -x509 -new " +
                    "-newkey rsa:2048 -nodes -days 365 " + " -out " +
                    cert_path_openssl + " -outform DER -subj \"" + subject +
                    "\"";

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

// Test -newkey and -key conflict
TEST_F(ReqComparisonTest, KeyConflict) {
  // Generate keys first
  std::string subject = "/CN=conflict-test.example.com";
  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-newkey rsa:4096 -key " + sign_key_path +
                              " -nodes " + " -keyout " + key_path_openssl +
                              " -out " + csr_path_awslc + " -subj \"" +
                              subject + "\"";
  std::string openssl_command = std::string(openssl_executable_path) +
                                " req -new " + "-newkey rsa:4096 -key " +
                                sign_key_path + " -nodes " + " -keyout " +
                                key_path_openssl + " -out " + csr_path_openssl +
                                " -subj \"" + subject + "\"";

  // Both tools should still pass since the conflict only results in a warning
  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);

  ASSERT_TRUE(csr_awslc != nullptr) << "Failed to load AWS-LC CSR";
  ASSERT_TRUE(csr_openssl != nullptr) << "Failed to load OpenSSL CSR";
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));

  bssl::UniquePtr<EVP_PKEY> awslc_key(
      DecryptPrivateKey(key_path_awslc, nullptr));
  bssl::UniquePtr<EVP_PKEY> openssl_key(
      DecryptPrivateKey(key_path_openssl, nullptr));

  // Since no new key were generated, the out keys should match
  ASSERT_TRUE(CompareKeyEquality(awslc_key.get(), openssl_key.get()) == 0);
}

// Test digest algorithm selection
TEST_F(ReqComparisonTest, DigestSelection) {
  std::string subject = "/CN=sha384-test.example.com";
  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-sha384 -newkey rsa:2048 -nodes" + " -out " +
                              csr_path_awslc + " -subj \"" + subject + "\"";
  std::string openssl_command = std::string(openssl_executable_path) +
                                " req -new " +
                                "-sha384 -newkey rsa:2048 -nodes" + " -out " +
                                csr_path_openssl + " -subj \"" + subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);

  ASSERT_TRUE(csr_awslc != nullptr) << "Failed to load AWS-LC CSR";
  ASSERT_TRUE(csr_openssl != nullptr) << "Failed to load OpenSSL CSR";
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));
}

// Test config file digest selection
TEST_F(ReqComparisonTest, DigestSelectionFromConfig) {
  // Create config with custom digest
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[ req ]\n"
          "default_md = sha384\n"
          "distinguished_name = req_distinguished_name\n"
          "prompt = no\n"
          "\n"
          "[ req_distinguished_name ]\n"
          "CN = encrypted-key.example.com\n");
  fclose(config_file.release());

  std::string awslc_command = std::string(tool_executable_path) + " req -new " +
                              "-config " + config_path +
                              " -newkey rsa:2048 -nodes -keyout " +
                              key_path_awslc + " -out " + csr_path_awslc;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " req -new " + "-config " + config_path +
                                " -newkey rsa:2048 -nodes -keyout " +
                                key_path_openssl + " -out " + csr_path_openssl;

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
                              "-key " + sign_key_path + " -nodes -out " +
                              csr_path_awslc + " -subj \"" + subject + "\"";
  std::string openssl_command = std::string(openssl_executable_path) +
                                " req -new " + "-key " + sign_key_path +
                                " -nodes -out " + csr_path_openssl +
                                " -subj \"" + subject + "\"";

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
                              " -passin pass:testpassword -nodes -out " +
                              csr_path_awslc + " -subj \"" + subject + "\"";
  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new " + "-key " +
      protected_sign_key_path + " -passin pass:testpassword -nodes -out " +
      csr_path_openssl + " -subj \"" + subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);

  ASSERT_TRUE(csr_awslc != nullptr);
  ASSERT_TRUE(csr_openssl != nullptr);
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));
}

// Test encrypted private key generation
TEST_F(ReqComparisonTest, GenerateProtectedPrivateKey) {
  std::string subject = "/CN=encrypted-key.example.com";

  // Create a simple config that disables encryption to avoid password prompts
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[ req ]\n"
          "distinguished_name = req_distinguished_name\n"
          "prompt = no\n"
          "encrypt_key = yes\n"
          "\n"
          "[ req_distinguished_name ]\n"
          "CN = encrypted-key.example.com\n");
  fclose(config_file.release());

  // Test with existing key (using the pre-generated sign_key_path) and config
  std::string awslc_command =
      std::string(tool_executable_path) + " req -new -newkey rsa:2048 " +
      "-config " + config_path + " -passout pass:testpassword -keyout " +
      key_path_awslc + " -out " + csr_path_awslc + " -subj \"" + subject + "\"";

  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new -newkey rsa:2048 " +
      "-config " + config_path + " -passout pass:testpassword -keyout " +
      key_path_openssl + " -out " + csr_path_openssl + " -subj \"" + subject +
      "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  // Verify both keys are unencrypted
  std::string awslc_key_content = ReadFileToString(key_path_awslc);
  std::string openssl_key_content = ReadFileToString(key_path_openssl);

  EXPECT_TRUE(awslc_key_content.find("-----BEGIN ENCRYPTED PRIVATE KEY-----") !=
              std::string::npos)
      << "AWS-LC private key should be encrypted PKCS#8";
  EXPECT_TRUE(openssl_key_content.find(
                  "-----BEGIN ENCRYPTED PRIVATE KEY-----") != std::string::npos)
      << "OpenSSL private key should be encrypted PKCS#8";

  bssl::UniquePtr<EVP_PKEY> awslc_key(
      DecryptPrivateKey(key_path_awslc, "testpassword"));
  bssl::UniquePtr<EVP_PKEY> openssl_key(
      DecryptPrivateKey(key_path_openssl, "testpassword"));

  ASSERT_TRUE(awslc_key) << "Failed to load AWS-LC private key";
  ASSERT_TRUE(openssl_key) << "Failed to load OpenSSL private key";

  ASSERT_TRUE(
      CompareRandomGeneratedKeys(awslc_key.get(), openssl_key.get(), 2048u))
      << "AWS-LC and OpenSSL private keys are different";
}

// Test -extensions option without -x509
TEST_F(ReqComparisonTest, ReqExtensions) {
  // Create config file with extension section
  ScopedFILE config_file(fopen(config_path, "w"));
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
      config_path + " -extensions test_ext " +
      "-newkey rsa:2048 -nodes -keyout " + key_path_awslc + " -out " +
      csr_path_awslc + " -subj \"" + subject + "\"";

  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new " + "-config " +
      config_path + " -extensions test_ext " +
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

// Test -extensions option with -x509
TEST_F(ReqComparisonTest, X509Extensions) {
  // Create config file with custom extension section
  ScopedFILE config_file(fopen(config_path, "w"));
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
      config_path + " -extensions custom_ext " +
      "-newkey rsa:2048 -nodes -days 365 -keyout " + key_path_awslc + " -out " +
      cert_path_awslc + " -subj \"" + subject + "\"";

  std::string openssl_command =
      std::string(openssl_executable_path) + " req -x509 -new " + "-config " +
      config_path + " -extensions custom_ext " +
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

// Test req extensions obtained from config
TEST_F(ReqComparisonTest, ReqExtensionsFromConfig) {
  ScopedFILE config_file(fopen(config_path, "w"));
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
      config_path + " -newkey rsa:2048 -nodes -keyout " + key_path_awslc +
      " -out " + csr_path_awslc + " -subj \"" + subject + "\"";

  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new " + "-config " +
      config_path + " -newkey rsa:2048 -nodes -keyout " + key_path_openssl +
      " -out " + csr_path_openssl + " -subj \"" + subject + "\"";

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
  ScopedFILE config_file(fopen(config_path, "w"));
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
  std::string awslc_command = std::string(tool_executable_path) +
                              " req -x509 -new " + "-config " + config_path +
                              " -newkey rsa:2048 -nodes -days 365 -keyout " +
                              key_path_awslc + " -out " + cert_path_awslc +
                              " -subj \"" + subject + "\"";

  std::string openssl_command =
      std::string(openssl_executable_path) + " req -x509 -new " + "-config " +
      config_path + " -newkey rsa:2048 -nodes -days 365 -keyout " +
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

// Test req extensions when config is provided but has no extension section
TEST_F(ReqComparisonTest, ReqExtentionsFromEmptyConfig) {
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[ req ]\n"
          "distinguished_name = req_distinguished_name\n"
          "prompt = no\n"
          "\n"
          "[ req_distinguished_name ]\n"
          "CN = req-ext-test.example.com\n"
          "\n");
  fclose(config_file.release());

  std::string subject = "/CN=req-ext-test.example.com";
  std::string awslc_command =
      std::string(tool_executable_path) + " req -new " + "-config " +
      config_path + " -newkey rsa:2048 -nodes -keyout " + key_path_awslc +
      " -out " + csr_path_awslc + " -subj \"" + subject + "\"";

  std::string openssl_command =
      std::string(openssl_executable_path) + " req -new " + "-config " +
      config_path + " -newkey rsa:2048 -nodes -keyout " + key_path_openssl +
      " -out " + csr_path_openssl + " -subj \"" + subject + "\"";

  ASSERT_EQ(ExecuteCommand(awslc_command), 0);
  ASSERT_EQ(ExecuteCommand(openssl_command), 0);

  auto csr_awslc = LoadPEMCSR(csr_path_awslc);
  auto csr_openssl = LoadPEMCSR(csr_path_openssl);
  ASSERT_TRUE(csr_awslc != nullptr);
  ASSERT_TRUE(csr_openssl != nullptr);
  ASSERT_TRUE(CompareCSRs(csr_awslc.get(), csr_openssl.get()));
}

// Test x509 extensions when config is provided but has no extension section
TEST_F(ReqComparisonTest, X509ExtensionsFromEmptyConfig) {
  ScopedFILE config_file(fopen(config_path, "w"));
  ASSERT_TRUE(config_file);
  fprintf(config_file.get(),
          "[ req ]\n"
          "distinguished_name = req_distinguished_name\n"
          "prompt = no\n"
          "\n"
          "[ req_distinguished_name ]\n"
          "CN = x509-ext-test.example.com\n"
          "\n");
  fclose(config_file.release());

  std::string subject = "/CN=x509-ext-test.example.com";
  std::string awslc_command = std::string(tool_executable_path) +
                              " req -x509 -new " + "-config " + config_path +
                              " -newkey rsa:2048 -nodes -days 365 -keyout " +
                              key_path_awslc + " -out " + cert_path_awslc +
                              " -subj \"" + subject + "\"";

  std::string openssl_command =
      std::string(openssl_executable_path) + " req -x509 -new " + "-config " +
      config_path + " -newkey rsa:2048 -nodes -days 365 -keyout " +
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
