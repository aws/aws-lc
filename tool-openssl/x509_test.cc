// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "openssl/x509.h"
#include <gtest/gtest.h>
#include <openssl/pem.h>
#include <cctype>
#include "../crypto/test/test_util.h"
#include "../crypto/x509/internal.h"
#include "internal.h"
#include "test_util.h"

class X509Test : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(csr_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);
    ASSERT_GT(createTempFILEpath(signkey_path), 0u);
    ASSERT_GT(createTempFILEpath(der_cert_path), 0u);
    ASSERT_GT(createTempFILEpath(ca_cert_path), 0u);
    ASSERT_GT(createTempFILEpath(ca_key_path), 0u);
    ASSERT_GT(createTempFILEpath(protected_signkey_path), 0u);
    ASSERT_GT(createTempFILEpath(protected_ca_cert_path), 0u);
    ASSERT_GT(createTempFILEpath(protected_ca_key_path), 0u);

    bssl::UniquePtr<X509> x509;
    CreateAndSignX509Certificate(x509, nullptr);
    ASSERT_TRUE(x509);

    bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
    ASSERT_TRUE(pkey);
    bssl::UniquePtr<RSA> rsa(RSA_new());
    ASSERT_TRUE(rsa);
    bssl::UniquePtr<BIGNUM> bn(BN_new());
    ASSERT_TRUE(bn && rsa && BN_set_word(bn.get(), RSA_F4) &&
                RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr));
    ASSERT_TRUE(EVP_PKEY_assign_RSA(pkey.get(), rsa.release()));

    ScopedFILE signkey_file(fopen(signkey_path, "wb"));
    ASSERT_TRUE(signkey_file);
    ASSERT_TRUE(PEM_write_PrivateKey(signkey_file.get(), pkey.get(), nullptr,
                                     nullptr, 0, nullptr, nullptr));

    ScopedFILE protected_signkey_file(fopen(protected_signkey_path, "wb"));
    ASSERT_TRUE(protected_signkey_file);
    ASSERT_TRUE(PEM_write_PrivateKey(
        protected_signkey_file.get(), pkey.get(), EVP_aes_256_cbc(),
        (unsigned char *)"testpassword", 12, nullptr, nullptr));

    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));

    // Write DER certificate
    ScopedFILE der_file(fopen(der_cert_path, "wb"));
    ASSERT_TRUE(der_file);
    ASSERT_TRUE(i2d_X509_fp(der_file.get(), x509.get()));

    bssl::UniquePtr<X509_REQ> csr(X509_REQ_new());
    ASSERT_TRUE(csr);
    X509_REQ_set_pubkey(csr.get(), pkey.get());
    X509_REQ_sign(csr.get(), pkey.get(), EVP_sha256());

    ScopedFILE csr_file(fopen(csr_path, "wb"));
    ASSERT_TRUE(csr_file);
    ASSERT_TRUE(PEM_write_X509_REQ(csr_file.get(), csr.get()));

    // Set up mini-CA
    bssl::UniquePtr<X509> ca;
    bssl::UniquePtr<EVP_PKEY> ca_pkey;
    CreateAndSignX509Certificate(ca, &ca_pkey);
    ASSERT_TRUE(ca);
    ASSERT_TRUE(ca_pkey);

    ScopedFILE ca_cert_file(fopen(ca_cert_path, "wb"));
    ASSERT_TRUE(ca_cert_file);
    ASSERT_TRUE(PEM_write_X509(ca_cert_file.get(), ca.get()));
    ASSERT_TRUE(PEM_write_PrivateKey(ca_cert_file.get(), ca_pkey.get(), nullptr,
                                     nullptr, 0, nullptr, nullptr));

    ScopedFILE protected_ca_cert_file(fopen(protected_ca_cert_path, "wb"));
    ASSERT_TRUE(protected_ca_cert_file);
    ASSERT_TRUE(PEM_write_X509(protected_ca_cert_file.get(), ca.get()));
    ASSERT_TRUE(PEM_write_PrivateKey(
        protected_ca_cert_file.get(), ca_pkey.get(), EVP_aes_256_cbc(),
        (unsigned char *)"testpassword", 12, nullptr, nullptr));


    ScopedFILE ca_key_file(fopen(ca_key_path, "wb"));
    ASSERT_TRUE(ca_key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(ca_key_file.get(), ca_pkey.get(), nullptr,
                                     nullptr, 0, nullptr, nullptr));

    ScopedFILE protected_ca_key_file(fopen(protected_ca_key_path, "wb"));
    ASSERT_TRUE(protected_ca_key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(
        protected_ca_key_file.get(), ca_pkey.get(), EVP_aes_256_cbc(),
        (unsigned char *)"testpassword", 12, nullptr, nullptr));
  }
  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(csr_path);
    RemoveFile(out_path);
    RemoveFile(signkey_path);
    RemoveFile(der_cert_path);
    RemoveFile(ca_cert_path);
    RemoveFile(ca_key_path);
    RemoveFile(protected_signkey_path);
    RemoveFile(protected_ca_cert_path);
    RemoveFile(protected_ca_key_path);
  }

  char in_path[PATH_MAX];
  char csr_path[PATH_MAX];
  char out_path[PATH_MAX];
  char signkey_path[PATH_MAX];
  char der_cert_path[PATH_MAX];
  char ca_cert_path[PATH_MAX];
  char ca_key_path[PATH_MAX];
  char protected_signkey_path[PATH_MAX];
  char protected_ca_cert_path[PATH_MAX];
  char protected_ca_key_path[PATH_MAX];
};

// ----------------------------- X509 Option Tests -----------------------------

// Test -in and -out
TEST_F(X509Test, X509ToolInOutTest) {
  args_list_t args = {"-in", in_path, "-out", out_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
  {
    ScopedFILE out_file(fopen(out_path, "rb"));
    ASSERT_TRUE(out_file);
    bssl::UniquePtr<X509> parsed_x509(
        PEM_read_X509(out_file.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(parsed_x509);
  }
}

// Test -modulus
TEST_F(X509Test, X509ToolModulusTest) {
  args_list_t args = {"-in", in_path, "-modulus"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -subject
TEST_F(X509Test, X509ToolSubjectTest) {
  args_list_t args = {"-in", in_path, "-subject"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -subject_hash and -subject_hash_old
TEST_F(X509Test, X509ToolSubjectHashTest) {
  args_list_t args = {"-in", in_path, "-subject_hash"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  args = {"-in", in_path, "-subject_hash_old"};
  result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -fingerprint
TEST_F(X509Test, X509ToolFingerprintTest) {
  args_list_t args = {"-in", in_path, "-fingerprint"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test signkey
TEST_F(X509Test, X509ToolSignkeyTest) {
  args_list_t args = {"-in", in_path, "-signkey", signkey_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -days
TEST_F(X509Test, X509ToolDaysTest) {
  args_list_t args = {"-in",      in_path,      "-out",  out_path,
                      "-signkey", signkey_path, "-days", "365"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -dates
TEST_F(X509Test, X509ToolDatesTest) {
  args_list_t args = {"-in", in_path, "-dates"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -enddate
TEST_F(X509Test, X509ToolEnddateTest) {
  args_list_t args = {"-in", in_path, "-enddate"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -inform
TEST_F(X509Test, X509ToolInformTest) {
  args_list_t args = {"-in", der_cert_path, "-inform", "DER"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  args = {"-in", in_path, "-inform", "PEM"};
  result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -outform
TEST_F(X509Test, X509ToolOutformTest) {
  args_list_t args = {"-in", in_path, "-out", out_path, "-outform", "DER"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  ScopedFILE out_file(fopen(out_path, "rb"));
  ASSERT_TRUE(out_file);
  bssl::UniquePtr<X509> parsed_x509(d2i_X509_fp(out_file.get(), nullptr));
  ASSERT_TRUE(parsed_x509);

  args = {"-in", in_path, "-out", out_path, "-outform", "PEM"};
  result = X509Tool(args);
  ASSERT_TRUE(result);

  out_file.reset(fopen(out_path, "rb"));
  ASSERT_TRUE(out_file);
  parsed_x509.reset(PEM_read_X509(out_file.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(result);
}

// Test -checkend
TEST_F(X509Test, X509ToolCheckendTest) {
  args_list_t args = {"-in", in_path, "-checkend", "3600"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -req
TEST_F(X509Test, X509ToolReqTest) {
  args_list_t args = {"-in",        csr_path, "-req",  "-signkey",
                      signkey_path, "-out",   out_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -pubkey
TEST_F(X509Test, X509ToolPubkeyTest) {
  args_list_t args = {"-in", in_path, "-pubkey"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -CA and -CAkey
TEST_F(X509Test, X509ToolCATest) {
  args_list_t args = {"-in",        in_path,  "-CA",
                      ca_cert_path, "-CAkey", ca_key_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  args = {"-in", in_path, "-CA", ca_cert_path};  // use key in CA file
  result = X509Tool(args);
  ASSERT_TRUE(result);

  args = {"-in", csr_path, "-req", "-CA", ca_cert_path, "-CAkey", ca_key_path};
  result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -extfile and -extensions
TEST_F(X509Test, X509ToolExtensionTest) {
  char ext_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(ext_path), 0u);

  ScopedFILE ext_file(fopen(ext_path, "w"));
  ASSERT_TRUE(ext_file);
  fprintf(ext_file.get(), "[test_ext]\nbasicConstraints=CA:FALSE\n");
  fclose(ext_file.release());

  args_list_t args = {"-in",      csr_path,      "-req",
                      "-signkey", signkey_path,  "-extfile",
                      ext_path,   "-extensions", "test_ext"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  // Test extfile without -extensions (default section)
  ext_file.reset(fopen(ext_path, "w"));
  ASSERT_TRUE(ext_file);
  fprintf(
      ext_file.get(),
      "basicConstraints=CA:FALSE\nkeyUsage=digitalSignature,keyEncipherment\n");
  fclose(ext_file.release());

  args = {"-in",        csr_path,   "-req",  "-signkey",
          signkey_path, "-extfile", ext_path};
  result = X509Tool(args);
  ASSERT_TRUE(result);

  // Test extfile with extensions variable pointing to section
  ext_file.reset(fopen(ext_path, "w"));
  ASSERT_TRUE(ext_file);
  fprintf(ext_file.get(),
          "extensions=v3_req\n\n[v3_req]\nbasicConstraints=CA:FALSE\nkeyUsage="
          "digitalSignature,keyEncipherment\n");
  fclose(ext_file.release());

  args = {"-in", in_path, "-signkey", signkey_path, "-extfile", ext_path};
  result = X509Tool(args);
  ASSERT_TRUE(result);

  RemoveFile(ext_path);
}

// Test -passin with -signkey
TEST_F(X509Test, X509ToolPassinSignkeyTest) {
  args_list_t args = {"-in",      in_path,
                      "-signkey", protected_signkey_path,
                      "-passin",  "pass:testpassword"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -passin with -CA (key in CA file)
TEST_F(X509Test, X509ToolPassinCATest) {
  args_list_t args = {"-in",     in_path,
                      "-CA",     protected_ca_cert_path,
                      "-passin", "pass:testpassword"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -passin with -CA and -CAkey
TEST_F(X509Test, X509ToolPassinCAkeyTest) {
  args_list_t args = {"-in",     in_path,
                      "-CA",     ca_cert_path,
                      "-CAkey",  protected_ca_key_path,
                      "-passin", "pass:testpassword"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -passin with -req and -signkey
TEST_F(X509Test, X509ToolPassinReqSignkeyTest) {
  args_list_t args = {
      "-in",     csr_path,           "-req", "-signkey", protected_signkey_path,
      "-passin", "pass:testpassword"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test SetSerial functionality with CA certificate
TEST_F(X509Test, X509ToolSetSerialTest) {
  // Test 1: First certificate with CA - should create .srl file
  args_list_t args = {"-in",    in_path,     "-CA",  ca_cert_path,
                      "-CAkey", ca_key_path, "-out", out_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  // Check that .srl file was created
  std::string srl_path =
      std::string(ca_cert_path)
          .substr(0, std::string(ca_cert_path).find_last_of('.')) +
      ".srl";
  ScopedFILE srl_file(fopen(srl_path.c_str(), "r"));
  ASSERT_TRUE(srl_file);

  // Read first serial number
  std::string serial1 = ReadFileToString(srl_path.c_str());
  ASSERT_FALSE(serial1.empty());
  serial1 = serial1.substr(0, serial1.find_first_of("\r\n"));  // Remove newline (handles both \r\n and \n)

  // Verify the first certificate serial matches the .srl file content
  auto cert1 = LoadPEMCertificate(out_path);
  ASSERT_TRUE(cert1 != nullptr);
  ASN1_INTEGER *cert_serial = X509_get_serialNumber(cert1.get());
  ASSERT_TRUE(cert_serial != nullptr);

  bssl::UniquePtr<BIGNUM> bn(ASN1_INTEGER_to_BN(cert_serial, nullptr));
  ASSERT_TRUE(bn != nullptr);
  bssl::UniquePtr<char> hex_str(BN_bn2hex(bn.get()));
  ASSERT_TRUE(hex_str != nullptr);

  ASSERT_EQ(serial1, std::string(hex_str.get()));
  srl_file.reset();

  // Test 2: Second certificate with same CA - should increment serial
  args = {"-in",    in_path,     "-CA",  ca_cert_path,
          "-CAkey", ca_key_path, "-out", out_path};
  result = X509Tool(args);
  ASSERT_TRUE(result);

  // Read updated serial number
  std::string serial2 = ReadFileToString(srl_path.c_str());
  ASSERT_FALSE(serial2.empty());
  serial2 = serial2.substr(0, serial2.find_first_of("\r\n"));  // Remove newline (handles both \r\n and \n)

  // Serial numbers should be different
  ASSERT_NE(serial1, serial2);

  // Verify the certificate serial matches the .srl file content
  auto cert2 = LoadPEMCertificate(out_path);
  ASSERT_TRUE(cert2 != nullptr);
  cert_serial = X509_get_serialNumber(cert2.get());
  ASSERT_TRUE(cert_serial != nullptr);

  // Convert certificate serial to hex string for comparison
  bn.reset(ASN1_INTEGER_to_BN(cert_serial, nullptr));
  ASSERT_TRUE(bn != nullptr);
  hex_str.reset(BN_bn2hex(bn.get()));
  ASSERT_TRUE(hex_str != nullptr);

  ASSERT_EQ(serial2, std::string(hex_str.get()));

  // Clean up
  RemoveFile(srl_path.c_str());
}

// Test SetSerial functionality without CA (random serial generation)
TEST_F(X509Test, X509ToolSetSerialRandomTest) {
  // Test self-signed certificates - should generate random serials
  args_list_t args = {"-in",        in_path, "-signkey",
                      signkey_path, "-out",  out_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);


  auto cert1 = LoadPEMCertificate(out_path);
  ASSERT_TRUE(cert1 != nullptr);

  args = {"-in", in_path, "-signkey", signkey_path, "-out", out_path};
  result = X509Tool(args);
  ASSERT_TRUE(result);

  auto cert2 = LoadPEMCertificate(out_path);
  ASSERT_TRUE(cert2 != nullptr);

  // Verify certificates have different serial numbers
  ASN1_INTEGER *serial1 = X509_get_serialNumber(cert1.get());
  ASN1_INTEGER *serial2 = X509_get_serialNumber(cert2.get());
  ASSERT_TRUE(serial1 != nullptr);
  ASSERT_TRUE(serial2 != nullptr);

  // Serial numbers should be different
  ASSERT_NE(0, ASN1_INTEGER_cmp(serial1, serial2));
}

// Test SetSerial functionality with existing .srl file
TEST_F(X509Test, X509ToolSetSerialExistingFileTest) {
  // Create existing .srl file with known serial number
  std::string srl_path =
      std::string(ca_cert_path)
          .substr(0, std::string(ca_cert_path).find_last_of('.')) +
      ".srl";
  ScopedFILE srl_file(fopen(srl_path.c_str(), "w"));
  ASSERT_TRUE(srl_file);
  fprintf(srl_file.get(), "1234ABCD\n");
  srl_file.reset();

  // Generate certificate with CA - should read from existing .srl file
  args_list_t args = {"-in",    in_path,     "-CA",  ca_cert_path,
                      "-CAkey", ca_key_path, "-out", out_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  // Read updated serial number from .srl file
  std::string new_serial = ReadFileToString(srl_path.c_str());
  ASSERT_FALSE(new_serial.empty());

  // Serial should be incremented from 1234ABCD to 1234ABCE
  // Strip trailing newline characters for comparison (handles both \r\n and \n)
  new_serial = new_serial.substr(0, new_serial.find_first_of("\r\n"));
  ASSERT_EQ("1234ABCE", new_serial);

  // Verify the certificate serial matches the .srl file content
  auto cert = LoadPEMCertificate(out_path);
  ASSERT_TRUE(cert != nullptr);
  ASN1_INTEGER *cert_serial = X509_get_serialNumber(cert.get());
  ASSERT_TRUE(cert_serial != nullptr);

  bssl::UniquePtr<BIGNUM> bn(ASN1_INTEGER_to_BN(cert_serial, nullptr));
  ASSERT_TRUE(bn != nullptr);
  bssl::UniquePtr<char> hex_str(BN_bn2hex(bn.get()));
  ASSERT_TRUE(hex_str != nullptr);

  // new_serial already stripped above, no need to strip again
  ASSERT_EQ(new_serial, std::string(hex_str.get()));

  // Clean up
  RemoveFile(srl_path.c_str());
}

// Test AKID serial number
TEST_F(X509Test, X509ToolAKIDSerialWithCATest) {
  char ext_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(ext_path), 0u);

  // Create extension file with authorityKeyIdentifier
  ScopedFILE ext_file(fopen(ext_path, "w"));
  ASSERT_TRUE(ext_file);
  fprintf(ext_file.get(), "[test_ext]\n");
  fprintf(ext_file.get(), "authorityKeyIdentifier=keyid,issuer:always\n");
  fprintf(ext_file.get(), "basicConstraints=CA:FALSE\n");
  ext_file.reset();

  args_list_t args = {"-in",         in_path,     "-CA",      ca_cert_path,
                      "-CAkey",      ca_key_path, "-extfile", ext_path,
                      "-extensions", "test_ext",  "-out",     out_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  // Verify the certificate serial matches the .srl file content
  auto cert = LoadPEMCertificate(out_path);
  ASSERT_TRUE(cert);
  ASN1_INTEGER *cert_serial = X509_get_serialNumber(cert.get());
  ASSERT_TRUE(cert_serial);

  // Verify cert serial number does not match CA serial number
  auto ca_cert = LoadPEMCertificate(ca_cert_path);
  ASN1_INTEGER *ca_serial = X509_get_serialNumber(ca_cert.get());
  ASSERT_TRUE(ca_serial);
  ASSERT_NE(ASN1_INTEGER_cmp(ca_serial, cert_serial), 0);

  // Verify AKID serial number matches CA serial number
  bssl::UniquePtr<AUTHORITY_KEYID> akid(static_cast<AUTHORITY_KEYID *>(
      X509_get_ext_d2i(cert.get(), NID_authority_key_identifier, NULL, NULL)));
  ASSERT_TRUE(akid);
  ASSERT_TRUE(akid.get()->serial);
  ASSERT_EQ(X509_check_akid(ca_cert.get(), akid.get()), 0);

  RemoveFile(ext_path);
}

// Test AKID serial number
TEST_F(X509Test, X509ToolAKIDSerialSelfSignedTest) {
  char ext_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(ext_path), 0u);

  // Create extension file with authorityKeyIdentifier
  ScopedFILE ext_file(fopen(ext_path, "w"));
  ASSERT_TRUE(ext_file);
  fprintf(ext_file.get(), "[test_ext]\n");
  fprintf(ext_file.get(),
          "authorityKeyIdentifier=keyid:always,issuer:always\n");
  fprintf(ext_file.get(), "basicConstraints=CA:FALSE\n");
  ext_file.reset();

  args_list_t args = {"-in",      in_path,  "-signkey",    signkey_path,
                      "-extfile", ext_path, "-extensions", "test_ext",
                      "-out",     out_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  // Verify the certificate serial matches the .srl file content
  auto cert = LoadPEMCertificate(out_path);
  ASSERT_TRUE(cert);
  ASN1_INTEGER *cert_serial = X509_get_serialNumber(cert.get());
  ASSERT_TRUE(cert_serial);

  // Verify AKID serial number matches CA serial number
  bssl::UniquePtr<AUTHORITY_KEYID> akid(static_cast<AUTHORITY_KEYID *>(
      X509_get_ext_d2i(cert.get(), NID_authority_key_identifier, NULL, NULL)));
  ASSERT_TRUE(akid);
  ASSERT_EQ(X509_check_akid(cert.get(), akid.get()), 0);

  RemoveFile(ext_path);
}

// -------------------- X590 Option Usage Error Tests --------------------------

class X509OptionUsageErrorsTest : public X509Test {
 protected:
  void TestOptionUsageErrors(const std::vector<std::string> &args) {
    args_list_t c_args;
    for (const auto &arg : args) {
      c_args.push_back(arg.c_str());
    }
    bool result = X509Tool(c_args);
    ASSERT_FALSE(result);
  }
};

//  Test mutually exclusive options
TEST_F(X509OptionUsageErrorsTest, MutuallyExclusiveOptionsTests) {
  std::vector<std::vector<std::string>> testparams = {
      {"-in", in_path, "-req", "-signkey", signkey_path, "-dates"},
      {"-in", in_path, "-req", "-signkey", signkey_path, "-checkend", "3600"},
      {"-in", in_path, "-signkey", signkey_path, "-dates"},
      {"-in", in_path, "-signkey", signkey_path, "-checkend", "3600"},
      {"-in", in_path, "-days", "365", "-dates"},
      {"-in", in_path, "-days", "365", "-checkend", "3600"},
      {"-in", in_path, "-signkey", signkey_path, "-CA", ca_cert_path},

  };
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

TEST_F(X509OptionUsageErrorsTest, RequiredOptionTests) {
  std::vector<std::vector<std::string>> testparams = {
      {"-in", in_path, "-req"},                // Test -req without -signkey
      {"-in", in_path, "-CAkey", ca_key_path}  // Test -CAkey without -CA
  };
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// Test argument errors for -days: !<0 || non-integer, -checkend: !<=0 ||
// non-integer, -inform != {DER, PEM}
TEST_F(X509OptionUsageErrorsTest, DaysAndCheckendArgTests) {
  std::vector<std::vector<std::string>> testparams = {
      {"-in", in_path, "-checkend", "abc"},
      {"-in", in_path, "-checkend", "-1"},
      {"-in", in_path, "-signkey", signkey_path, "-days", "abc"},
      {"-in", in_path, "-signkey", signkey_path, "-days", "0"},
      {"-in", in_path, "-signkey", signkey_path, "-days", "-1.7"},
  };
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

TEST_F(X509OptionUsageErrorsTest, InvalidArgTests) {
  std::vector<std::vector<std::string>> testparams = {
      {"-in", in_path, "-inform", "RANDOM"},
      {"-in", in_path, "-out", out_path, "-outform", "RANDOM"}};
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// Test -passin with invalid formats and wrong passwords
TEST_F(X509OptionUsageErrorsTest, InvalidPassinTest) {
  std::vector<std::vector<std::string>> testparams = {
      {"-in", in_path, "-signkey", protected_signkey_path, "-passin",
       "pass:wrongpassword"},
      {"-in", in_path, "-CA", protected_ca_cert_path, "-passin",
       "pass:wrongpassword"},
      {"-in", in_path, "-CA", ca_cert_path, "-CAkey", protected_ca_key_path,
       "-passin", "pass:wrongpassword"},
      {"-in", in_path, "-signkey", signkey_path, "-passin", "invalid:format"}};
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// -------------------- X509 OpenSSL Comparison Tests --------------------------

// Comparison tests cannot run without set up of environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.

class X509ComparisonTest : public ::testing::Test {
 protected:
  void SetUp() override {
    // Skip gtests if env variables not set
    tool_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
    if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
      GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH "
                      "environment variables are not set";
    }

    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(csr_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);
    ASSERT_GT(createTempFILEpath(signkey_path), 0u);
    ASSERT_GT(createTempFILEpath(der_cert_path), 0u);
    ASSERT_GT(createTempFILEpath(ca_cert_path), 0u);
    ASSERT_GT(createTempFILEpath(ca_key_path), 0u);
    ASSERT_GT(createTempFILEpath(protected_signkey_path), 0u);

    CreateAndSignX509Certificate(x509, nullptr);
    ASSERT_TRUE(x509);

    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));

    ScopedFILE der_file(fopen(der_cert_path, "wb"));
    ASSERT_TRUE(der_file);
    ASSERT_TRUE(i2d_X509_fp(der_file.get(), x509.get()));

    bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
    bssl::UniquePtr<RSA> rsa(RSA_new());
    bssl::UniquePtr<BIGNUM> bn(BN_new());
    ASSERT_TRUE(bn && BN_set_word(bn.get(), RSA_F4) &&
                RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr));
    ASSERT_TRUE(EVP_PKEY_assign_RSA(pkey.get(), rsa.release()));

    ScopedFILE signkey_file(fopen(signkey_path, "wb"));
    ASSERT_TRUE(signkey_file);
    ASSERT_TRUE(PEM_write_PrivateKey(signkey_file.get(), pkey.get(), nullptr,
                                     nullptr, 0, nullptr, nullptr));

    // Create password-protected private key for testing -passin
    ScopedFILE protected_signkey_file(fopen(protected_signkey_path, "wb"));
    ASSERT_TRUE(protected_signkey_file);
    ASSERT_TRUE(PEM_write_PrivateKey(
        protected_signkey_file.get(), pkey.get(), EVP_aes_256_cbc(),
        (unsigned char *)"testpassword", 12, nullptr, nullptr));

    csr.reset(X509_REQ_new());
    ASSERT_TRUE(csr);
    X509_REQ_set_pubkey(csr.get(), pkey.get());
    X509_REQ_sign(csr.get(), pkey.get(), EVP_sha256());

    ScopedFILE csr_file(fopen(csr_path, "wb"));
    ASSERT_TRUE(csr_file);
    ASSERT_TRUE(PEM_write_X509_REQ(csr_file.get(), csr.get()));

    // Set up mini-CA
    bssl::UniquePtr<X509> ca;
    bssl::UniquePtr<EVP_PKEY> ca_pkey;
    CreateAndSignX509Certificate(ca, &ca_pkey);
    ASSERT_TRUE(ca);
    ASSERT_TRUE(ca_pkey);

    ScopedFILE ca_cert_file(fopen(ca_cert_path, "wb"));
    ASSERT_TRUE(ca_cert_file);
    ASSERT_TRUE(PEM_write_X509(ca_cert_file.get(), ca.get()));
    ASSERT_TRUE(PEM_write_PrivateKey(ca_cert_file.get(), ca_pkey.get(), nullptr,
                                     nullptr, 0, nullptr, nullptr));

    ScopedFILE ca_key_file(fopen(ca_key_path, "wb"));
    ASSERT_TRUE(ca_key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(ca_key_file.get(), ca_pkey.get(), nullptr,
                                     nullptr, 0, nullptr, nullptr));
  }

  void TearDown() override {
    if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
      RemoveFile(in_path);
      RemoveFile(csr_path);
      RemoveFile(out_path_tool);
      RemoveFile(out_path_openssl);
      RemoveFile(signkey_path);
      RemoveFile(der_cert_path);
      RemoveFile(ca_cert_path);
      RemoveFile(ca_key_path);
      RemoveFile(protected_signkey_path);
    }
  }

  char in_path[PATH_MAX];
  char csr_path[PATH_MAX];
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  char signkey_path[PATH_MAX];
  char der_cert_path[PATH_MAX];
  char ca_cert_path[PATH_MAX];
  char ca_key_path[PATH_MAX];
  char protected_signkey_path[PATH_MAX];
  bssl::UniquePtr<X509> x509;
  bssl::UniquePtr<X509_REQ> csr;
  const char *tool_executable_path;
  const char *openssl_executable_path;
  std::string tool_output_str;
  std::string openssl_output_str;
};

// normalize_subject extracts the subject line from |input|. It removes all
// whitespaces from the subject line and replaces it in |input|.
static std::string normalize_subject(std::string input) {
  size_t subject_start = input.find("subject=");
  if (subject_start != std::string::npos) {
    size_t line_end = input.find('\n', subject_start);
    if (line_end != std::string::npos) {
      std::string subject_line =
          input.substr(subject_start, line_end - subject_start);
      subject_line.erase(remove(subject_line.begin(), subject_line.end(), ' '),
                         subject_line.end());
      input.replace(subject_start, line_end - subject_start, subject_line);
    }
  }
  return input;
}

// Test against OpenSSL output "openssl x509 -in file -text -noout"
TEST_F(X509ComparisonTest, X509ToolCompareTextOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -text -noout> " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " x509 -in " + in_path + " -text -noout > " +
                                out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  // OpenSSL 3.0+ include an additional "Signature Value" header before printing
  // the signature
  const char *signature_string = "Signature Value:";
  size_t index = openssl_output_str.find(signature_string);
  if (index != std::string::npos) {
    openssl_output_str.replace(index, strlen(signature_string), "");
  }

  // OpenSSL disagrees on what the Subject Public Key Info headers should be
  const char *rsa_public_key = "RSA Public-Key:";
  index = openssl_output_str.find(rsa_public_key);
  if (index != std::string::npos) {
    openssl_output_str.replace(index, strlen(rsa_public_key), "Public-Key:");
  }

  // OpenSSL versions disagree on the amount of indentation of certain fields
  tool_output_str.erase(
      remove_if(tool_output_str.begin(), tool_output_str.end(), isspace),
      tool_output_str.end());
  openssl_output_str.erase(
      remove_if(openssl_output_str.begin(), openssl_output_str.end(), isspace),
      openssl_output_str.end());

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl x509 -in file -modulus"
TEST_F(X509ComparisonTest, X509ToolCompareModulusOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -modulus > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " x509 -in " + in_path + " -modulus > " +
                                out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);

  tool_command = std::string(tool_executable_path) + " x509 -in " + in_path +
                 " -modulus -out " + out_path_tool;
  openssl_command = std::string(openssl_executable_path) + " x509 -in " +
                    in_path + " -modulus -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl x509 -in file -subject"
TEST_F(X509ComparisonTest, X509ToolCompareSubjectOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -subject > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " x509 -in " + in_path + " -subject > " +
                                out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  // OpenSSL master and versions <= 3.2 have differences in spacing for the
  // subject field
  tool_output_str = normalize_subject(tool_output_str);
  openssl_output_str = normalize_subject(openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);

  tool_command = std::string(tool_executable_path) + " x509 -in " + in_path +
                 " -subject -out " + out_path_tool;
  openssl_command = std::string(openssl_executable_path) + " x509 -in " +
                    in_path + " -subject -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  // OpenSSL master and versions <= 3.2 have differences in spacing for the
  // subject field
  tool_output_str = normalize_subject(tool_output_str);
  openssl_output_str = normalize_subject(openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl x509 -in file -fingerprint -subject_hash
// -subject_hash_old"
TEST_F(X509ComparisonTest, X509ToolCompareFingerprintOpenSSL) {
  std::string tool_command =
      std::string(tool_executable_path) + " x509 -in " + in_path +
      " -subject_hash -subject_hash_old -fingerprint > " + out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " x509 -in " + in_path +
      " -subject_hash -subject_hash_old -fingerprint > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);

  tool_command = std::string(tool_executable_path) + " x509 -in " + in_path +
                 " -subject_hash -subject_hash_old -fingerprint -out " +
                 out_path_tool;
  openssl_command =
      std::string(openssl_executable_path) + " x509 -in " + in_path +
      " -subject_hash -subject_hash_old -fingerprint -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl x509 -in file -fingerprint -subject_hash
// -subject_hash_old"
TEST_F(X509ComparisonTest, X509ToolCompareReorderedFingerprintOpenSSL) {
  std::string tool_command =
      std::string(tool_executable_path) + " x509 -in " + in_path +
      " -subject_hash -fingerprint -subject_hash_old > " + out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " x509 -in " + in_path +
      " -subject_hash -fingerprint -subject_hash_old > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);

  tool_command = std::string(tool_executable_path) + " x509 -in " + in_path +
                 " -fingerprint -subject_hash_old -subject_hash -out " +
                 out_path_tool;
  openssl_command =
      std::string(openssl_executable_path) + " x509 -in " + in_path +
      " -fingerprint -subject_hash_old -subject_hash -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl x509 -in file -fingerprint -subject_hash
// -subject_hash_old"
TEST_F(X509ComparisonTest, X509ToolCompareHashFingerprintOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) +
                             " x509 -subject_hash -fingerprint -noout -in " +
                             in_path + " > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " x509 -subject_hash -fingerprint -noout -in " +
                                in_path + " > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl x509 -in file -pubkey"
TEST_F(X509ComparisonTest, X509ToolComparePubkeyOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -pubkey > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " x509 -in " + in_path + " -pubkey > " +
                                out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl x509 -in file -noout -subject
// -fingerprint"
TEST_F(X509ComparisonTest, X509ToolCompareSubjectFingerprintOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -noout -subject -fingerprint > " +
                             out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " x509 -in " + in_path +
      " -noout -subject -fingerprint > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  // OpenSSL master and versions <= 3.2 have differences in spacing for the
  // subject field
  tool_output_str = normalize_subject(tool_output_str);
  openssl_output_str = normalize_subject(openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);

  tool_command = std::string(tool_executable_path) + " x509 -in " + in_path +
                 " -noout -subject -fingerprint -out " + out_path_tool;
  openssl_command = std::string(openssl_executable_path) + " x509 -in " +
                    in_path + " -noout -subject -fingerprint -out " +
                    out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  // OpenSSL master and versions <= 3.2 have differences in spacing for the
  // subject field
  tool_output_str = normalize_subject(tool_output_str);
  openssl_output_str = normalize_subject(openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl x509 -in file -noout -subject
// -fingerprint"
TEST_F(X509ComparisonTest, X509ToolCompareReorderedSubjectFingerprintOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -noout -fingerprint -subject > " +
                             out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " x509 -in " + in_path +
      " -noout -fingerprint -subject > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  // OpenSSL master and versions <= 3.2 have differences in spacing for the
  // subject field
  tool_output_str = normalize_subject(tool_output_str);
  openssl_output_str = normalize_subject(openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);

  tool_command = std::string(tool_executable_path) + " x509 -in " + in_path +
                 " -noout -fingerprint -subject -out " + out_path_tool;
  openssl_command = std::string(openssl_executable_path) + " x509 -in " +
                    in_path + " -noout -fingerprint -subject -out " +
                    out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  // OpenSSL master and versions <= 3.2 have differences in spacing for the
  // subject field
  tool_output_str = normalize_subject(tool_output_str);
  openssl_output_str = normalize_subject(openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl x509 -in in_file -checkend 0"
TEST_F(X509ComparisonTest, X509ToolCompareCheckendOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -checkend 0 > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " x509 -in " + in_path + " -checkend 0 > " +
                                out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl x509 -req -in csr_file -signkey
// private_key_file -days 80 -out out_file"
TEST_F(X509ComparisonTest, X509ToolCompareReqSignkeyDaysOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) +
                             " x509 -req -in " + csr_path + " -signkey " +
                             signkey_path + " -days 80 -out " + out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " x509 -req -in " + csr_path +
      " -signkey " + signkey_path + " -days 80 -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  // Load certificates
  auto cert_tool = LoadPEMCertificate(out_path_tool);
  auto cert_openssl = LoadPEMCertificate(out_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr)
      << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl != nullptr)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 365 days validity period
  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 80))
      << "Certificates generated by tool and OpenSSL have different attributes";
}

// Test against OpenSSL output "openssl x509 -in file -dates -noout"
TEST_F(X509ComparisonTest, X509ToolCompareDatesNooutOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -dates -noout > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " x509 -in " + in_path + " -dates -noout > " +
                                out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);

  tool_command = std::string(tool_executable_path) + " x509 -in " + in_path +
                 " -dates -noout -out " + out_path_tool;
  openssl_command = std::string(openssl_executable_path) + " x509 -in " +
                    in_path + " -dates -noout -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl x509 -in file -dates -enddate", notAfter
// date should only be printed out once
TEST_F(X509ComparisonTest, X509ToolCompareDatesEnddateOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -dates -enddate > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " x509 -in " + in_path + " -dates -enddate > " +
                                out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);

  tool_command = std::string(tool_executable_path) + " x509 -in " + in_path +
                 " -dates -enddate -out " + out_path_tool;
  openssl_command = std::string(openssl_executable_path) + " x509 -in " +
                    in_path + " -dates -enddate -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl x509 -in file -inform DER -enddate"
TEST_F(X509ComparisonTest, X509ToolCompareInformDEREnddateOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             der_cert_path + " -inform DER -enddate > " +
                             out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " x509 -in " + der_cert_path +
                                " -inform DER -enddate > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);

  tool_command = std::string(tool_executable_path) + " x509 -in " +
                 der_cert_path + " -inform DER -enddate -out " + out_path_tool;
  openssl_command = std::string(openssl_executable_path) + " x509 -in " +
                    der_cert_path + " -inform DER -enddate -out " +
                    out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl x509 -in file -inform DER -enddate"
TEST_F(X509ComparisonTest, X509ToolCompareInformPEMEnddateOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -inform PEM -enddate > " +
                             out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " x509 -in " + in_path +
                                " -inform PEM -enddate > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);

  tool_command = std::string(tool_executable_path) + " x509 -in " + in_path +
                 " -inform PEM -enddate -out " + out_path_tool;
  openssl_command = std::string(openssl_executable_path) + " x509 -in " +
                    in_path + " -inform PEM -enddate -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output reading from stdin "openssl x509 -fingerprint
// -dates"
TEST_F(X509ComparisonTest, X509ToolCompareStdinFingerprintDatesOpenSSL) {
  std::string tool_command = "cat " + std::string(in_path) + " | " +
                             std::string(tool_executable_path) +
                             " x509 -fingerprint -dates > " + out_path_tool;
  std::string openssl_command = "cat " + std::string(in_path) + " | " +
                                std::string(openssl_executable_path) +
                                " x509 -fingerprint -dates > " +
                                out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);

  tool_command = "cat " + std::string(in_path) + " | " +
                 std::string(tool_executable_path) +
                 " x509 -fingerprint -dates -out " + out_path_tool;
  openssl_command = "cat " + std::string(in_path) + " | " +
                    std::string(openssl_executable_path) +
                    " x509 -fingerprint -dates -out " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL output "openssl x509 -in in_file (-req) -signkey
// private_key_file -out out_file -outform PEM"
TEST_F(X509ComparisonTest, X509ToolCompareSignkeyOutformPEMOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -signkey " + signkey_path +
                             " -outform PEM -out " + out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " x509 -in " + in_path +
      " -signkey " + signkey_path + " -outform PEM -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  // Load certificates
  auto cert_tool = LoadPEMCertificate(out_path_tool);
  auto cert_openssl = LoadPEMCertificate(out_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr)
      << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl != nullptr)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 365 days validity period
  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 30))
      << "Certificates generated by tool and OpenSSL have different attributes";


  tool_command = std::string(tool_executable_path) + " x509 -in " + csr_path +
                 " -req -signkey " + signkey_path + " -outform PEM -out " +
                 out_path_tool;
  openssl_command = std::string(openssl_executable_path) + " x509 -in " +
                    csr_path + " -req -signkey " + signkey_path +
                    " -outform PEM -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  // Load certificates
  cert_tool = LoadPEMCertificate(out_path_tool);
  cert_openssl = LoadPEMCertificate(out_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr)
      << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl != nullptr)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 365 days validity period
  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 30))
      << "Certificates generated by tool and OpenSSL have different attributes";
}

// Test against OpenSSL output "openssl x509 -in in_file (-req) -signkey
// private_key_file -out out_file -outform DER"
TEST_F(X509ComparisonTest, X509ToolCompareSignkeyOutformDEROpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -signkey " + signkey_path +
                             " -outform DER -out " + out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " x509 -in " + in_path +
      " -signkey " + signkey_path + " -outform DER -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  // Load certificates
  auto cert_tool = LoadDERCertificate(out_path_tool);
  auto cert_openssl = LoadDERCertificate(out_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr)
      << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl != nullptr)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 30 days validity period
  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 30))
      << "Certificates generated by tool and OpenSSL have different attributes";

  tool_command = std::string(tool_executable_path) + " x509 -in " + csr_path +
                 " -req -signkey " + signkey_path + " -outform DER -out " +
                 out_path_tool;
  openssl_command = std::string(openssl_executable_path) + " x509 -in " +
                    csr_path + " -req -signkey " + signkey_path +
                    " -outform DER -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  // Load certificates
  cert_tool = LoadDERCertificate(out_path_tool);
  cert_openssl = LoadDERCertificate(out_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr)
      << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl != nullptr)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 30 days validity period
  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 30))
      << "Certificates generated by tool and OpenSSL have different attributes";
}


// Test against OpenSSL output "openssl x509 -in in_file -CA certfile -CAkey
// keyfile"
TEST_F(X509ComparisonTest, X509ToolCompareCAOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -CA " + ca_cert_path + " -out " +
                             out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " x509 -in " + in_path + " -CA " +
                                ca_cert_path + " -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  // Load certificates
  auto cert_tool = LoadPEMCertificate(out_path_tool);
  auto cert_openssl = LoadPEMCertificate(out_path_openssl);
  auto ca_cert = LoadPEMCertificate(ca_cert_path);

  ASSERT_TRUE(cert_tool != nullptr)
      << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl != nullptr)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 365 days validity period
  ASSERT_TRUE(CompareCertificates(cert_tool.get(), cert_openssl.get(),
                                  ca_cert.get(), 30))
      << "Certificates generated by tool and OpenSSL have different attributes";


  tool_command = std::string(tool_executable_path) + " x509 -in " + in_path +
                 " -CA " + ca_cert_path + " -CAkey " + ca_key_path + " -out " +
                 out_path_tool;
  openssl_command = std::string(openssl_executable_path) + " x509 -in " +
                    in_path + " -CA " + ca_cert_path + " -CAkey " +
                    ca_key_path + " -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  // Load certificates
  cert_tool = LoadPEMCertificate(out_path_tool);
  cert_openssl = LoadPEMCertificate(out_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr)
      << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl != nullptr)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 365 days validity period
  ASSERT_TRUE(CompareCertificates(cert_tool.get(), cert_openssl.get(),
                                  ca_cert.get(), 30))
      << "Certificates generated by tool and OpenSSL have different attributes";
}

// Test against OpenSSL output "openssl x509 -in in_file -CA certfile -CAkey
// keyfile"
TEST_F(X509ComparisonTest, X509ToolCompareReqCAOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             csr_path + " -req -CA " + ca_cert_path + " -out " +
                             out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " x509 -in " + csr_path + " -req -CA " +
                                ca_cert_path + " -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  // Load certificates
  auto cert_tool = LoadPEMCertificate(out_path_tool);
  auto cert_openssl = LoadPEMCertificate(out_path_openssl);
  auto ca_cert = LoadPEMCertificate(ca_cert_path);

  ASSERT_TRUE(cert_tool != nullptr)
      << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl != nullptr)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 365 days validity period
  ASSERT_TRUE(CompareCertificates(cert_tool.get(), cert_openssl.get(),
                                  ca_cert.get(), 30))
      << "Certificates generated by tool and OpenSSL have different attributes";


  tool_command = std::string(tool_executable_path) + " x509 -in " + csr_path +
                 " -req -CA " + ca_cert_path + " -CAkey " + ca_key_path +
                 " -out " + out_path_tool;
  openssl_command = std::string(openssl_executable_path) + " x509 -in " +
                    csr_path + " -req -CA " + ca_cert_path + " -CAkey " +
                    ca_key_path + " -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  // Load certificates
  cert_tool = LoadPEMCertificate(out_path_tool);
  cert_openssl = LoadPEMCertificate(out_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr)
      << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl != nullptr)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 365 days validity period
  ASSERT_TRUE(CompareCertificates(cert_tool.get(), cert_openssl.get(),
                                  ca_cert.get(), 30))
      << "Certificates generated by tool and OpenSSL have different attributes";
}

// Test against OpenSSL output with -passin option
TEST_F(X509ComparisonTest, X509ToolComparePassinOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -signkey " + protected_signkey_path +
                             " -passin pass:testpassword -out " + out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " x509 -in " + in_path +
      " -signkey " + protected_signkey_path +
      " -passin pass:testpassword -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  // Load certificates
  auto cert_tool = LoadPEMCertificate(out_path_tool);
  auto cert_openssl = LoadPEMCertificate(out_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr)
      << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl != nullptr)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 30 days validity period
  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 30))
      << "Certificates generated by tool and OpenSSL have different attributes";
}

// Test against OpenSSL output "openssl x509 -extfile extfile -extensions
// extension_header"
TEST_F(X509ComparisonTest, X509ToolCompareExtensionsOpenSSL) {
  char ext_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(ext_path), 0u);

  ScopedFILE ext_file(fopen(ext_path, "w"));
  ASSERT_TRUE(ext_file);
  fprintf(ext_file.get(), "[test_ext]\nbasicConstraints=CA:FALSE\n");
  fclose(ext_file.release());

  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             csr_path + " -req -signkey " + signkey_path +
                             " -extfile " + ext_path +
                             " -extensions test_ext -out " + out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " x509 -in " + csr_path +
      " -req -signkey " + signkey_path + " -extfile " + ext_path +
      " -extensions test_ext -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  auto cert_tool = LoadPEMCertificate(out_path_tool);
  auto cert_openssl = LoadPEMCertificate(out_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr);
  ASSERT_TRUE(cert_openssl != nullptr);

  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 30));

  // Test extfile without -extensions (default section)
  ext_file.reset(fopen(ext_path, "w"));
  ASSERT_TRUE(ext_file);
  fprintf(ext_file.get(), "basicConstraints=CA:FALSE\n");
  fprintf(ext_file.get(), "keyUsage=digitalSignature,keyEncipherment\n");
  fclose(ext_file.release());

  tool_command = std::string(tool_executable_path) + " x509 -in " + csr_path +
                 " -req -signkey " + signkey_path + " -extfile " + ext_path +
                 " -out " + out_path_tool;
  openssl_command = std::string(openssl_executable_path) + " x509 -in " +
                    csr_path + " -req -signkey " + signkey_path + " -extfile " +
                    ext_path + " -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  cert_tool = LoadPEMCertificate(out_path_tool);
  cert_openssl = LoadPEMCertificate(out_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr);
  ASSERT_TRUE(cert_openssl != nullptr);

  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 30));

  // Test extfile with extensions variable pointing to section
  ext_file.reset(fopen(ext_path, "w"));
  ASSERT_TRUE(ext_file);
  fprintf(ext_file.get(), "extensions=v3_req\n\n");
  fprintf(ext_file.get(), "[v3_req]\n");
  fprintf(ext_file.get(), "basicConstraints=CA:FALSE\n");
  fprintf(ext_file.get(), "keyUsage=digitalSignature,keyEncipherment\n");
  fclose(ext_file.release());

  tool_command = std::string(tool_executable_path) + " x509 -in " + in_path +
                 " -signkey " + signkey_path + " -extfile " + ext_path +
                 " -out " + out_path_tool;
  openssl_command = std::string(openssl_executable_path) + " x509 -in " +
                    in_path + " -signkey " + signkey_path + " -extfile " +
                    ext_path + " -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  cert_tool = LoadPEMCertificate(out_path_tool);
  cert_openssl = LoadPEMCertificate(out_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr);
  ASSERT_TRUE(cert_openssl != nullptr);

  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 30));

  RemoveFile(ext_path);
}

// Test SetSerial functionality against OpenSSL with CA certificate
TEST_F(X509ComparisonTest, X509ToolCompareSetSerialCAOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -CA " + ca_cert_path + " -CAkey " +
                             ca_key_path + " -out " + out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " x509 -in " + in_path + " -CA " +
      ca_cert_path + " -CAkey " + ca_key_path + " -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  auto cert_tool = LoadPEMCertificate(out_path_tool);
  auto cert_openssl = LoadPEMCertificate(out_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr);
  ASSERT_TRUE(cert_openssl != nullptr);

  // Both should have valid serial numbers (non-zero)
  ASN1_INTEGER *serial_tool = X509_get_serialNumber(cert_tool.get());
  ASN1_INTEGER *serial_openssl = X509_get_serialNumber(cert_openssl.get());
  ASSERT_TRUE(serial_tool != nullptr);
  ASSERT_TRUE(serial_openssl != nullptr);

  // Clean up .srl files
  std::string srl_path =
      std::string(ca_cert_path)
          .substr(0, std::string(ca_cert_path).find_last_of('.')) +
      ".srl";
  RemoveFile(srl_path.c_str());
}

// Test SetSerial functionality against OpenSSL with existing .srl file
TEST_F(X509ComparisonTest, X509ToolCompareSetSerialExistingFileOpenSSL) {
  // Create existing .srl file with known serial number
  std::string srl_path =
      std::string(ca_cert_path)
          .substr(0, std::string(ca_cert_path).find_last_of('.')) +
      ".srl";
  ScopedFILE srl_file(fopen(srl_path.c_str(), "w"));
  ASSERT_TRUE(srl_file);
  fprintf(srl_file.get(), "1234ABCD\n");
  srl_file.reset();

  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -CA " + ca_cert_path + " -CAkey " +
                             ca_key_path + " -out " + out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " x509 -in " + in_path + " -CA " +
      ca_cert_path + " -CAkey " + ca_key_path + " -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  auto cert_tool = LoadPEMCertificate(out_path_tool);
  auto cert_openssl = LoadPEMCertificate(out_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr);
  ASSERT_TRUE(cert_openssl != nullptr);

  // Both should have incremented the serial number
  ASN1_INTEGER *serial_tool = X509_get_serialNumber(cert_tool.get());
  ASN1_INTEGER *serial_openssl = X509_get_serialNumber(cert_openssl.get());
  ASSERT_TRUE(serial_tool != nullptr);
  ASSERT_TRUE(serial_openssl != nullptr);

  // Clean up .srl files
  RemoveFile(srl_path.c_str());
}

// Test AdaptKeyIDExtension with existing valid key identifier extensions
TEST_F(X509ComparisonTest, X509ToolCompareKeyIDExtensionValidOpenSSL) {
  char ext_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(ext_path), 0u);

  // Create extension file with valid key identifiers
  ScopedFILE ext_file(fopen(ext_path, "w"));
  ASSERT_TRUE(ext_file);
  fprintf(ext_file.get(), "[test_ext]\n");
  fprintf(ext_file.get(), "subjectKeyIdentifier=hash\n");
  fprintf(ext_file.get(), "authorityKeyIdentifier=keyid:always\n");
  fclose(ext_file.release());

  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -signkey " + signkey_path +
                             " -extfile " + ext_path + " -extensions test_ext" +
                             " -out " + out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " x509 -in " + in_path +
      " -signkey " + signkey_path + " -extfile " + ext_path +
      " -extensions test_ext -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  auto cert_tool = LoadPEMCertificate(out_path_tool);
  auto cert_openssl = LoadPEMCertificate(out_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr);
  ASSERT_TRUE(cert_openssl != nullptr);

  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 30));

  RemoveFile(ext_path);
}

// Test AdaptKeyIDExtension with self-signed cert missing authorityKeyIdentifier
TEST_F(X509ComparisonTest, X509ToolCompareKeyIDExtensionSelfSignedOpenSSL) {
  char ext_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(ext_path), 0u);

  // Create extension file with only subjectKeyIdentifier (no
  // authorityKeyIdentifier)
  ScopedFILE ext_file(fopen(ext_path, "w"));
  ASSERT_TRUE(ext_file);
  fprintf(ext_file.get(), "[test_ext]\n");
  fprintf(ext_file.get(), "subjectKeyIdentifier=hash\n");
  fprintf(ext_file.get(), "basicConstraints=CA:TRUE\n");
  fclose(ext_file.release());

  // Self-sign the certificate (same key for signing and subject)
  std::string tool_command = std::string(tool_executable_path) + " x509 -in " +
                             in_path + " -signkey " + signkey_path +
                             " -extfile " + ext_path + " -extensions test_ext" +
                             " -out " + out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " x509 -in " + in_path +
      " -signkey " + signkey_path + " -extfile " + ext_path +
      " -extensions test_ext -out " + out_path_openssl;

  ExecuteCommand(tool_command);
  ExecuteCommand(openssl_command);

  auto cert_tool = LoadPEMCertificate(out_path_tool);
  auto cert_openssl = LoadPEMCertificate(out_path_openssl);

  ASSERT_TRUE(cert_tool != nullptr);
  ASSERT_TRUE(cert_openssl != nullptr);

  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 30));

  RemoveFile(ext_path);
}
