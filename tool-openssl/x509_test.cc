// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "openssl/x509.h"
#include <gtest/gtest.h>
#include <openssl/pem.h>
#include <cctype>
#include <ctime>
#include <functional>
#include <limits>
#include <sstream>
#include "../crypto/test/test_util.h"
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
TEST_F(X509Test, InOut) {
  args_list_t args = {"-in", in_path, "-out", out_path};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
  {
    ScopedFILE out_file(fopen(out_path, "rb"));
    ASSERT_TRUE(out_file);
    bssl::UniquePtr<X509> parsed_x509(
        PEM_read_X509(out_file.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(parsed_x509);
  }
}

// Test -modulus
TEST_F(X509Test, Modulus) {
  args_list_t args = {"-in", in_path, "-modulus"};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -subject
TEST_F(X509Test, Subject) {
  args_list_t args = {"-in", in_path, "-subject"};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -subject_hash and -subject_hash_old
TEST_F(X509Test, SubjectHash) {
  args_list_t args = {"-in", in_path, "-subject_hash"};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  args = {"-in", in_path, "-subject_hash_old"};
  result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -fingerprint
TEST_F(X509Test, Fingerprint) {
  args_list_t args = {"-in", in_path, "-fingerprint"};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test signkey
TEST_F(X509Test, Signkey) {
  args_list_t args = {"-in", in_path, "-signkey", signkey_path};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -days
TEST_F(X509Test, Days) {
  args_list_t args = {"-in",      in_path,      "-out",  out_path,
                      "-signkey", signkey_path, "-days", "365"};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -dates
TEST_F(X509Test, Dates) {
  args_list_t args = {"-in", in_path, "-dates"};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -enddate
TEST_F(X509Test, Enddate) {
  args_list_t args = {"-in", in_path, "-enddate"};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -inform
TEST_F(X509Test, Inform) {
  args_list_t args = {"-in", der_cert_path, "-inform", "DER"};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  args = {"-in", in_path, "-inform", "PEM"};
  result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -outform
TEST_F(X509Test, Outform) {
  args_list_t args = {"-in", in_path, "-out", out_path, "-outform", "DER"};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  ScopedFILE out_file(fopen(out_path, "rb"));
  ASSERT_TRUE(out_file);
  bssl::UniquePtr<X509> parsed_x509(d2i_X509_fp(out_file.get(), nullptr));
  ASSERT_TRUE(parsed_x509);

  args = {"-in", in_path, "-out", out_path, "-outform", "PEM"};
  result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  out_file.reset(fopen(out_path, "rb"));
  ASSERT_TRUE(out_file);
  parsed_x509.reset(PEM_read_X509(out_file.get(), nullptr, nullptr, nullptr));
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -checkend. The exit status is 0 when the certificate will not expire
// within the window and 1 when it will. The test certificate is valid for 30
// days.
TEST_F(X509Test, Checkend) {
  args_list_t args = {"-in", in_path, "-checkend", "3600"};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  args_list_t expiring_args = {"-in", in_path, "-checkend",
                               std::to_string(60 * 60 * 24 * 31L)};
  ASSERT_EQ(1, X509Tool(expiring_args));

  // -checkend writes only its verdict, never the certificate, to -out.
  args_list_t expiring_out_args = {
      "-in",  in_path, "-checkend", std::to_string(60 * 60 * 24 * 31L),
      "-out", out_path};
  ASSERT_EQ(1, X509Tool(expiring_out_args));
  std::string out_contents = ReadFileToString(out_path);
  EXPECT_EQ("Certificate will expire\n", out_contents);
}

struct CheckendRangeCase {
  int days;
  int64_t seconds;
  int expected_exit;
};

static const CheckendRangeCase kCheckendRangeCases[] = {
    {30, 0, kToolExitSuccess},          {30, 2678400, kToolExitFailure},
    {30, 2147483648, kToolExitFailure}, {30, 4294967296, kToolExitFailure},
    {30000, 0, kToolExitSuccess},       {-30000, 0, kToolExitFailure},
};

TEST_F(X509Test, CheckendRange) {
  bssl::UniquePtr<X509> cert;
  bssl::UniquePtr<EVP_PKEY> key;
  CreateAndSignX509Certificate(cert, &key);
  ASSERT_TRUE(cert);
  ASSERT_TRUE(key);

  for (const auto &test : kCheckendRangeCases) {
    SCOPED_TRACE(test.days);
    SCOPED_TRACE(test.seconds);
    // Use day offsets so constructing the test certificate does not itself
    // overflow a 32-bit seconds count.
    ASSERT_TRUE(
        X509_time_adj_ex(X509_getm_notBefore(cert.get()), -30001, 0, nullptr));
    ASSERT_TRUE(X509_time_adj_ex(X509_getm_notAfter(cert.get()), test.days, 0,
                                 nullptr));
    ASSERT_GT(X509_sign(cert.get(), key.get(), EVP_sha256()), 0);
    {
      ScopedFILE cert_file(fopen(in_path, "wb"));
      ASSERT_TRUE(cert_file);
      ASSERT_TRUE(PEM_write_X509(cert_file.get(), cert.get()));
    }

    args_list_t args = {"-in",       in_path,
                        "-checkend", std::to_string(test.seconds),
                        "-out",      out_path};
    EXPECT_EQ(test.expected_exit, X509Tool(args));
    EXPECT_EQ(test.expected_exit == kToolExitSuccess
                  ? "Certificate will not expire\n"
                  : "Certificate will expire\n",
              ReadFileToString(out_path));
  }
}

TEST_F(X509Test, CheckendWindowParsing) {
  const struct {
    const char *seconds;
    int expected_exit;
    const char *expected_output;
  } cases[] = {
      {"0000", kToolExitSuccess, "Certificate will not expire\n"},
      {"00002678400", kToolExitFailure, "Certificate will expire\n"},
      {"9223372036854775807", kToolExitFailure, "Certificate will expire\n"},
      {"9223372036854775808", kToolExitFailure, ""},
      {"18446744073709551616", kToolExitFailure, ""},
      {"", kToolExitFailure, ""},
      {"1x", kToolExitFailure, ""},
  };
  for (const auto &test : cases) {
    SCOPED_TRACE(test.seconds);
    args_list_t args = {"-in",        in_path, "-checkend",
                        test.seconds, "-out",  out_path};
    EXPECT_EQ(test.expected_exit, X509Tool(args));
    EXPECT_EQ(test.expected_output, ReadFileToString(out_path));
  }
}

// Test -req
TEST_F(X509Test, Req) {
  args_list_t args = {"-in",        csr_path, "-req",  "-signkey",
                      signkey_path, "-out",   out_path};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -pubkey
TEST_F(X509Test, Pubkey) {
  args_list_t args = {"-in", in_path, "-pubkey"};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -CA and -CAkey
TEST_F(X509Test, CA) {
  args_list_t args = {"-in",        in_path,  "-CA",
                      ca_cert_path, "-CAkey", ca_key_path};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  args = {"-in", in_path, "-CA", ca_cert_path};  // use key in CA file
  result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  args = {"-in", csr_path, "-req", "-CA", ca_cert_path, "-CAkey", ca_key_path};
  result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -extfile and -extensions
TEST_F(X509Test, Extension) {
  char ext_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(ext_path), 0u);

  ScopedFILE ext_file(fopen(ext_path, "w"));
  ASSERT_TRUE(ext_file);
  fprintf(ext_file.get(), "[test_ext]\nbasicConstraints=CA:FALSE\n");
  fclose(ext_file.release());

  args_list_t args = {"-in",      csr_path,      "-req",
                      "-signkey", signkey_path,  "-extfile",
                      ext_path,   "-extensions", "test_ext"};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);

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
  ASSERT_EQ(kToolExitSuccess, result);

  // Test extfile with extensions variable pointing to section
  ext_file.reset(fopen(ext_path, "w"));
  ASSERT_TRUE(ext_file);
  fprintf(ext_file.get(),
          "extensions=v3_req\n\n[v3_req]\nbasicConstraints=CA:FALSE\nkeyUsage="
          "digitalSignature,keyEncipherment\n");
  fclose(ext_file.release());

  args = {"-in", in_path, "-signkey", signkey_path, "-extfile", ext_path};
  result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  RemoveFile(ext_path);
}

// Test -passin with -signkey
TEST_F(X509Test, PassinSignkey) {
  args_list_t args = {"-in",      in_path,
                      "-signkey", protected_signkey_path,
                      "-passin",  "pass:testpassword"};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -passin with -CA (key in CA file)
TEST_F(X509Test, PassinCA) {
  args_list_t args = {"-in",     in_path,
                      "-CA",     protected_ca_cert_path,
                      "-passin", "pass:testpassword"};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -passin with -CA and -CAkey
TEST_F(X509Test, PassinCAkey) {
  args_list_t args = {"-in",     in_path,
                      "-CA",     ca_cert_path,
                      "-CAkey",  protected_ca_key_path,
                      "-passin", "pass:testpassword"};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -passin with -req and -signkey
TEST_F(X509Test, PassinReqSignkey) {
  args_list_t args = {
      "-in",     csr_path,           "-req", "-signkey", protected_signkey_path,
      "-passin", "pass:testpassword"};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test SetSerial functionality with CA certificate
TEST_F(X509Test, SetSerial) {
  // Test 1: First certificate with CA - should create .srl file
  args_list_t args = {"-in",    in_path,     "-CA",  ca_cert_path,
                      "-CAkey", ca_key_path, "-out", out_path};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);

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
  serial1 = serial1.substr(
      0, serial1.find_first_of(
             "\r\n"));  // Remove newline (handles both \r\n and \n)

  // Verify the first certificate serial matches the .srl file content
  auto cert1 = LoadPEMCertificate(out_path);
  ASSERT_TRUE(cert1);
  ASN1_INTEGER *cert_serial = X509_get_serialNumber(cert1.get());
  ASSERT_TRUE(cert_serial);

  bssl::UniquePtr<BIGNUM> bn(ASN1_INTEGER_to_BN(cert_serial, nullptr));
  ASSERT_TRUE(bn);
  bssl::UniquePtr<char> hex_str(BN_bn2hex(bn.get()));
  ASSERT_TRUE(hex_str);

  ASSERT_EQ(serial1, std::string(hex_str.get()));
  srl_file.reset();

  // Test 2: Second certificate with same CA - should increment serial
  args = {"-in",    in_path,     "-CA",  ca_cert_path,
          "-CAkey", ca_key_path, "-out", out_path};
  result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  // Read updated serial number
  std::string serial2 = ReadFileToString(srl_path.c_str());
  ASSERT_FALSE(serial2.empty());
  serial2 = serial2.substr(
      0, serial2.find_first_of(
             "\r\n"));  // Remove newline (handles both \r\n and \n)

  // Serial numbers should be different
  ASSERT_NE(serial1, serial2);

  // Verify the certificate serial matches the .srl file content
  auto cert2 = LoadPEMCertificate(out_path);
  ASSERT_TRUE(cert2);
  cert_serial = X509_get_serialNumber(cert2.get());
  ASSERT_TRUE(cert_serial);

  // Convert certificate serial to hex string for comparison
  bn.reset(ASN1_INTEGER_to_BN(cert_serial, nullptr));
  ASSERT_TRUE(bn);
  hex_str.reset(BN_bn2hex(bn.get()));
  ASSERT_TRUE(hex_str);

  ASSERT_EQ(serial2, std::string(hex_str.get()));

  // Clean up
  RemoveFile(srl_path.c_str());
}

// Test serial generation without CA (random serial generation)
TEST_F(X509Test, BasicSerialGeneration) {
  // Test self-signed certificates - should generate random serials
  args_list_t args = {"-in",        in_path, "-signkey",
                      signkey_path, "-out",  out_path};
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);


  auto cert1 = LoadPEMCertificate(out_path);
  ASSERT_TRUE(cert1);

  args = {"-in", in_path, "-signkey", signkey_path, "-out", out_path};
  result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  auto cert2 = LoadPEMCertificate(out_path);
  ASSERT_TRUE(cert2);

  // Verify certificates have different serial numbers
  ASN1_INTEGER *serial1 = X509_get_serialNumber(cert1.get());
  ASN1_INTEGER *serial2 = X509_get_serialNumber(cert2.get());
  ASSERT_TRUE(serial1);
  ASSERT_TRUE(serial2);

  // Serial numbers should be different
  ASSERT_NE(0, ASN1_INTEGER_cmp(serial1, serial2));
}

// Test serial generation with existing .srl file
TEST_F(X509Test, SerialGenerationExistingFile) {
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
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  // Read updated serial number from .srl file
  std::string new_serial = ReadFileToString(srl_path.c_str());
  ASSERT_FALSE(new_serial.empty());

  // Serial should be incremented from 1234ABCD to 1234ABCE
  // Strip trailing newline characters for comparison (handles both \r\n and \n)
  new_serial = new_serial.substr(0, new_serial.find_first_of("\r\n"));
  ASSERT_EQ("1234ABCE", new_serial);

  // Verify the certificate serial matches the .srl file content
  auto cert = LoadPEMCertificate(out_path);
  ASSERT_TRUE(cert);
  ASN1_INTEGER *cert_serial = X509_get_serialNumber(cert.get());
  ASSERT_TRUE(cert_serial);

  bssl::UniquePtr<BIGNUM> bn(ASN1_INTEGER_to_BN(cert_serial, nullptr));
  ASSERT_TRUE(bn);
  bssl::UniquePtr<char> hex_str(BN_bn2hex(bn.get()));
  ASSERT_TRUE(hex_str);

  // new_serial already stripped above, no need to strip again
  ASSERT_EQ(new_serial, std::string(hex_str.get()));

  // Clean up
  RemoveFile(srl_path.c_str());
}

// Test AKID serial number
TEST_F(X509Test, AKIDSerialWithCA) {
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
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);

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
  ASSERT_EQ(ASN1_INTEGER_cmp(ca_serial, akid->serial), 0);

  RemoveFile(ext_path);
}

// Test AKID serial number
TEST_F(X509Test, AKIDSerialSelfSigned) {
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
  int result = X509Tool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  // Verify the certificate serial matches the .srl file content
  auto cert = LoadPEMCertificate(out_path);
  ASSERT_TRUE(cert);
  ASN1_INTEGER *cert_serial = X509_get_serialNumber(cert.get());
  ASSERT_TRUE(cert_serial);

  // Verify AKID serial number matches CA serial number
  bssl::UniquePtr<AUTHORITY_KEYID> akid(static_cast<AUTHORITY_KEYID *>(
      X509_get_ext_d2i(cert.get(), NID_authority_key_identifier, NULL, NULL)));
  ASSERT_TRUE(akid);
  ASSERT_EQ(ASN1_INTEGER_cmp(cert_serial, akid->serial), 0);

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
    int result = X509Tool(c_args);
    ASSERT_EQ(kToolExitFailure, result);
  }
};

//  Test mutually exclusive options
TEST_F(X509OptionUsageErrorsTest, MutuallyExclusiveOptions) {
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

TEST_F(X509OptionUsageErrorsTest, RequiredOptions) {
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
TEST_F(X509OptionUsageErrorsTest, DaysAndCheckendArgs) {
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

TEST_F(X509OptionUsageErrorsTest, InvalidArgs) {
  std::vector<std::vector<std::string>> testparams = {
      {"-in", in_path, "-inform", "RANDOM"},
      {"-in", in_path, "-out", out_path, "-outform", "RANDOM"},
      {"-in", in_path, "-nameopt", ""},
      {"-in", in_path, "-nameopt", "bogus"},
      {"-in", in_path, "-subject", "-nameopt", "oneline,-esc_msb"}};
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// Test -passin with invalid formats and wrong passwords
TEST_F(X509OptionUsageErrorsTest, InvalidPassin) {
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
TEST_F(X509ComparisonTest, Text) {
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
TEST_F(X509ComparisonTest, Modulus) {
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
TEST_F(X509ComparisonTest, Subject) {
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
TEST_F(X509ComparisonTest, Fingerprint) {
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
TEST_F(X509ComparisonTest, ReorderedFingerprint) {
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
TEST_F(X509ComparisonTest, HashFingerprint) {
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
TEST_F(X509ComparisonTest, Pubkey) {
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
TEST_F(X509ComparisonTest, SubjectFingerprint) {
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
TEST_F(X509ComparisonTest, ReorderedSubjectFingerprint) {
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
TEST_F(X509ComparisonTest, Checkend) {
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

// Compare both the exit status and verdict, including time ranges that do
// not fit in 32-bit seconds.
TEST_F(X509ComparisonTest, CheckendExitCode) {
  bssl::UniquePtr<EVP_PKEY> key;
  CreateAndSignX509Certificate(x509, &key);
  ASSERT_TRUE(x509);
  ASSERT_TRUE(key);

  for (const auto &test : kCheckendRangeCases) {
    SCOPED_TRACE(test.days);
    SCOPED_TRACE(test.seconds);
    // The reference OpenSSL adds the window to a time_t. Its 32-bit builds
    // cannot represent the large windows tested by CheckendRange above.
    if (test.seconds >
        std::numeric_limits<time_t>::max() - std::time(nullptr)) {
      continue;
    }
    ASSERT_TRUE(
        X509_time_adj_ex(X509_getm_notBefore(x509.get()), -30001, 0, nullptr));
    ASSERT_TRUE(X509_time_adj_ex(X509_getm_notAfter(x509.get()), test.days, 0,
                                 nullptr));
    ASSERT_GT(X509_sign(x509.get(), key.get(), EVP_sha256()), 0);
    {
      ScopedFILE cert_file(fopen(in_path, "wb"));
      ASSERT_TRUE(cert_file);
      ASSERT_TRUE(PEM_write_X509(cert_file.get(), x509.get()));
    }

    std::string tool_command = std::string(tool_executable_path) +
                               " x509 -in " + in_path + " -noout -checkend " +
                               std::to_string(test.seconds) + " > " +
                               out_path_tool;
    std::string openssl_command =
        std::string(openssl_executable_path) + " x509 -in " + in_path +
        " -noout -checkend " + std::to_string(test.seconds) + " > " +
        out_path_openssl;

    int tool_exit = ExecuteCommandExitCode(tool_command);
    int openssl_exit = ExecuteCommandExitCode(openssl_command);
    EXPECT_EQ(test.expected_exit, tool_exit);
    EXPECT_EQ(openssl_exit, tool_exit);
    EXPECT_EQ(ReadFileToString(out_path_openssl),
              ReadFileToString(out_path_tool));
  }
}

// Test against OpenSSL output "openssl x509 -req -in csr_file -signkey
// private_key_file -days 80 -out out_file"
TEST_F(X509ComparisonTest, ReqSignkeyDays) {
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

  ASSERT_TRUE(cert_tool) << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 365 days validity period
  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 80))
      << "Certificates generated by tool and OpenSSL have different attributes";
}

// Test against OpenSSL output "openssl x509 -in file -dates -noout"
TEST_F(X509ComparisonTest, DatesNoout) {
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
TEST_F(X509ComparisonTest, DatesEnddate) {
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
TEST_F(X509ComparisonTest, InformDEREnddate) {
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
TEST_F(X509ComparisonTest, InformPEMEnddate) {
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
TEST_F(X509ComparisonTest, StdinFingerprintDates) {
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
TEST_F(X509ComparisonTest, SignkeyOutformPEM) {
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

  ASSERT_TRUE(cert_tool) << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl)
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

  ASSERT_TRUE(cert_tool) << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 365 days validity period
  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 30))
      << "Certificates generated by tool and OpenSSL have different attributes";
}

// Test against OpenSSL output "openssl x509 -in in_file (-req) -signkey
// private_key_file -out out_file -outform DER"
TEST_F(X509ComparisonTest, SignkeyOutformDER) {
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

  ASSERT_TRUE(cert_tool) << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl)
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

  ASSERT_TRUE(cert_tool) << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 30 days validity period
  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 30))
      << "Certificates generated by tool and OpenSSL have different attributes";
}


// Test against OpenSSL output "openssl x509 -in in_file -CA certfile -CAkey
// keyfile"
TEST_F(X509ComparisonTest, CA) {
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

  ASSERT_TRUE(cert_tool) << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl)
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

  ASSERT_TRUE(cert_tool) << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 365 days validity period
  ASSERT_TRUE(CompareCertificates(cert_tool.get(), cert_openssl.get(),
                                  ca_cert.get(), 30))
      << "Certificates generated by tool and OpenSSL have different attributes";
}

// Test against OpenSSL output "openssl x509 -in in_file -CA certfile -CAkey
// keyfile"
TEST_F(X509ComparisonTest, ReqCA) {
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

  ASSERT_TRUE(cert_tool) << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl)
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

  ASSERT_TRUE(cert_tool) << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 365 days validity period
  ASSERT_TRUE(CompareCertificates(cert_tool.get(), cert_openssl.get(),
                                  ca_cert.get(), 30))
      << "Certificates generated by tool and OpenSSL have different attributes";
}

// Test against OpenSSL output with -passin option
TEST_F(X509ComparisonTest, Passin) {
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

  ASSERT_TRUE(cert_tool) << "Failed to load certificate generated by tool";
  ASSERT_TRUE(cert_openssl)
      << "Failed to load certificate generated by OpenSSL";

  // Compare certificates in detail with 30 days validity period
  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 30))
      << "Certificates generated by tool and OpenSSL have different attributes";
}

// Test against OpenSSL output "openssl x509 -extfile extfile -extensions
// extension_header"
TEST_F(X509ComparisonTest, Extensions) {
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

  ASSERT_TRUE(cert_tool);
  ASSERT_TRUE(cert_openssl);

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

  ASSERT_TRUE(cert_tool);
  ASSERT_TRUE(cert_openssl);

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

  ASSERT_TRUE(cert_tool);
  ASSERT_TRUE(cert_openssl);

  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 30));

  RemoveFile(ext_path);
}

// Test serial generation against OpenSSL
TEST_F(X509ComparisonTest, BasicSerialGeneration) {
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

  ASSERT_TRUE(cert_tool);
  ASSERT_TRUE(cert_openssl);

  // Both should have valid serial numbers (non-zero)
  ASN1_INTEGER *serial_tool = X509_get_serialNumber(cert_tool.get());
  ASN1_INTEGER *serial_openssl = X509_get_serialNumber(cert_openssl.get());
  ASSERT_TRUE(serial_tool);
  ASSERT_TRUE(serial_openssl);

  // Clean up .srl files
  std::string srl_path =
      std::string(ca_cert_path)
          .substr(0, std::string(ca_cert_path).find_last_of('.')) +
      ".srl";
  RemoveFile(srl_path.c_str());
}

// Test serial generation against OpenSSL with existing .srl file
TEST_F(X509ComparisonTest, SerialGenerationExistingFile) {
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

  ASSERT_TRUE(cert_tool);
  ASSERT_TRUE(cert_openssl);

  // Both should have incremented the serial number
  ASN1_INTEGER *serial_tool = X509_get_serialNumber(cert_tool.get());
  ASN1_INTEGER *serial_openssl = X509_get_serialNumber(cert_openssl.get());
  ASSERT_TRUE(serial_tool);
  ASSERT_TRUE(serial_openssl);

  // Clean up .srl files
  RemoveFile(srl_path.c_str());
}

// Test AdaptKeyIDExtension with existing valid key identifier extensions
TEST_F(X509ComparisonTest, KeyIDExtensionValid) {
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

  ASSERT_TRUE(cert_tool);
  ASSERT_TRUE(cert_openssl);

  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 30));

  RemoveFile(ext_path);
}

// Test AdaptKeyIDExtension with self-signed cert missing authorityKeyIdentifier
TEST_F(X509ComparisonTest, KeyIDExtensionSelfSigned) {
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

  ASSERT_TRUE(cert_tool);
  ASSERT_TRUE(cert_openssl);

  ASSERT_TRUE(
      CompareCertificates(cert_tool.get(), cert_openssl.get(), nullptr, 30));

  RemoveFile(ext_path);
}

// -------------------- -nameopt and -text name/label tests --------------------

// ConfigureCertFn populates |name| (and may add extensions to |x509|)
// before the certificate returned by BuildSelfSignedCert is signed.
using ConfigureCertFn = std::function<bool(X509 *x509, X509_NAME *name)>;

// BuildSelfSignedCert creates a minimal self-signed RSA-2048/SHA-256
// certificate. |configure| fills in the empty subject/issuer name and may add
// extensions before signing. Returns null on failure.
static bssl::UniquePtr<X509> BuildSelfSignedCert(
    const ConfigureCertFn &configure) {
  bssl::UniquePtr<X509> x509(X509_new());
  if (!x509 || !X509_set_version(x509.get(), X509_VERSION_3)) {
    return nullptr;
  }
  if (!X509_gmtime_adj(X509_getm_notBefore(x509.get()), 0) ||
      !X509_gmtime_adj(X509_getm_notAfter(x509.get()), 60 * 60 * 24 * 30L)) {
    return nullptr;
  }

  bssl::UniquePtr<RSA> rsa(RSA_new());
  bssl::UniquePtr<BIGNUM> bn(BN_new());
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  if (!rsa || !bn || !pkey || !BN_set_word(bn.get(), RSA_F4) ||
      !RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr) ||
      !EVP_PKEY_assign_RSA(pkey.get(), rsa.release()) ||
      !X509_set_pubkey(x509.get(), pkey.get())) {
    return nullptr;
  }

  bssl::UniquePtr<X509_NAME> name(X509_NAME_new());
  if (!name || !configure(x509.get(), name.get())) {
    return nullptr;
  }
  if (!X509_set_subject_name(x509.get(), name.get()) ||
      !X509_set_issuer_name(x509.get(), name.get())) {
    return nullptr;
  }

  bssl::UniquePtr<ASN1_INTEGER> serial(ASN1_INTEGER_new());
  if (!serial || !ASN1_INTEGER_set(serial.get(), 1) ||
      !X509_set_serialNumber(x509.get(), serial.get())) {
    return nullptr;
  }

  if (X509_sign(x509.get(), pkey.get(), EVP_sha256()) <= 0) {
    return nullptr;
  }
  return x509;
}

// WriteCertToFile PEM-encodes |x509| to |path|.
static bool WriteCertToFile(X509 *x509, const char *path) {
  ScopedFILE file(fopen(path, "wb"));
  return file && PEM_write_X509(file.get(), x509);
}

// AddRawExtension adds an extension with type |obj| and raw OCTET STRING
// content |data| to |x509|. This synthesizes extensions AWS-LC has no
// |X509V3_EXT_METHOD| for, such as the CT SCT list.
static bool AddRawExtension(X509 *x509, const ASN1_OBJECT *obj, bool critical,
                            const uint8_t *data, size_t data_len) {
  bssl::UniquePtr<ASN1_OCTET_STRING> value(ASN1_OCTET_STRING_new());
  if (!value ||
      !ASN1_OCTET_STRING_set(value.get(), data, static_cast<int>(data_len))) {
    return false;
  }
  bssl::UniquePtr<X509_EXTENSION> ext(X509_EXTENSION_create_by_OBJ(
      nullptr, obj, critical ? 1 : 0, value.get()));
  return ext && X509_add_ext(x509, ext.get(), -1);
}

// ContainsExtensionLabelLine returns true if |output| contains a line that,
// after trimming whitespace, is exactly "|label|:", as callers grepping -text
// output for an extension header expect.
static bool ContainsExtensionLabelLine(const std::string &output,
                                       const std::string &label) {
  const std::string expected = label + ":";
  std::istringstream stream(output);
  std::string line;
  while (std::getline(stream, line)) {
    if (trim(line) == expected) {
      return true;
    }
  }
  return false;
}

// ExtractLastCNValue emulates `openssl x509 -noout -subject | sed 's/.*CN=//'`:
// it returns the text after the last "CN=" on the first line of |output|.
static std::string ExtractLastCNValue(const std::string &output) {
  size_t line_end = output.find('\n');
  std::string line =
      line_end == std::string::npos ? output : output.substr(0, line_end);
  size_t cn_pos = line.rfind("CN=");
  return cn_pos == std::string::npos ? line : line.substr(cn_pos + 3);
}

// Scripts commonly extract the leaf CN with `sed 's/.*CN=//'`, which only
// works when -subject prints tight "TAG=value" pairs. The previous
// XN_FLAG_ONELINE default printed "CN = value" and broke this, including for
// subjects with multiple CNs and a multi-valued RDN as built here.
TEST_F(X509Test, SubjectMultiRDNCommonNameFallback) {
  bssl::UniquePtr<X509> x509 = BuildSelfSignedCert([](X509 * /*cert*/,
                                                      X509_NAME *name) {
    return X509_NAME_add_entry_by_NID(
               name, NID_countryName, MBSTRING_UTF8,
               reinterpret_cast<const unsigned char *>("US"), -1, -1, 0) &&
           X509_NAME_add_entry_by_NID(
               name, NID_organizationName, MBSTRING_UTF8,
               reinterpret_cast<const unsigned char *>("Example, Inc."), -1, -1,
               0) &&
           // OU and the first CN form one multi-valued RDN ("+"
           // grouped).
           X509_NAME_add_entry_by_NID(
               name, NID_organizationalUnitName, MBSTRING_UTF8,
               reinterpret_cast<const unsigned char *>("Eng"), -1, -1, 0) &&
           X509_NAME_add_entry_by_NID(
               name, NID_commonName, MBSTRING_UTF8,
               reinterpret_cast<const unsigned char *>("First"), -1, -1, -1) &&
           // The second, trailing CN is its own (final) RDN.
           X509_NAME_add_entry_by_NID(
               name, NID_commonName, MBSTRING_UTF8,
               reinterpret_cast<const unsigned char *>("Second"), -1, -1, 0);
  });
  ASSERT_TRUE(x509);
  ASSERT_TRUE(WriteCertToFile(x509.get(), in_path));

  args_list_t args = {"-in", in_path, "-noout", "-subject", "-out", out_path};
  ASSERT_EQ(kToolExitSuccess, X509Tool(args));

  std::string output = ReadFileToString(out_path);
  EXPECT_EQ("subject=C=US, O=Example, Inc., OU=Eng + CN=First, CN=Second\n",
            output);
  EXPECT_EQ("Second", ExtractLastCNValue(output));
}

// SAN entries in -text are printed by GENERAL_NAMES' i2v method, not
// X509_NAME_print_ex, and so must be unaffected by the -subject default change.
TEST_F(X509Test, TextSubjectAltNameCallerPattern) {
  bssl::UniquePtr<X509> x509 = BuildSelfSignedCert([](X509 *cert,
                                                      X509_NAME *name) {
    if (!X509_NAME_add_entry_by_NID(
            name, NID_commonName, MBSTRING_UTF8,
            reinterpret_cast<const unsigned char *>("san-test"), -1, -1, 0)) {
      return false;
    }
    X509V3_CTX ctx;
    X509V3_set_ctx_nodb(&ctx);
    X509V3_set_ctx(&ctx, cert, cert, nullptr, nullptr, 0);
    bssl::UniquePtr<X509_EXTENSION> ext(X509V3_EXT_conf_nid(
        nullptr, &ctx, NID_subject_alt_name,
        const_cast<char *>("DNS:example.com,DNS:www.example.com")));
    return ext && X509_add_ext(cert, ext.get(), -1) != 0;
  });
  ASSERT_TRUE(x509);
  ASSERT_TRUE(WriteCertToFile(x509.get(), in_path));

  args_list_t args = {"-in", in_path, "-noout", "-text", "-out", out_path};
  ASSERT_EQ(kToolExitSuccess, X509Tool(args));

  std::string output = ReadFileToString(out_path);
  EXPECT_NE(std::string::npos, output.find("X509v3 Subject Alternative Name:"));
  EXPECT_NE(std::string::npos,
            output.find("DNS:example.com, DNS:www.example.com"));
}

// -text labels the SCT list extension (NID_ct_precert_scts) by name rather
// than raw OID. Only the OID is registered; its contents are still printed by
// the generic unknown-extension fallback. 1.3.101.77 is an unregistered
// control OID that must continue to print in dotted form.
TEST_F(X509Test, TextCTPrecertSCTsLabelAndUnregisteredOID) {
  bssl::UniquePtr<X509> x509 = BuildSelfSignedCert([](X509 *cert,
                                                      X509_NAME *name) {
    if (!X509_NAME_add_entry_by_NID(
            name, NID_commonName, MBSTRING_UTF8,
            reinterpret_cast<const unsigned char *>("sct-test"), -1, -1, 0)) {
      return false;
    }

    static const uint8_t kSCTPayload[] = {0x01, 0x02, 0x03};
    if (!AddRawExtension(cert, OBJ_nid2obj(NID_ct_precert_scts),
                         /*critical=*/false, kSCTPayload,
                         sizeof(kSCTPayload))) {
      return false;
    }

    bssl::UniquePtr<ASN1_OBJECT> unregistered_oid(
        OBJ_txt2obj("1.3.101.77", /*dont_search_names=*/1));
    static const uint8_t kOtherPayload[] = {0x0a, 0x0b, 0x0c};
    return unregistered_oid &&
           AddRawExtension(cert, unregistered_oid.get(),
                           /*critical=*/false, kOtherPayload,
                           sizeof(kOtherPayload));
  });
  ASSERT_TRUE(x509);
  ASSERT_TRUE(WriteCertToFile(x509.get(), in_path));

  args_list_t args = {"-in", in_path, "-noout", "-text", "-out", out_path};
  ASSERT_EQ(kToolExitSuccess, X509Tool(args));

  std::string output = ReadFileToString(out_path);
  EXPECT_TRUE(ContainsExtensionLabelLine(output, "CT Precertificate SCTs"))
      << output;
  EXPECT_TRUE(ContainsExtensionLabelLine(output, "1.3.101.77")) << output;
}

// Exact output for each -nameopt preset, verified against OpenSSL 3.6.4.
// "compat" differs: X509_NAME_oneline does not mark multi-valued RDNs
// with '+'.
TEST_F(X509Test, SubjectNameoptPresets) {
  bssl::UniquePtr<X509> x509 = BuildSelfSignedCert([](X509 * /*cert*/,
                                                      X509_NAME *name) {
    return X509_NAME_add_entry_by_NID(
               name, NID_countryName, MBSTRING_UTF8,
               reinterpret_cast<const unsigned char *>("US"), -1, -1, 0) &&
           X509_NAME_add_entry_by_NID(
               name, NID_organizationName, MBSTRING_UTF8,
               reinterpret_cast<const unsigned char *>("Example, Inc."), -1, -1,
               0) &&
           X509_NAME_add_entry_by_NID(
               name, NID_organizationalUnitName, MBSTRING_UTF8,
               reinterpret_cast<const unsigned char *>("Eng"), -1, -1, 0) &&
           X509_NAME_add_entry_by_NID(
               name, NID_commonName, MBSTRING_UTF8,
               reinterpret_cast<const unsigned char *>("First"), -1, -1, -1) &&
           X509_NAME_add_entry_by_NID(
               name, NID_commonName, MBSTRING_UTF8,
               reinterpret_cast<const unsigned char *>("Second"), -1, -1, 0);
  });
  ASSERT_TRUE(x509);
  ASSERT_TRUE(WriteCertToFile(x509.get(), in_path));

  const struct {
    const char *nameopt;  // nullptr means "omit -nameopt".
    const char *expected;
  } kCases[] = {
      {nullptr,
       "subject=C=US, O=Example, Inc., OU=Eng + CN=First, CN=Second\n"},
      {"oneline",
       "subject=C = US, O = \"Example, Inc.\", OU = Eng + CN = First, CN = "
       "Second\n"},
      {"RFC2253", "subject=CN=Second,CN=First+OU=Eng,O=Example\\, Inc.,C=US\n"},
      {"compat", "subject=/C=US/O=Example, Inc./OU=Eng/CN=First/CN=Second\n"},
      {"multiline",
       "subject=\n"
       "    countryName               = US\n"
       "    organizationName          = Example, Inc.\n"
       "    organizationalUnitName    = Eng + commonName                = "
       "First\n"
       "    commonName                = Second\n"},
  };

  for (const auto &c : kCases) {
    SCOPED_TRACE(c.nameopt ? c.nameopt : "(default)");
    args_list_t args = {"-in", in_path, "-noout", "-subject", "-out", out_path};
    if (c.nameopt != nullptr) {
      args.push_back("-nameopt");
      args.push_back(c.nameopt);
    }
    ASSERT_EQ(kToolExitSuccess, X509Tool(args));
    EXPECT_EQ(c.expected, ReadFileToString(out_path));
  }
}

TEST_F(X509Test, NameoptPresetsAreCaseInsensitive) {
  for (const auto &names : {std::make_pair("compat", "CoMpAt"),
                            std::make_pair("oneline", "ONELINE"),
                            std::make_pair("RFC2253", "rfc2253"),
                            std::make_pair("multiline", "MultiLine")}) {
    for (const char *option : {"-subject", "-text"}) {
      SCOPED_TRACE(names.second);
      SCOPED_TRACE(option);
      args_list_t args = {"-in",  in_path,  "-noout",   option,
                          "-out", out_path, "-nameopt", names.first};
      ASSERT_EQ(kToolExitSuccess, X509Tool(args));
      const std::string expected = ReadFileToString(out_path);
      args.back() = names.second;
      ASSERT_EQ(kToolExitSuccess, X509Tool(args));
      EXPECT_EQ(expected, ReadFileToString(out_path));
    }
  }
}

// -nameopt also governs -text's Issuer/Subject lines when given
// explicitly; with no -nameopt, -text's rendering is unchanged.
TEST_F(X509Test, TextNameoptAffectsSubjectIssuer) {
  bssl::UniquePtr<X509> x509 = BuildSelfSignedCert([](X509 * /*cert*/,
                                                      X509_NAME *name) {
    return X509_NAME_add_entry_by_NID(
               name, NID_organizationName, MBSTRING_UTF8,
               reinterpret_cast<const unsigned char *>("Example, Inc."), -1, -1,
               0) &&
           X509_NAME_add_entry_by_NID(
               name, NID_commonName, MBSTRING_UTF8,
               reinterpret_cast<const unsigned char *>("text-test"), -1, -1, 0);
  });
  ASSERT_TRUE(x509);
  ASSERT_TRUE(WriteCertToFile(x509.get(), in_path));

  args_list_t default_args = {"-in",   in_path, "-noout",
                              "-text", "-out",  out_path};
  ASSERT_EQ(kToolExitSuccess, X509Tool(default_args));
  std::string default_output = ReadFileToString(out_path);
  EXPECT_NE(std::string::npos,
            default_output.find("Subject: O=Example, Inc., CN=text-test"));

  args_list_t rfc_args = {"-in",      in_path,   "-noout", "-text",
                          "-nameopt", "RFC2253", "-out",   out_path};
  ASSERT_EQ(kToolExitSuccess, X509Tool(rfc_args));
  std::string rfc_output = ReadFileToString(out_path);
  EXPECT_NE(std::string::npos, rfc_output.find("Subject: CN=text-test"));
}

// The default -nameopt must escape control characters so a crafted subject
// cannot inject extra lines into the single-line "subject=" output.
TEST_F(X509Test, SubjectControlCharactersEscaped) {
  bssl::UniquePtr<X509> x509 =
      BuildSelfSignedCert([](X509 * /*cert*/, X509_NAME *name) {
        return X509_NAME_add_entry_by_NID(
            name, NID_commonName, MBSTRING_UTF8,
            reinterpret_cast<const unsigned char *>("line1\nline2\rline3"), -1,
            -1, 0);
      });
  ASSERT_TRUE(x509);
  ASSERT_TRUE(WriteCertToFile(x509.get(), in_path));

  args_list_t args = {"-in", in_path, "-noout", "-subject", "-out", out_path};
  ASSERT_EQ(kToolExitSuccess, X509Tool(args));

  std::string output = ReadFileToString(out_path);
  ASSERT_FALSE(output.empty());
  // Exactly one newline, and it is the final byte: the raw newline/CR bytes
  // must not have split "subject=" output across physical lines.
  EXPECT_EQ(output.size() - 1, output.find('\n'));
  // Nor may the raw bytes appear unescaped anywhere in the output.
  EXPECT_EQ(std::string::npos, output.find("line1\nline2"));
  EXPECT_EQ(std::string::npos, output.find("line2\rline3"));

  // The control bytes must instead show up hex-escaped
  // (ASN1_STRFLGS_ESC_CTRL: backslash + 2 hex digits).
  const char kBackslash = static_cast<char>(0x5C);
  std::string escaped_newline = std::string("line1") + kBackslash + "0Aline2";
  std::string escaped_cr = std::string("line2") + kBackslash + "0Dline3";
  EXPECT_NE(std::string::npos, output.find(escaped_newline));
  EXPECT_NE(std::string::npos, output.find(escaped_cr));
}
