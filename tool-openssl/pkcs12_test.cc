// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/asn1.h>
#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/pkcs8.h>
#include <openssl/stack.h>
#include <openssl/x509.h>
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>
#if !defined(OPENSSL_WINDOWS)
#include <fcntl.h>
#include <signal.h>
#include <unistd.h>
#endif
#include "internal.h"
#include "test_util.h"

namespace {

// Serializes a PKCS#12 blob containing |pkey| (may be null, for a
// certificate-only bundle) and |certs| (in order), protected by |password|.
bool BuildPKCS12(const char *password, EVP_PKEY *pkey,
                 const std::vector<X509 *> &certs,
                 std::vector<uint8_t> *out_der, int cert_nid = 0) {
  bssl::UniquePtr<STACK_OF(X509)> chain(sk_X509_new_null());
  if (!chain) {
    return false;
  }
  for (X509 *cert : certs) {
    if (!bssl::PushToStack(chain.get(), bssl::UpRef(cert))) {
      return false;
    }
  }

  bssl::UniquePtr<PKCS12> p12(PKCS12_create(password, nullptr /* name */, pkey,
                                            nullptr /* cert */, chain.get(), 0,
                                            cert_nid, 0, 0, 0));
  if (!p12) {
    return false;
  }

  uint8_t *der = nullptr;
  int len = i2d_PKCS12(p12.get(), &der);
  if (len <= 0) {
    return false;
  }
  bssl::UniquePtr<uint8_t> free_der(der);
  out_der->assign(der, der + len);
  return true;
}

bool WriteBytesToFile(const char *path, const std::vector<uint8_t> &bytes) {
  ScopedFILE f(fopen(path, "wb"));
  if (!f) {
    return false;
  }
  if (!bytes.empty() &&
      fwrite(bytes.data(), 1, bytes.size(), f.get()) != bytes.size()) {
    return false;
  }
  return true;
}

// Parses every PEM certificate present in |path|, in order. Comparison
// tests work at the certificate level rather than byte-for-byte because
// this tool omits the "Bag Attributes" comment lines other implementations
// print before each block.
std::vector<bssl::UniquePtr<X509>> ParseAllCertsFromPEMFile(
    const std::string &path) {
  std::vector<bssl::UniquePtr<X509>> result;
  bssl::UniquePtr<BIO> bio(BIO_new_file(path.c_str(), "rb"));
  if (!bio) {
    return result;
  }
  for (;;) {
    bssl::UniquePtr<X509> cert(
        PEM_read_bio_X509(bio.get(), nullptr, nullptr, nullptr));
    if (!cert) {
      ERR_clear_error();
      break;
    }
    result.push_back(std::move(cert));
  }
  return result;
}

}  // namespace

class PKCS12Test : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);

    CreateAndSignX509Certificate(cert_a, &key_a);
    ASSERT_TRUE(cert_a);
    ASSERT_TRUE(key_a);
    CreateAndSignX509Certificate(cert_b, nullptr);
    ASSERT_TRUE(cert_b);
    CreateAndSignX509Certificate(cert_c, nullptr);
    ASSERT_TRUE(cert_c);
  }

  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(out_path);
  }

  // Builds a PKCS#12 containing |key_a| and, in order, cert_a, cert_b,
  // cert_c, then writes it to |in_path|.
  bool WriteKeyAndChainBundle(const char *password) {
    std::vector<uint8_t> der;
    return BuildPKCS12(password, key_a.get(),
                       {cert_a.get(), cert_b.get(), cert_c.get()}, &der) &&
           WriteBytesToFile(in_path, der);
  }

  // Builds a certificate-only (no key) PKCS#12 containing, in order,
  // cert_b, cert_c, then writes it to |in_path|.
  bool WriteCertOnlyBundle(const char *password) {
    std::vector<uint8_t> der;
    return BuildPKCS12(password, nullptr, {cert_b.get(), cert_c.get()}, &der) &&
           WriteBytesToFile(in_path, der);
  }

  char in_path[PATH_MAX];
  char out_path[PATH_MAX];
  bssl::UniquePtr<X509> cert_a, cert_b, cert_c;
  bssl::UniquePtr<EVP_PKEY> key_a;
};

// -nokeys extracts every certificate in the file, in the order they appear,
// and never writes any private key material even though the input has one.
TEST_F(PKCS12Test, NoKeysExtractsAllCertsInOrder) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));

  args_list_t args = {
      "-nokeys", "-in",   in_path, "-password", "pass:testpassword12",
      "-out",    out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));

  std::string output = ReadFileToString(out_path);
  EXPECT_EQ(output.find("PRIVATE KEY"), std::string::npos);

  auto certs = ParseAllCertsFromPEMFile(out_path);
  ASSERT_EQ(certs.size(), 3u);
  EXPECT_EQ(0, X509_cmp(certs[0].get(), cert_a.get()));
  EXPECT_EQ(0, X509_cmp(certs[1].get(), cert_b.get()));
  EXPECT_EQ(0, X509_cmp(certs[2].get(), cert_c.get()));
}

// A certificate-only bundle (no key at all) is extracted the same way.
TEST_F(PKCS12Test, CertOnlyBundleWithNokeys) {
  ASSERT_TRUE(WriteCertOnlyBundle("certsonly"));

  args_list_t args = {"-nokeys",        "-in",  in_path, "-password",
                      "pass:certsonly", "-out", out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));

  auto certs = ParseAllCertsFromPEMFile(out_path);
  ASSERT_EQ(certs.size(), 2u);
  EXPECT_EQ(0, X509_cmp(certs[0].get(), cert_b.get()));
  EXPECT_EQ(0, X509_cmp(certs[1].get(), cert_c.get()));
}

// A certificate-only bundle has no key to reject, so it succeeds even
// without -nokeys.
TEST_F(PKCS12Test, CertOnlyBundleWithoutNokeysSucceeds) {
  ASSERT_TRUE(WriteCertOnlyBundle("certsonly"));

  args_list_t args = {"-in",  in_path, "-password", "pass:certsonly",
                      "-out", out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));

  std::string output = ReadFileToString(out_path);
  EXPECT_EQ(output.find("PRIVATE KEY"), std::string::npos);
  EXPECT_EQ(ParseAllCertsFromPEMFile(out_path).size(), 2u);
}

// A wrong password is rejected, and -out is left untouched.
TEST_F(PKCS12Test, WrongPasswordFails) {
  ASSERT_TRUE(WriteKeyAndChainBundle("rightpassword"));
  ASSERT_TRUE(WriteBytesToFile(out_path, {'k', 'e', 'e', 'p'}));

  args_list_t args = {
      "-nokeys", "-in",   in_path, "-password", "pass:wrongpassword",
      "-out",    out_path};
  EXPECT_EQ(kToolExitFailure, pkcs12Tool(args));
  EXPECT_EQ(ReadFileToString(out_path), "keep");
}

// An explicitly empty password (-password pass:) is handled correctly.
TEST_F(PKCS12Test, EmptyPasswordExplicit) {
  ASSERT_TRUE(WriteKeyAndChainBundle(""));

  args_list_t args = {"-nokeys", "-in",  in_path, "-password",
                      "pass:",   "-out", out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));
  EXPECT_EQ(ParseAllCertsFromPEMFile(out_path).size(), 3u);
}

// The same, via -passin instead of -password.
TEST_F(PKCS12Test, EmptyPasswordExplicitViaPassin) {
  ASSERT_TRUE(WriteKeyAndChainBundle(""));

  args_list_t args = {"-nokeys", "-in",  in_path, "-passin",
                      "pass:",   "-out", out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));
  EXPECT_EQ(ParseAllCertsFromPEMFile(out_path).size(), 3u);
}

// If neither -passin nor -password is given at all, an empty password is
// assumed (this tool never prompts interactively).
TEST_F(PKCS12Test, EmptyPasswordDefaultedWhenOmitted) {
  ASSERT_TRUE(WriteKeyAndChainBundle(""));

  args_list_t args = {"-nokeys", "-in", in_path, "-out", out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));
  EXPECT_EQ(ParseAllCertsFromPEMFile(out_path).size(), 3u);
}

// Malformed (non-PKCS#12) input is rejected cleanly.
TEST_F(PKCS12Test, MalformedInputFails) {
  std::vector<uint8_t> garbage = {0x00, 0x01, 0x02, 'n',  'o', 't',  ' ',
                                  'a',  ' ',  'p',  '1',  '2', 0xff, 0xfe,
                                  0x10, 0x30, 0x7f, 0x01, 0x02};
  ASSERT_TRUE(WriteBytesToFile(in_path, garbage));
  ASSERT_TRUE(WriteBytesToFile(out_path, {'k', 'e', 'e', 'p'}));

  args_list_t args = {"-nokeys", "-in",  in_path, "-password",
                      "pass:x",  "-out", out_path};
  EXPECT_EQ(kToolExitFailure, pkcs12Tool(args));
  EXPECT_EQ(ReadFileToString(out_path), "keep");
}

// An empty input file is rejected rather than treated as a trivial success.
TEST_F(PKCS12Test, EmptyInputFileFails) {
  args_list_t args = {"-nokeys", "-in",  in_path, "-password",
                      "pass:x",  "-out", out_path};
  EXPECT_EQ(kToolExitFailure, pkcs12Tool(args));
}

// A missing input file is rejected.
TEST_F(PKCS12Test, MissingInputFileFails) {
  args_list_t args = {"-nokeys",   "-in",    "/nonexistent/path/to/file.p12",
                      "-password", "pass:x", "-out",
                      out_path};
  EXPECT_EQ(kToolExitFailure, pkcs12Tool(args));
}

// -noout suppresses all output, including any private key, without
// requiring -passout. A successful -noout still opens and truncates -out.
TEST_F(PKCS12Test, NoOutSuppressesAllOutput) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));
  ASSERT_TRUE(WriteBytesToFile(out_path, {'o', 'l', 'd'}));

  args_list_t args = {
      "-noout", "-in",   in_path, "-password", "pass:testpassword12",
      "-out",   out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));
  EXPECT_TRUE(ReadFileToString(out_path).empty());
}

TEST_F(PKCS12Test, NoOutStillRejectsWrongPassword) {
  ASSERT_TRUE(WriteKeyAndChainBundle("rightpassword"));
  ASSERT_TRUE(WriteBytesToFile(out_path, {'k', 'e', 'e', 'p'}));
  EXPECT_EQ(kToolExitFailure,
            pkcs12Tool({"-noout", "-in", in_path, "-password",
                        "pass:wrongpassword", "-out", out_path}));
  EXPECT_EQ(ReadFileToString(out_path), "keep");
}

// A private key present in the input, without -nokeys, -nodes or
// -passout, is rejected outright: this tool never prompts interactively.
TEST_F(PKCS12Test, KeyExportRequiresPassoutOrNodesOrNokeys) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));
  ASSERT_TRUE(WriteBytesToFile(out_path, {'k', 'e', 'e', 'p'}));

  args_list_t args = {"-in",  in_path, "-password", "pass:testpassword12",
                      "-out", out_path};
  testing::internal::CaptureStderr();
  int result = pkcs12Tool(args);
  std::string stderr_output = testing::internal::GetCapturedStderr();

  EXPECT_EQ(kToolExitFailure, result);
  EXPECT_NE(stderr_output.find("-nokeys"), std::string::npos) << stderr_output;
  EXPECT_NE(stderr_output.find("-passout"), std::string::npos) << stderr_output;
  EXPECT_NE(stderr_output.find("-nodes"), std::string::npos) << stderr_output;
  EXPECT_EQ(ReadFileToString(out_path), "keep");
}

// With -passout, the private key is PEM-encrypted (AES-256-CBC), never
// plaintext, round-trips to the original key, and follows the certificates.
TEST_F(PKCS12Test, KeyExportWithPassoutProducesEncryptedKeyAfterCerts) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));

  args_list_t args = {"-in",       in_path,
                      "-password", "pass:testpassword12",
                      "-passout",  "pass:exportpw123",
                      "-out",      out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));

  std::string output = ReadFileToString(out_path);
  size_t key_pos = output.find("-----BEGIN ENCRYPTED PRIVATE KEY-----");
  size_t last_cert_pos = output.rfind("-----BEGIN CERTIFICATE-----");
  ASSERT_NE(key_pos, std::string::npos);
  ASSERT_NE(last_cert_pos, std::string::npos);
  EXPECT_LT(last_cert_pos, key_pos);
  // Must not also contain an unencrypted key block.
  EXPECT_EQ(output.find("-----BEGIN PRIVATE KEY-----"), std::string::npos);

  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "rb"));
  ASSERT_TRUE(bio);
  // Certificates come first; skip past them to reach the key.
  for (size_t i = 0; i < 3; i++) {
    bssl::UniquePtr<X509> cert(
        PEM_read_bio_X509(bio.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(cert);
  }
  bssl::UniquePtr<EVP_PKEY> decrypted(PEM_read_bio_PrivateKey(
      bio.get(), nullptr, nullptr, const_cast<char *>("exportpw123")));
  ASSERT_TRUE(decrypted);
  EXPECT_EQ(1, EVP_PKEY_cmp(decrypted.get(), key_a.get()));

  EXPECT_EQ(ParseAllCertsFromPEMFile(out_path).size(), 3u);
}

// -nodes writes the private key unencrypted (PKCS#8 "PRIVATE KEY") and
// does not require -passout.
TEST_F(PKCS12Test, NodesWritesUnencryptedKey) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));

  args_list_t args = {
      "-nodes", "-in",   in_path, "-password", "pass:testpassword12",
      "-out",   out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));

  std::string output = ReadFileToString(out_path);
  EXPECT_NE(output.find("-----BEGIN PRIVATE KEY-----"), std::string::npos);
  EXPECT_EQ(output.find("ENCRYPTED"), std::string::npos);

  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "rb"));
  ASSERT_TRUE(bio);
  for (size_t i = 0; i < 3; i++) {
    bssl::UniquePtr<X509> cert(
        PEM_read_bio_X509(bio.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(cert);
  }
  bssl::UniquePtr<EVP_PKEY> parsed(
      PEM_read_bio_PrivateKey(bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(parsed);
  EXPECT_EQ(1, EVP_PKEY_cmp(parsed.get(), key_a.get()));
}

// -nodes overrides -passout.
TEST_F(PKCS12Test, NodesOverridesPassout) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));

  args_list_t args = {
      "-nodes",   "-in",          in_path, "-password", "pass:testpassword12",
      "-passout", "pass:ignored", "-out",  out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));

  std::string output = ReadFileToString(out_path);
  EXPECT_NE(output.find("-----BEGIN PRIVATE KEY-----"), std::string::npos);
  EXPECT_EQ(output.find("ENCRYPTED"), std::string::npos);
}

// -nocerts emits only the key.
TEST_F(PKCS12Test, NocertsEmitsOnlyKey) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));

  args_list_t args = {"-nocerts", "-nodes",    "-in",
                      in_path,    "-password", "pass:testpassword12",
                      "-out",     out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));

  std::string output = ReadFileToString(out_path);
  EXPECT_EQ(output.find("CERTIFICATE"), std::string::npos);
  EXPECT_NE(output.find("-----BEGIN PRIVATE KEY-----"), std::string::npos);
  EXPECT_TRUE(ParseAllCertsFromPEMFile(out_path).empty());
}

// -nocerts -nokeys together verify the bundle and write nothing. A
// successful run still opens and truncates -out, as -noout does.
TEST_F(PKCS12Test, NocertsAndNokeysWriteNothing) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));
  ASSERT_TRUE(WriteBytesToFile(out_path, {'o', 'l', 'd'}));

  args_list_t args = {"-nocerts", "-nokeys",   "-in",
                      in_path,    "-password", "pass:testpassword12",
                      "-out",     out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));
  EXPECT_TRUE(ReadFileToString(out_path).empty());
}

// -nocerts does not relax the -passout requirement for a key.
TEST_F(PKCS12Test, NocertsStillRequiresPassoutForKey) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));
  ASSERT_TRUE(WriteBytesToFile(out_path, {'k', 'e', 'e', 'p'}));

  args_list_t args = {
      "-nocerts", "-in",   in_path, "-password", "pass:testpassword12",
      "-out",     out_path};
  EXPECT_EQ(kToolExitFailure, pkcs12Tool(args));
  EXPECT_EQ(ReadFileToString(out_path), "keep");
}

// A wrong password produces a one-line diagnostic with no error-queue dump
// (ERR_LIB_PKCS12 has no registered strings), and leaves the queue empty.
TEST_F(PKCS12Test, WrongPasswordReportsMacVerifyError) {
  ASSERT_TRUE(WriteKeyAndChainBundle("rightpassword"));

  args_list_t args = {
      "-nokeys", "-in",   in_path, "-password", "pass:wrongpassword",
      "-out",    out_path};
  testing::internal::CaptureStderr();
  int result = pkcs12Tool(args);
  std::string stderr_output = testing::internal::GetCapturedStderr();

  EXPECT_EQ(kToolExitFailure, result);
  EXPECT_EQ(stderr_output, "Mac verify error: invalid password?\n");
  EXPECT_EQ(0u, ERR_peek_error());
}

// Malformed input reports a generic parse error, not the MAC diagnostic.
TEST_F(PKCS12Test, MalformedInputDoesNotReportMacError) {
  ASSERT_TRUE(WriteBytesToFile(in_path, {0x30, 0x03, 0x02, 0x01, 0x03}));

  args_list_t args = {"-nokeys", "-in",  in_path, "-password",
                      "pass:x",  "-out", out_path};
  testing::internal::CaptureStderr();
  int result = pkcs12Tool(args);
  std::string stderr_output = testing::internal::GetCapturedStderr();

  EXPECT_EQ(kToolExitFailure, result);
  EXPECT_EQ(stderr_output.find("Mac verify error"), std::string::npos)
      << stderr_output;
  EXPECT_NE(stderr_output.find("BAD_PKCS12_DATA"), std::string::npos)
      << stderr_output;
}

// An explicit "-passout pass:" is a deliberate empty password, distinct from
// omitting -passout, and produces an encrypted key rather than a rejection.
TEST_F(PKCS12Test, PassoutExplicitEmptyPasswordEncryptsKey) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));

  args_list_t args = {"-in",      in_path, "-password", "pass:testpassword12",
                      "-passout", "pass:", "-out",      out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));

  std::string output = ReadFileToString(out_path);
  EXPECT_NE(output.find("-----BEGIN ENCRYPTED PRIVATE KEY-----"),
            std::string::npos);

  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "rb"));
  ASSERT_TRUE(bio);
  bssl::UniquePtr<EVP_PKEY> decrypted(PEM_read_bio_PrivateKey(
      bio.get(), nullptr, nullptr, const_cast<char *>("")));
  ASSERT_TRUE(decrypted);
  EXPECT_EQ(1, EVP_PKEY_cmp(decrypted.get(), key_a.get()));
}

// -nokeys always wins: even if -passout is also given, no key is emitted.
TEST_F(PKCS12Test, NoKeysIgnoresPassout) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));

  args_list_t args = {"-nokeys",
                      "-in",
                      in_path,
                      "-password",
                      "pass:testpassword12",
                      "-passout",
                      "pass:exportpw123",
                      "-out",
                      out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));

  std::string output = ReadFileToString(out_path);
  EXPECT_EQ(output.find("PRIVATE KEY"), std::string::npos);
}

// -password overrides -passin when both are given, regardless of order.
TEST_F(PKCS12Test, PasswordOverridesPassinWhenBothGiven) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));

  // A wrong -passin is masked by a correct -password.
  args_list_t args_right_password = {"-nokeys",
                                     "-in",
                                     in_path,
                                     "-passin",
                                     "pass:wrongpassword",
                                     "-password",
                                     "pass:testpassword12",
                                     "-out",
                                     out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args_right_password));

  // A correct -passin is overridden by a wrong -password.
  args_list_t args_wrong_password = {"-nokeys",
                                     "-in",
                                     in_path,
                                     "-passin",
                                     "pass:testpassword12",
                                     "-password",
                                     "pass:wrongpassword",
                                     "-out",
                                     out_path};
  EXPECT_EQ(kToolExitFailure, pkcs12Tool(args_wrong_password));
}

// -passin alone still works when -password is absent.
TEST_F(PKCS12Test, PassinAloneWorksWhenPasswordAbsent) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));

  args_list_t args = {
      "-nokeys", "-in",   in_path, "-passin", "pass:testpassword12",
      "-out",    out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));
}

// -password acts as a -passin alias when -passin is absent.
TEST_F(PKCS12Test, PasswordAliasWorksWhenPassinAbsent) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));

  args_list_t args = {
      "-nokeys", "-in",   in_path, "-password", "pass:testpassword12",
      "-out",    out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));
}

TEST_F(PKCS12Test, PassinBareEmptyArgumentFails) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));
  EXPECT_EQ(kToolExitFailure, pkcs12Tool({"-nokeys", "-in", in_path, "-passin",
                                          "", "-out", out_path}));
}

TEST_F(PKCS12Test, PasswordOverridesInvalidPassinSource) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));
  for (const char *ignored : {"", "not-a-password-source"}) {
    EXPECT_EQ(kToolExitSuccess,
              pkcs12Tool({"-nokeys", "-in", in_path, "-password",
                          "pass:testpassword12", "-passin", ignored, "-out",
                          out_path}));
    EXPECT_EQ(ParseAllCertsFromPEMFile(out_path).size(), 3u);
  }
}

TEST_F(PKCS12Test, EmptyPathsAreNotStandardStreams) {
  EXPECT_EQ(kToolExitFailure,
            pkcs12Tool({"-nokeys", "-in", "", "-out", out_path}));
  EXPECT_EQ(kToolExitFailure,
            pkcs12Tool({"-nokeys", "-in", in_path, "-out", ""}));
}

TEST_F(PKCS12Test, PasswordBareEmptyArgumentFails) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));

  args_list_t args = {"-nokeys", "-in",  in_path, "-password",
                      "",        "-out", out_path};
  EXPECT_EQ(kToolExitFailure, pkcs12Tool(args));
}

TEST_F(PKCS12Test, PassoutBareEmptyArgumentFails) {
  ASSERT_TRUE(WriteKeyAndChainBundle("testpassword12"));

  args_list_t args = {"-in",      in_path, "-password", "pass:testpassword12",
                      "-passout", "",      "-out",      out_path};
  EXPECT_EQ(kToolExitFailure, pkcs12Tool(args));
}

// Options this scoped tool does not implement (notably -export) must fail
// rather than silently no-op.
TEST_F(PKCS12Test, UnsupportedFlagsFail) {
  ASSERT_TRUE(WriteCertOnlyBundle("certsonly"));

  std::vector<std::string> unsupported = {"-export",  "-info",    "-clcerts",
                                          "-cacerts", "-chain",   "-descert",
                                          "-twopass", "-nomacver"};
  for (const auto &flag : unsupported) {
    args_list_t args = {flag,   "-in",   in_path, "-password", "pass:certsonly",
                        "-out", out_path};
    EXPECT_EQ(kToolExitFailure, pkcs12Tool(args))
        << "Expected failure for flag: " << flag;
  }
}

// OpenSSL 3 scripts pass -legacy to load RC2/3DES; accept it as a no-op.
TEST_F(PKCS12Test, LegacyIsAcceptedNoOp) {
  ASSERT_TRUE(WriteCertOnlyBundle("certsonly"));

  args_list_t args = {"-legacy",   "-nokeys",        "-in",  in_path,
                      "-password", "pass:certsonly", "-out", out_path};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));
  EXPECT_EQ(ParseAllCertsFromPEMFile(out_path).size(), 2u);
}

// Positional arguments are not accepted.
TEST_F(PKCS12Test, PositionalArgumentFails) {
  ASSERT_TRUE(WriteCertOnlyBundle("certsonly"));

  args_list_t args = {"-nokeys",        "-in",         in_path, "-password",
                      "pass:certsonly", "somefile.p12"};
  EXPECT_EQ(kToolExitFailure, pkcs12Tool(args));
}

// -help succeeds and does not attempt to process other options.
TEST_F(PKCS12Test, HelpSucceeds) {
  args_list_t args = {"-help"};
  EXPECT_EQ(kToolExitSuccess, pkcs12Tool(args));
}

// Password extraction must not translate or truncate binary data which follows
// the password lines on stdin, even on Windows.
TEST_F(PKCS12Test, ReadsPasswordAndBundleFromStdin) {
  // Leave the certificate bag unencrypted so its serial number guarantees the
  // DER contains Ctrl-Z and CRLF, rather than relying on random ciphertext.
  ASSERT_TRUE(ASN1_INTEGER_set(X509_get_serialNumber(cert_a.get()), 0x1a0d0a));
  ASSERT_GT(X509_sign(cert_a.get(), key_a.get(), EVP_sha256()), 0);
  std::vector<uint8_t> der;
  ASSERT_TRUE(BuildPKCS12("certsonly", nullptr, {cert_a.get()}, &der, -1));
  const uint8_t marker[] = {0x1a, '\r', '\n'};
  ASSERT_NE(
      std::search(der.begin(), der.end(), marker, marker + sizeof(marker)),
      der.end());

  for (const char *line_ending : {"\n", "\r\n"}) {
    SCOPED_TRACE(strlen(line_ending));
    for (bool two_passwords : {false, true}) {
      SCOPED_TRACE(two_passwords);
      std::string prefix = std::string("certsonly") + line_ending;
      args_list_t args = {"-nokeys", "-passin", "stdin", "-out", out_path};
      if (two_passwords) {
        prefix += std::string("unused") + line_ending;
        args.insert(args.end(), {"-passout", "stdin"});
      }
      std::vector<uint8_t> input(prefix.begin(), prefix.end());
      input.insert(input.end(), der.begin(), der.end());
      ASSERT_TRUE(WriteBytesToFile(in_path, input));
      ScopedFILE input_file(fopen(in_path, "rb"));
      ASSERT_TRUE(input_file);

#if defined(OPENSSL_WINDOWS)
      ScopedFD saved_stdin(_dup(_fileno(stdin)));
      ASSERT_GE(saved_stdin.get(), 0);
      ASSERT_EQ(_dup2(_fileno(input_file.get()), _fileno(stdin)), 0);
#else
      ScopedFD saved_stdin(dup(STDIN_FILENO));
      ASSERT_GE(saved_stdin.get(), 0);
      ASSERT_EQ(dup2(fileno(input_file.get()), STDIN_FILENO), STDIN_FILENO);
#endif
      clearerr(stdin);
      int result = pkcs12Tool(args);
      // Restore stdin before any assertions can abort the test.
#if defined(OPENSSL_WINDOWS)
      int restore_result = _dup2(saved_stdin.get(), _fileno(stdin));
#else
      int restore_result = dup2(saved_stdin.get(), STDIN_FILENO);
#endif
      clearerr(stdin);
      ASSERT_GE(restore_result, 0);
      EXPECT_EQ(kToolExitSuccess, result);
      auto certs = ParseAllCertsFromPEMFile(out_path);
      ASSERT_EQ(certs.size(), 1u);
      EXPECT_EQ(X509_cmp(certs[0].get(), cert_a.get()), 0);
    }
  }
}

#if !defined(OPENSSL_WINDOWS)
// -in may be omitted to read the PKCS#12 data from stdin.
TEST_F(PKCS12Test, ReadsFromStdin) {
  ASSERT_TRUE(WriteCertOnlyBundle("certsonly"));

  std::vector<uint8_t> der;
  {
    ScopedFILE f(fopen(in_path, "rb"));
    ASSERT_TRUE(f);
    ASSERT_TRUE(ReadAll(&der, f.get()));
  }
  ASSERT_FALSE(der.empty());

  int pipefd[2];
  ASSERT_EQ(pipe(pipefd), 0);
  // Write before swapping fd 0 so a failed ASSERT here cannot leave the
  // process stdin pointed at this pipe.
  ASSERT_EQ(write(pipefd[1], der.data(), der.size()),
            static_cast<ssize_t>(der.size()));
  close(pipefd[1]);

  int old_stdin = dup(STDIN_FILENO);
  ASSERT_GE(old_stdin, 0);
  ASSERT_GE(dup2(pipefd[0], STDIN_FILENO), 0);
  close(pipefd[0]);
  // |stdin|'s EOF/error indicators survive the dup2 above; clear them so a
  // previous test having drained the original stdin does not make this read
  // report EOF immediately.
  clearerr(stdin);

  args_list_t args = {"-nokeys", "-password", "pass:certsonly", "-out",
                      out_path};
  int result = pkcs12Tool(args);

  dup2(old_stdin, STDIN_FILENO);
  close(old_stdin);
  clearerr(stdin);

  EXPECT_EQ(kToolExitSuccess, result);
  EXPECT_EQ(ParseAllCertsFromPEMFile(out_path).size(), 2u);
}

// -out may be omitted to write PEM output to stdout.
TEST_F(PKCS12Test, WritesToStdout) {
  ASSERT_TRUE(WriteCertOnlyBundle("certsonly"));

  char redirect_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(redirect_path), 0u);
  int redirect_fd = open(redirect_path, O_WRONLY | O_TRUNC);
  ASSERT_GE(redirect_fd, 0);

  fflush(stdout);
  int old_stdout = dup(STDOUT_FILENO);
  ASSERT_GE(old_stdout, 0);
  ASSERT_GE(dup2(redirect_fd, STDOUT_FILENO), 0);
  close(redirect_fd);

  args_list_t args = {"-nokeys", "-in", in_path, "-password", "pass:certsonly"};
  int result = pkcs12Tool(args);
  fflush(stdout);

  dup2(old_stdout, STDOUT_FILENO);
  close(old_stdout);

  EXPECT_EQ(kToolExitSuccess, result);
  EXPECT_EQ(ParseAllCertsFromPEMFile(redirect_path).size(), 2u);
  RemoveFile(redirect_path);
}

// A write/flush failure on -out (here: a broken pipe on stdout) is
// reported as failure, not swallowed by an unchecked BIO_flush.
TEST_F(PKCS12Test, WriteFailureIsReported) {
  ASSERT_TRUE(WriteCertOnlyBundle("certsonly"));

  int pipefd[2];
  ASSERT_EQ(pipe(pipefd), 0);
  close(pipefd[0]);  // No reader: writes/flushes below fail with EPIPE.

  auto old_sigpipe = signal(SIGPIPE, SIG_IGN);
  fflush(stdout);
  int old_stdout = dup(STDOUT_FILENO);
  ASSERT_GE(old_stdout, 0);
  ASSERT_GE(dup2(pipefd[1], STDOUT_FILENO), 0);
  close(pipefd[1]);

  args_list_t args = {"-nokeys", "-in", in_path, "-password", "pass:certsonly"};
  int result = pkcs12Tool(args);

  dup2(old_stdout, STDOUT_FILENO);
  close(old_stdout);
  signal(SIGPIPE, old_sigpipe);
  // Clear the error indicator the failed writes left on |stdout|.
  clearerr(stdout);

  EXPECT_EQ(kToolExitFailure, result);
}
#endif  // !OPENSSL_WINDOWS

// Comparison tests cannot run without set up of environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.

class PKCS12ComparisonTest : public ::testing::Test {
 protected:
  void SetUp() override {
    // Skip gtests if env variables not set
    tool_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
    if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
      GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH "
                      "environment variables are not set";
    }

    ASSERT_GT(createTempFILEpath(key_path), 0u);
    ASSERT_GT(createTempFILEpath(cert_path), 0u);
    ASSERT_GT(createTempFILEpath(p12_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);

    CreateAndSignX509Certificate(cert, &key);
    ASSERT_TRUE(cert);
    ASSERT_TRUE(key);

    ScopedFILE key_file(fopen(key_path, "wb"));
    ASSERT_TRUE(key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(key_file.get(), key.get(), nullptr,
                                     nullptr, 0, nullptr, nullptr));
    key_file.reset();

    ScopedFILE cert_file(fopen(cert_path, "wb"));
    ASSERT_TRUE(cert_file);
    ASSERT_TRUE(PEM_write_X509(cert_file.get(), cert.get()));
    cert_file.reset();
  }

  void TearDown() override {
    if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
      RemoveFile(key_path);
      RemoveFile(cert_path);
      RemoveFile(p12_path);
      RemoveFile(out_path_tool);
      RemoveFile(out_path_openssl);
    }
  }

  char key_path[PATH_MAX];
  char cert_path[PATH_MAX];
  char p12_path[PATH_MAX];
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  bssl::UniquePtr<X509> cert;
  bssl::UniquePtr<EVP_PKEY> key;
  const char *tool_executable_path;
  const char *openssl_executable_path;
};

// Both tools extract the same certificate from a bundle produced by the
// reference tool's -export (which this tool does not implement). Outputs are
// compared as parsed X509 objects, not as text, since this tool omits the
// "Bag Attributes" comment lines.
TEST_F(PKCS12ComparisonTest, ImportMatchesOpenSSL) {
  std::string export_command = std::string(openssl_executable_path) +
                               " pkcs12 -export -inkey " + key_path + " -in " +
                               cert_path + " -passout pass:exportpw -out " +
                               p12_path;
  ASSERT_EQ(system(export_command.c_str()), 0)
      << "OpenSSL fixture export failed: " << export_command;

  std::string tool_command = std::string(tool_executable_path) +
                             " pkcs12 -nokeys -in " + p12_path +
                             " -password pass:exportpw -out " + out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " pkcs12 -nokeys -in " + p12_path +
      " -password pass:exportpw -out " + out_path_openssl;

  ASSERT_EQ(system(tool_command.c_str()), 0)
      << "AWS-LC tool command failed: " << tool_command;
  ASSERT_EQ(system(openssl_command.c_str()), 0)
      << "OpenSSL command failed: " << openssl_command;

  auto tool_certs = ParseAllCertsFromPEMFile(out_path_tool);
  auto openssl_certs = ParseAllCertsFromPEMFile(out_path_openssl);

  ASSERT_FALSE(tool_certs.empty());
  ASSERT_EQ(tool_certs.size(), openssl_certs.size());
  for (size_t i = 0; i < tool_certs.size(); i++) {
    EXPECT_EQ(0, X509_cmp(tool_certs[i].get(), openssl_certs[i].get()));
  }
}

// With -nodes, both tools emit the certificate(s) followed by the plaintext
// key, so the sequence of PEM block types must match and the key must
// round-trip.
TEST_F(PKCS12ComparisonTest, NodesImportMatchesOpenSSL) {
  std::string export_command = std::string(openssl_executable_path) +
                               " pkcs12 -export -inkey " + key_path + " -in " +
                               cert_path + " -passout pass:exportpw -out " +
                               p12_path;
  ASSERT_EQ(system(export_command.c_str()), 0)
      << "OpenSSL fixture export failed: " << export_command;

  std::string tool_command = std::string(tool_executable_path) +
                             " pkcs12 -nodes -in " + p12_path +
                             " -password pass:exportpw -out " + out_path_tool;
  std::string openssl_command =
      std::string(openssl_executable_path) + " pkcs12 -nodes -in " + p12_path +
      " -password pass:exportpw -out " + out_path_openssl;
  ASSERT_EQ(system(tool_command.c_str()), 0) << tool_command;
  ASSERT_EQ(system(openssl_command.c_str()), 0) << openssl_command;

  // Extract the ordered sequence of PEM block labels from each output.
  auto pem_labels = [](const std::string &path) {
    std::vector<std::string> labels;
    std::string text = ReadFileToString(path);
    const std::string begin = "-----BEGIN ";
    for (size_t pos = text.find(begin); pos != std::string::npos;
         pos = text.find(begin, pos + 1)) {
      size_t start = pos + begin.size();
      size_t end = text.find("-----", start);
      labels.push_back(text.substr(start, end - start));
    }
    return labels;
  };
  auto tool_labels = pem_labels(out_path_tool);
  auto openssl_labels = pem_labels(out_path_openssl);
  ASSERT_FALSE(tool_labels.empty());
  EXPECT_EQ(tool_labels, openssl_labels);

  // Certificates match, and the tool's key matches the original.
  auto tool_certs = ParseAllCertsFromPEMFile(out_path_tool);
  auto openssl_certs = ParseAllCertsFromPEMFile(out_path_openssl);
  ASSERT_EQ(tool_certs.size(), openssl_certs.size());
  for (size_t i = 0; i < tool_certs.size(); i++) {
    EXPECT_EQ(0, X509_cmp(tool_certs[i].get(), openssl_certs[i].get()));
  }

  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path_tool, "rb"));
  ASSERT_TRUE(bio);
  for (size_t i = 0; i < tool_certs.size(); i++) {
    bssl::UniquePtr<X509> skip(
        PEM_read_bio_X509(bio.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(skip);
  }
  bssl::UniquePtr<EVP_PKEY> tool_key(
      PEM_read_bio_PrivateKey(bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(tool_key);
  EXPECT_EQ(1, EVP_PKEY_cmp(tool_key.get(), key.get()));
}
