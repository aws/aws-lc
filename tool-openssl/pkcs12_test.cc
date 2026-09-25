// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/asn1.h>
#include <openssl/bio.h>
#include <openssl/bytestring.h>
#include <openssl/ec_key.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/nid.h>
#include <openssl/pem.h>
#include <openssl/pkcs8.h>
#include <openssl/stack.h>
#include <openssl/x509.h>
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cstring>
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

// -export tests. AWS-LC exposes no accessor for embedded PBE/iteration
// counts, so ParseExportedAlgorithms walks the DER directly with CBS -- a
// minimal, test-only walk of the shapes PKCS12_create produces, not a
// general parser.

namespace {

const uint8_t kPbeSha1Rc2_40Oid[] = {0x2a, 0x86, 0x48, 0x86, 0xf7,
                                     0x0d, 0x01, 0x0c, 0x01, 0x06};
const uint8_t kPbeSha1_3DesOid[] = {0x2a, 0x86, 0x48, 0x86, 0xf7,
                                    0x0d, 0x01, 0x0c, 0x01, 0x03};
const uint8_t kPkcs7DataOid[] = {0x2a, 0x86, 0x48, 0x86, 0xf7,
                                 0x0d, 0x01, 0x07, 0x01};
const uint8_t kPkcs7EncryptedDataOid[] = {0x2a, 0x86, 0x48, 0x86, 0xf7,
                                          0x0d, 0x01, 0x07, 0x06};
const uint8_t kKeyBagOid[] = {0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d,
                              0x01, 0x0c, 0x0a, 0x01, 0x01};
const uint8_t kPkcs8ShroudedKeyBagOid[] = {0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d,
                                           0x01, 0x0c, 0x0a, 0x01, 0x02};
const uint8_t kCertBagOid[] = {0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d,
                               0x01, 0x0c, 0x0a, 0x01, 0x03};
const uint8_t kSha1Oid[] = {0x2b, 0x0e, 0x03, 0x02, 0x1a};

template <size_t N>
std::vector<uint8_t> OidBytes(const uint8_t (&oid)[N]) {
  return std::vector<uint8_t>(oid, oid + N);
}

std::vector<uint8_t> CBSToVector(const CBS *cbs) {
  return std::vector<uint8_t>(CBS_data(cbs), CBS_data(cbs) + CBS_len(cbs));
}

// Reads the PBEParameter { salt OCTET STRING, iterations INTEGER } that
// follows a PBE OID inside an AlgorithmIdentifier.
bool ReadPbeIterations(CBS *algorithm_identifier_tail,
                       uint64_t *out_iterations) {
  CBS pbe_param, salt;
  return CBS_get_asn1(algorithm_identifier_tail, &pbe_param,
                      CBS_ASN1_SEQUENCE) &&
         CBS_get_asn1(&pbe_param, &salt, CBS_ASN1_OCTETSTRING) &&
         CBS_get_asn1_uint64(&pbe_param, out_iterations);
}

struct Pkcs12AlgorithmInfo {
  bool cert_present = false;
  bool cert_encrypted = false;
  std::vector<uint8_t> cert_pbe_oid;
  uint64_t cert_iterations = 0;

  bool key_present = false;
  bool key_encrypted = false;
  std::vector<uint8_t> key_pbe_oid;
  uint64_t key_iterations = 0;

  bool mac_present = false;
  std::vector<uint8_t> mac_digest_oid;
  uint64_t mac_iterations = 0;
};

// Walks the DER structure PKCS12_create produces (crypto/pkcs8/pkcs8_x509.c)
// to recover which PBE algorithms and iteration counts were actually used.
bool ParseExportedAlgorithms(const std::vector<uint8_t> &der,
                             Pkcs12AlgorithmInfo *out) {
  CBS cbs, pfx;
  CBS_init(&cbs, der.data(), der.size());
  uint64_t version = 0;
  CBS auth_safe;
  if (!CBS_get_asn1(&cbs, &pfx, CBS_ASN1_SEQUENCE) ||
      !CBS_get_asn1_uint64(&pfx, &version) ||
      !CBS_get_asn1(&pfx, &auth_safe, CBS_ASN1_SEQUENCE)) {
    return false;
  }

  // auth_safe: ContentInfo { OID(data), [0]{ OCTET STRING { SEQUENCE OF
  // ContentInfo } } }
  CBS auth_safe_oid, auth_safe_wrapper, auth_safe_octets, content_infos;
  if (!CBS_get_asn1(&auth_safe, &auth_safe_oid, CBS_ASN1_OBJECT) ||
      !CBS_get_asn1(&auth_safe, &auth_safe_wrapper,
                    CBS_ASN1_CONTEXT_SPECIFIC | CBS_ASN1_CONSTRUCTED | 0) ||
      !CBS_get_asn1(&auth_safe_wrapper, &auth_safe_octets,
                    CBS_ASN1_OCTETSTRING) ||
      !CBS_get_asn1(&auth_safe_octets, &content_infos, CBS_ASN1_SEQUENCE)) {
    return false;
  }

  while (CBS_len(&content_infos) > 0) {
    CBS ci, ci_oid, ci_wrapper;
    if (!CBS_get_asn1(&content_infos, &ci, CBS_ASN1_SEQUENCE) ||
        !CBS_get_asn1(&ci, &ci_oid, CBS_ASN1_OBJECT) ||
        !CBS_get_asn1(&ci, &ci_wrapper,
                      CBS_ASN1_CONTEXT_SPECIFIC | CBS_ASN1_CONSTRUCTED | 0)) {
      return false;
    }

    if (CBS_mem_equal(&ci_oid, kPkcs7EncryptedDataOid,
                      sizeof(kPkcs7EncryptedDataOid))) {
      // Encrypted certs: EncryptedData { version, EncryptedContentInfo {
      // OID(data), contentEncryptionAlgorithm, [0] IMPLICIT OCTET STRING } }
      CBS encrypted_data, eci, inner_oid, algorithm, pbe_oid;
      uint64_t encrypted_data_version = 0;
      if (!CBS_get_asn1(&ci_wrapper, &encrypted_data, CBS_ASN1_SEQUENCE) ||
          !CBS_get_asn1_uint64(&encrypted_data, &encrypted_data_version) ||
          !CBS_get_asn1(&encrypted_data, &eci, CBS_ASN1_SEQUENCE) ||
          !CBS_get_asn1(&eci, &inner_oid, CBS_ASN1_OBJECT) ||
          !CBS_get_asn1(&eci, &algorithm, CBS_ASN1_SEQUENCE) ||
          !CBS_get_asn1(&algorithm, &pbe_oid, CBS_ASN1_OBJECT) ||
          !ReadPbeIterations(&algorithm, &out->cert_iterations)) {
        return false;
      }
      out->cert_present = true;
      out->cert_encrypted = true;
      out->cert_pbe_oid = CBSToVector(&pbe_oid);
      continue;
    }

    if (!CBS_mem_equal(&ci_oid, kPkcs7DataOid, sizeof(kPkcs7DataOid))) {
      continue;  // Not a shape this tool's -export can produce; ignore.
    }

    // A plain "data" ContentInfo: either unencrypted CertBag(s) or the
    // key's SafeContents (one KeyBag or PKCS8ShroudedKeyBag). Both share
    // this shape, so classify by walking the bags and inspecting each
    // bag's own OID.
    CBS octets, safe_contents;
    if (!CBS_get_asn1(&ci_wrapper, &octets, CBS_ASN1_OCTETSTRING) ||
        !CBS_get_asn1(&octets, &safe_contents, CBS_ASN1_SEQUENCE)) {
      return false;
    }
    while (CBS_len(&safe_contents) > 0) {
      CBS bag, bag_oid, bag_value;
      if (!CBS_get_asn1(&safe_contents, &bag, CBS_ASN1_SEQUENCE) ||
          !CBS_get_asn1(&bag, &bag_oid, CBS_ASN1_OBJECT) ||
          !CBS_get_asn1(&bag, &bag_value,
                        CBS_ASN1_CONTEXT_SPECIFIC | CBS_ASN1_CONSTRUCTED | 0)) {
        return false;
      }
      if (CBS_mem_equal(&bag_oid, kKeyBagOid, sizeof(kKeyBagOid))) {
        out->key_present = true;
        out->key_encrypted = false;
      } else if (CBS_mem_equal(&bag_oid, kPkcs8ShroudedKeyBagOid,
                               sizeof(kPkcs8ShroudedKeyBagOid))) {
        CBS epki, algorithm, pbe_oid;
        if (!CBS_get_asn1(&bag_value, &epki, CBS_ASN1_SEQUENCE) ||
            !CBS_get_asn1(&epki, &algorithm, CBS_ASN1_SEQUENCE) ||
            !CBS_get_asn1(&algorithm, &pbe_oid, CBS_ASN1_OBJECT) ||
            !ReadPbeIterations(&algorithm, &out->key_iterations)) {
          return false;
        }
        out->key_present = true;
        out->key_encrypted = true;
        out->key_pbe_oid = CBSToVector(&pbe_oid);
      } else if (CBS_mem_equal(&bag_oid, kCertBagOid, sizeof(kCertBagOid))) {
        out->cert_present = true;
        out->cert_encrypted = false;
      }
      // Else: a bag type this tool's -export never produces; ignore.
    }
  }

  if (CBS_len(&pfx) != 0) {
    CBS mac_data, digest_info, mac_salt;
    if (!CBS_get_asn1(&pfx, &mac_data, CBS_ASN1_SEQUENCE) ||
        !CBS_get_asn1(&mac_data, &digest_info, CBS_ASN1_SEQUENCE) ||
        !CBS_get_asn1(&mac_data, &mac_salt, CBS_ASN1_OCTETSTRING)) {
      return false;
    }
    CBS mac_alg, mac_oid;
    if (!CBS_get_asn1(&digest_info, &mac_alg, CBS_ASN1_SEQUENCE) ||
        !CBS_get_asn1(&mac_alg, &mac_oid, CBS_ASN1_OBJECT)) {
      return false;
    }
    out->mac_present = true;
    out->mac_digest_oid = CBSToVector(&mac_oid);
    if (CBS_len(&mac_data) != 0) {
      if (!CBS_get_asn1_uint64(&mac_data, &out->mac_iterations)) {
        return false;
      }
    } else {
      out->mac_iterations = 1;  // ASN.1 DEFAULT when omitted.
    }
  }
  return true;
}

// EVP_PKEY_cmp only compares public key material; marshal both keys to
// PKCS8 DER and compare bytes so a mismatched private component is caught.
bool PrivateKeysEqual(EVP_PKEY *a, EVP_PKEY *b) {
  if (!a || !b) {
    return false;
  }
  bssl::ScopedCBB cbb_a, cbb_b;
  uint8_t *der_a = nullptr, *der_b = nullptr;
  size_t len_a = 0, len_b = 0;
  if (!CBB_init(cbb_a.get(), 0) || !EVP_marshal_private_key(cbb_a.get(), a) ||
      !CBB_finish(cbb_a.get(), &der_a, &len_a)) {
    return false;
  }
  bssl::UniquePtr<uint8_t> free_der_a(der_a);
  if (!CBB_init(cbb_b.get(), 0) || !EVP_marshal_private_key(cbb_b.get(), b) ||
      !CBB_finish(cbb_b.get(), &der_b, &len_b)) {
    return false;
  }
  bssl::UniquePtr<uint8_t> free_der_b(der_b);
  return len_a == len_b && memcmp(der_a, der_b, len_a) == 0;
}

// Mirrors CreateAndSignX509Certificate (test_util.cc), which only generates
// RSA -- -export must handle both key types.
void CreateAndSignP256Certificate(bssl::UniquePtr<X509> &x509,
                                  bssl::UniquePtr<EVP_PKEY> *pkey_p) {
  bssl::UniquePtr<EC_KEY> ec_key(
      EC_KEY_new_by_curve_name(NID_X9_62_prime256v1));
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  if (!ec_key || !pkey || !EC_KEY_generate_key(ec_key.get()) ||
      !EVP_PKEY_assign_EC_KEY(pkey.get(), ec_key.release())) {
    return;
  }

  x509.reset(X509_new());
  if (!x509 || !X509_gmtime_adj(X509_getm_notBefore(x509.get()), 0) ||
      !X509_gmtime_adj(X509_getm_notAfter(x509.get()), 60 * 60 * 24 * 30L) ||
      !X509_set_pubkey(x509.get(), pkey.get())) {
    x509.reset();
    return;
  }
  X509_NAME *subject = X509_get_subject_name(x509.get());
  if (!X509_NAME_add_entry_by_NID(
          subject, NID_commonName, MBSTRING_UTF8,
          reinterpret_cast<const unsigned char *>("P256 Leaf"), -1, -1, 0) ||
      !X509_set_issuer_name(x509.get(), subject) ||
      X509_sign(x509.get(), pkey.get(), EVP_sha256()) <= 0) {
    x509.reset();
    return;
  }
  if (pkey_p != nullptr) {
    pkey_p->reset(pkey.release());
  }
}

// Writes |key| (optionally PEM-encrypted with |key_password|) and |certs|
// to |path| as PEM, key-then-certs unless |cert_first|. |key| may be null
// (a certs-only file, e.g. -certfile) and |certs| may be empty (a key-only
// file, e.g. -inkey).
bool WritePemBundle(const char *path, EVP_PKEY *key, const char *key_password,
                    const std::vector<X509 *> &certs, bool cert_first = false) {
  bssl::UniquePtr<BIO> bio(BIO_new_file(path, "wb"));
  if (!bio) {
    return false;
  }
  auto write_key = [&]() -> bool {
    if (key == nullptr) {
      return true;
    }
    if (key_password != nullptr) {
      return PEM_write_bio_PKCS8PrivateKey(
          bio.get(), key, EVP_aes_256_cbc(), key_password,
          static_cast<int>(strlen(key_password)), nullptr, nullptr);
    }
    return PEM_write_bio_PrivateKey(bio.get(), key, nullptr, nullptr, 0,
                                    nullptr, nullptr);
  };
  auto write_certs = [&]() -> bool {
    for (X509 *cert : certs) {
      if (!PEM_write_bio_X509(bio.get(), cert)) {
        return false;
      }
    }
    return true;
  };
  return cert_first ? (write_certs() && write_key())
                    : (write_key() && write_certs());
}

bool ReadBytesFromFile(const char *path, std::vector<uint8_t> *out) {
  ScopedFILE f(fopen(path, "rb"));
  return f && ReadAll(out, f.get());
}

// Re-imports |der| with AWS-LC's own PKCS12_get_key_and_certs, independent
// of this tool's own import path, as ground truth for what an export
// actually produced.
bool ImportPkcs12(const std::vector<uint8_t> &der, const char *password,
                  bssl::UniquePtr<EVP_PKEY> *out_key,
                  bssl::UniquePtr<STACK_OF(X509)> *out_certs) {
  out_certs->reset(sk_X509_new_null());
  if (!*out_certs) {
    return false;
  }
  EVP_PKEY *raw_key = nullptr;
  CBS cbs;
  CBS_init(&cbs, der.data(), der.size());
  if (!PKCS12_get_key_and_certs(&raw_key, out_certs->get(), &cbs, password)) {
    return false;
  }
  out_key->reset(raw_key);
  return true;
}

}  // namespace

class PKCS12ExportTest : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);
    ASSERT_GT(createTempFILEpath(inkey_path), 0u);
    ASSERT_GT(createTempFILEpath(certfile_path), 0u);

    CreateAndSignX509Certificate(rsa_cert, &rsa_key);
    ASSERT_TRUE(rsa_cert);
    ASSERT_TRUE(rsa_key);

    CreateAndSignP256Certificate(p256_cert, &p256_key);
    ASSERT_TRUE(p256_cert);
    ASSERT_TRUE(p256_key);
  }

  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(out_path);
    RemoveFile(inkey_path);
    RemoveFile(certfile_path);
  }

  bool WriteBaselineRsaBundle() {
    return WritePemBundle(in_path, rsa_key.get(), nullptr, {rsa_cert.get()});
  }

  // Exports (-in in_path plus |extra_args|), decrypts with |out_password|
  // (via -passout "pass:<out_password>", or |passout_arg| verbatim if
  // given), and checks the recovered key (full private material, not just
  // what EVP_PKEY_cmp checks) and certs (in order) match. |expect_key| may
  // be null to assert no key was exported.
  void ExpectExportRoundTrips(const args_list_t &extra_args,
                              const char *out_password, EVP_PKEY *expect_key,
                              const std::vector<X509 *> &expect_certs,
                              const char *passout_arg = nullptr) {
    std::string passout =
        passout_arg ? passout_arg : std::string("pass:") + out_password;
    args_list_t args = {"-export", "-in",  in_path, "-passout",
                        passout,   "-out", out_path};
    args.insert(args.end(), extra_args.begin(), extra_args.end());
    ASSERT_EQ(kToolExitSuccess, pkcs12Tool(args));

    std::vector<uint8_t> der;
    ASSERT_TRUE(ReadBytesFromFile(out_path, &der));
    bssl::UniquePtr<EVP_PKEY> key;
    bssl::UniquePtr<STACK_OF(X509)> certs;
    ASSERT_TRUE(ImportPkcs12(der, out_password, &key, &certs));
    if (expect_key == nullptr) {
      EXPECT_EQ(nullptr, key.get());
    } else {
      ASSERT_TRUE(key);
      EXPECT_TRUE(PrivateKeysEqual(key.get(), expect_key));
    }
    ASSERT_EQ(expect_certs.size(), sk_X509_num(certs.get()));
    for (size_t i = 0; i < expect_certs.size(); i++) {
      EXPECT_EQ(0, X509_cmp(sk_X509_value(certs.get(), i), expect_certs[i]))
          << "cert " << i;
    }
  }

  char in_path[PATH_MAX];
  char out_path[PATH_MAX];
  char inkey_path[PATH_MAX];
  char certfile_path[PATH_MAX];
  bssl::UniquePtr<X509> rsa_cert, p256_cert;
  bssl::UniquePtr<EVP_PKEY> rsa_key, p256_key;
};

TEST_F(PKCS12ExportTest, RoundTripsAcrossKeyTypesAndInputShapes) {
  struct Shape {
    const char *name;
    bool p256;
    bool separate_inkey;
    bool with_certfile;
  };
  const Shape shapes[] = {
      {"rsa combined", false, false, false},
      {"rsa separate inkey", false, true, false},
      {"rsa with certfile chain", false, false, true},
      {"p256 combined", true, false, false},
  };
  for (const auto &shape : shapes) {
    SCOPED_TRACE(shape.name);
    EVP_PKEY *key = shape.p256 ? p256_key.get() : rsa_key.get();
    X509 *cert = shape.p256 ? p256_cert.get() : rsa_cert.get();
    std::vector<X509 *> expect_certs = {cert};
    args_list_t extra;

    if (shape.separate_inkey) {
      ASSERT_TRUE(WritePemBundle(inkey_path, key, nullptr, {}));
      ASSERT_TRUE(WritePemBundle(in_path, nullptr, nullptr, {cert}));
      extra.insert(extra.end(), {"-inkey", inkey_path});
    } else {
      ASSERT_TRUE(WritePemBundle(in_path, key, nullptr, {cert}));
    }

    bssl::UniquePtr<X509> chain_cert;
    if (shape.with_certfile) {
      CreateAndSignX509Certificate(chain_cert, nullptr);
      ASSERT_TRUE(chain_cert);
      ASSERT_TRUE(
          WritePemBundle(certfile_path, nullptr, nullptr, {chain_cert.get()}));
      extra.insert(extra.end(), {"-certfile", certfile_path});
      expect_certs.push_back(chain_cert.get());
    }

    ExpectExportRoundTrips(extra, "outpw", key, expect_certs);
  }
}

// With -inkey given, a decoy private key embedded in -in must be ignored.
TEST_F(PKCS12ExportTest, InkeyTakesPrecedenceOverKeyEmbeddedInIn) {
  ASSERT_TRUE(WritePemBundle(inkey_path, rsa_key.get(), nullptr, {}));
  bssl::UniquePtr<EVP_PKEY> decoy_key;
  bssl::UniquePtr<X509> decoy_cert;
  CreateAndSignX509Certificate(decoy_cert, &decoy_key);
  ASSERT_TRUE(decoy_key);
  ASSERT_TRUE(
      WritePemBundle(in_path, decoy_key.get(), nullptr, {rsa_cert.get()}));

  ExpectExportRoundTrips({"-inkey", inkey_path}, "outpw", rsa_key.get(),
                         {rsa_cert.get()});
}

// The first -in certificate matching the key becomes the leaf; the
// remaining -in certs keep their relative order, followed by every
// -certfile entry in order.
TEST_F(PKCS12ExportTest, PicksFirstMatchingCertAsLeafAndOrdersRemainder) {
  bssl::UniquePtr<X509> decoy1, decoy2, cf1, cf2;
  CreateAndSignX509Certificate(decoy1, nullptr);
  CreateAndSignX509Certificate(decoy2, nullptr);
  CreateAndSignX509Certificate(cf1, nullptr);
  CreateAndSignX509Certificate(cf2, nullptr);
  ASSERT_TRUE(decoy1 && decoy2 && cf1 && cf2);

  ASSERT_TRUE(WritePemBundle(in_path, rsa_key.get(), nullptr,
                             {decoy1.get(), rsa_cert.get(), decoy2.get()}));
  ASSERT_TRUE(
      WritePemBundle(certfile_path, nullptr, nullptr, {cf1.get(), cf2.get()}));

  ExpectExportRoundTrips(
      {"-certfile", certfile_path}, "outpw", rsa_key.get(),
      {rsa_cert.get(), decoy1.get(), decoy2.get(), cf1.get(), cf2.get()});
}

TEST_F(PKCS12ExportTest, NoCertMatchesKeyFailsWithExactMessage) {
  bssl::UniquePtr<X509> unrelated_cert;
  CreateAndSignX509Certificate(unrelated_cert, nullptr);
  ASSERT_TRUE(unrelated_cert);
  ASSERT_TRUE(
      WritePemBundle(in_path, rsa_key.get(), nullptr, {unrelated_cert.get()}));
  ASSERT_TRUE(WriteBytesToFile(out_path, {'k', 'e', 'e', 'p'}));

  testing::internal::CaptureStderr();
  int result = pkcs12Tool(
      {"-export", "-in", in_path, "-passout", "pass:outpw", "-out", out_path});
  std::string stderr_output = testing::internal::GetCapturedStderr();

  EXPECT_EQ(kToolExitFailure, result);
  // Exact text from OpenSSL_1_1_1w's apps/pkcs12.c.
  EXPECT_EQ(stderr_output, "No certificate matches private key\n");
  EXPECT_EQ(ReadFileToString(out_path), "keep");
  ERR_clear_error();
}

TEST_F(PKCS12ExportTest, NokeysAndNocertsFlags) {
  ASSERT_TRUE(WriteBaselineRsaBundle());
  ExpectExportRoundTrips({"-nokeys"}, "outpw", nullptr, {rsa_cert.get()});

  // -nocerts skips loading certs from -in, but -certfile entries are still
  // added -- matching OpenSSL's own quirk.
  bssl::UniquePtr<X509> cf_cert;
  CreateAndSignX509Certificate(cf_cert, nullptr);
  ASSERT_TRUE(cf_cert);
  ASSERT_TRUE(WritePemBundle(certfile_path, nullptr, nullptr, {cf_cert.get()}));
  ExpectExportRoundTrips({"-nocerts", "-certfile", certfile_path}, "outpw",
                         rsa_key.get(), {cf_cert.get()});
}

TEST_F(PKCS12ExportTest, NothingToExportFails) {
  ASSERT_TRUE(WriteBaselineRsaBundle());
  ASSERT_TRUE(WriteBytesToFile(out_path, {'k', 'e', 'e', 'p'}));

  for (const args_list_t &flags :
       std::vector<args_list_t>{{"-noout"}, {"-nokeys", "-nocerts"}}) {
    SCOPED_TRACE(flags[0]);
    args_list_t args = {"-export",    "-in",  in_path, "-passout",
                        "pass:outpw", "-out", out_path};
    args.insert(args.end(), flags.begin(), flags.end());
    testing::internal::CaptureStderr();
    int result = pkcs12Tool(args);
    std::string stderr_output = testing::internal::GetCapturedStderr();
    EXPECT_EQ(kToolExitFailure, result);
    EXPECT_NE(stderr_output.find("Nothing to export"), std::string::npos)
        << stderr_output;
    EXPECT_EQ(ReadFileToString(out_path), "keep");
  }
}

// Without -nokeys, a key is mandatory: with only certificates in -in and no
// -inkey, there is no key to export.
TEST_F(PKCS12ExportTest, RequiresKeyUnlessNokeys) {
  ASSERT_TRUE(WritePemBundle(in_path, nullptr, nullptr, {rsa_cert.get()}));
  ASSERT_TRUE(WriteBytesToFile(out_path, {'k', 'e', 'e', 'p'}));

  EXPECT_EQ(kToolExitFailure, pkcs12Tool({"-export", "-in", in_path, "-passout",
                                          "pass:outpw", "-out", out_path}));
  EXPECT_EQ(ReadFileToString(out_path), "keep");
}

// -in and -out may be the same path: the input is fully buffered and
// validated before -out is opened.
TEST_F(PKCS12ExportTest, SameInputOutputPathSucceeds) {
  ASSERT_TRUE(WriteBaselineRsaBundle());
  ASSERT_EQ(kToolExitSuccess, pkcs12Tool({"-export", "-in", in_path, "-passout",
                                          "pass:outpw", "-out", in_path}));

  std::vector<uint8_t> der;
  ASSERT_TRUE(ReadBytesFromFile(in_path, &der));
  bssl::UniquePtr<EVP_PKEY> key;
  bssl::UniquePtr<STACK_OF(X509)> certs;
  ASSERT_TRUE(ImportPkcs12(der, "outpw", &key, &certs));
  EXPECT_TRUE(PrivateKeysEqual(key.get(), rsa_key.get()));
  ASSERT_EQ(1u, sk_X509_num(certs.get()));
  EXPECT_EQ(0, X509_cmp(sk_X509_value(certs.get(), 0), rsa_cert.get()));
}

#if !defined(OPENSSL_WINDOWS)
// The key may appear anywhere in the buffered -in input relative to its
// certs (here, after them); -in may also be omitted to read that same
// buffered input from stdin.
TEST_F(PKCS12ExportTest, CertBeforeKeyViaFileAndStdin) {
  ASSERT_TRUE(WritePemBundle(in_path, rsa_key.get(), nullptr, {rsa_cert.get()},
                             /*cert_first=*/true));
  ExpectExportRoundTrips({}, "outpw", rsa_key.get(), {rsa_cert.get()});

  std::vector<uint8_t> pem;
  ASSERT_TRUE(ReadBytesFromFile(in_path, &pem));
  int pipefd[2];
  ASSERT_EQ(pipe(pipefd), 0);
  ASSERT_EQ(write(pipefd[1], pem.data(), pem.size()),
            static_cast<ssize_t>(pem.size()));
  close(pipefd[1]);
  int old_stdin = dup(STDIN_FILENO);
  ASSERT_GE(old_stdin, 0);
  ASSERT_GE(dup2(pipefd[0], STDIN_FILENO), 0);
  close(pipefd[0]);
  clearerr(stdin);
  int result =
      pkcs12Tool({"-export", "-passout", "pass:outpw", "-out", out_path});
  dup2(old_stdin, STDIN_FILENO);
  close(old_stdin);
  clearerr(stdin);
  ASSERT_EQ(kToolExitSuccess, result);

  std::vector<uint8_t> der;
  ASSERT_TRUE(ReadBytesFromFile(out_path, &der));
  bssl::UniquePtr<EVP_PKEY> key;
  bssl::UniquePtr<STACK_OF(X509)> certs;
  ASSERT_TRUE(ImportPkcs12(der, "outpw", &key, &certs));
  EXPECT_TRUE(PrivateKeysEqual(key.get(), rsa_key.get()));
  ASSERT_EQ(1u, sk_X509_num(certs.get()));
  EXPECT_EQ(0, X509_cmp(sk_X509_value(certs.get(), 0), rsa_cert.get()));
}
#endif  // !OPENSSL_WINDOWS

// A later, malformed certificate block must fail the whole export, not
// just be skipped after a valid one is already found.
TEST_F(PKCS12ExportTest, MalformedCertAfterValidCertFails) {
  ASSERT_TRUE(WriteBaselineRsaBundle());
  {
    ScopedFILE f(fopen(in_path, "ab"));
    ASSERT_TRUE(f);
    ASSERT_GT(fprintf(f.get(), "%s",
                      "-----BEGIN CERTIFICATE-----\n"
                      "bm90IGEgcmVhbCBjZXJ0aWZpY2F0ZQ==\n"
                      "-----END CERTIFICATE-----\n"),
              0);
  }
  ASSERT_TRUE(WriteBytesToFile(out_path, {'k', 'e', 'e', 'p'}));

  EXPECT_EQ(kToolExitFailure, pkcs12Tool({"-export", "-in", in_path, "-passout",
                                          "pass:outpw", "-out", out_path}));
  EXPECT_EQ(ReadFileToString(out_path), "keep");
}

#if !defined(OPENSSL_WINDOWS)
// -out may be omitted to write the DER PKCS#12 to stdout; a write/flush
// failure there (broken pipe) must be reported as failure.
TEST_F(PKCS12ExportTest, StdoutOutput) {
  ASSERT_TRUE(WriteBaselineRsaBundle());
  {
    SCOPED_TRACE("success");
    char redirect_path[PATH_MAX];
    ASSERT_GT(createTempFILEpath(redirect_path), 0u);
    int redirect_fd = open(redirect_path, O_WRONLY | O_TRUNC);
    ASSERT_GE(redirect_fd, 0);
    fflush(stdout);
    int old_stdout = dup(STDOUT_FILENO);
    ASSERT_GE(old_stdout, 0);
    ASSERT_GE(dup2(redirect_fd, STDOUT_FILENO), 0);
    close(redirect_fd);

    int result =
        pkcs12Tool({"-export", "-in", in_path, "-passout", "pass:outpw"});
    fflush(stdout);
    dup2(old_stdout, STDOUT_FILENO);
    close(old_stdout);

    EXPECT_EQ(kToolExitSuccess, result);
    std::vector<uint8_t> der;
    ASSERT_TRUE(ReadBytesFromFile(redirect_path, &der));
    bssl::UniquePtr<EVP_PKEY> key;
    bssl::UniquePtr<STACK_OF(X509)> certs;
    ASSERT_TRUE(ImportPkcs12(der, "outpw", &key, &certs));
    EXPECT_TRUE(PrivateKeysEqual(key.get(), rsa_key.get()));
    RemoveFile(redirect_path);
  }
  {
    SCOPED_TRACE("broken pipe");
    int pipefd[2];
    ASSERT_EQ(pipe(pipefd), 0);
    close(pipefd[0]);  // No reader: writes/flushes below fail with EPIPE.
    auto old_sigpipe = signal(SIGPIPE, SIG_IGN);
    fflush(stdout);
    int old_stdout = dup(STDOUT_FILENO);
    ASSERT_GE(old_stdout, 0);
    ASSERT_GE(dup2(pipefd[1], STDOUT_FILENO), 0);
    close(pipefd[1]);

    int result =
        pkcs12Tool({"-export", "-in", in_path, "-passout", "pass:outpw"});

    dup2(old_stdout, STDOUT_FILENO);
    close(old_stdout);
    signal(SIGPIPE, old_sigpipe);
    clearerr(stdout);
    EXPECT_EQ(kToolExitFailure, result);
  }
}
#endif  // !OPENSSL_WINDOWS

TEST_F(PKCS12ExportTest, EncryptedCertificatesDoNotPrompt) {
  ASSERT_TRUE(WritePemBundle(inkey_path, rsa_key.get(), nullptr, {}));
  auto encode_cert = [](const void *cert, unsigned char **out) {
    return i2d_X509(const_cast<X509 *>(static_cast<const X509 *>(cert)), out);
  };
  bssl::UniquePtr<BIO> bio(BIO_new_file(in_path, "wb"));
  ASSERT_TRUE(bio);
  ASSERT_TRUE(PEM_ASN1_write_bio(
      encode_cert, PEM_STRING_X509, bio.get(), rsa_cert.get(),
      EVP_aes_256_cbc(), reinterpret_cast<const unsigned char *>("certpw"), 6,
      nullptr, nullptr));
  bio.reset();
  ASSERT_TRUE(WriteBytesToFile(out_path, {'k', 'e', 'e', 'p'}));
  testing::internal::CaptureStderr();
  int result = pkcs12Tool({"-export", "-in", in_path, "-inkey", inkey_path,
                           "-out", out_path, "-passout", "pass:outpw"});
  std::string errors = testing::internal::GetCapturedStderr();
  EXPECT_EQ(kToolExitFailure, result);
  EXPECT_EQ(std::string::npos, errors.find("Enter PEM pass phrase"));
  EXPECT_EQ("keep", ReadFileToString(out_path));
  ExpectExportRoundTrips({"-inkey", inkey_path, "-passin", "pass:certpw"},
                         "outpw", rsa_key.get(), {rsa_cert.get()});
}

// -password overrides -passout regardless of order (apps/pkcs12.c resolves
// this only after option parsing completes).
TEST_F(PKCS12ExportTest, PasswordOverridesPassoutRegardlessOfOrder) {
  ASSERT_TRUE(WriteBaselineRsaBundle());

  for (bool password_first : {false, true}) {
    SCOPED_TRACE(password_first);
    args_list_t args = {"-export", "-in", in_path, "-out", out_path};
    if (password_first) {
      args.insert(args.end(),
                  {"-password", "pass:winner", "-passout", "pass:ignored"});
    } else {
      args.insert(args.end(),
                  {"-passout", "pass:ignored", "-password", "pass:winner"});
    }
    ASSERT_EQ(kToolExitSuccess, pkcs12Tool(args));

    std::vector<uint8_t> der;
    ASSERT_TRUE(ReadBytesFromFile(out_path, &der));
    bssl::UniquePtr<EVP_PKEY> key;
    bssl::UniquePtr<STACK_OF(X509)> certs;
    EXPECT_TRUE(ImportPkcs12(der, "winner", &key, &certs));
    key.reset();
    certs.reset();
    EXPECT_FALSE(ImportPkcs12(der, "ignored", &key, &certs));
    ERR_clear_error();
  }
}

TEST_F(PKCS12ExportTest, LastScalarOptionWins) {
  ASSERT_TRUE(WriteBaselineRsaBundle());
  ASSERT_EQ(
      kToolExitSuccess,
      pkcs12Tool({"-export", "-in", "missing.pem", "-in", in_path, "-out", "",
                  "-out", out_path, "-passout", "pass:wrong", "-passout",
                  "pass:outpw", "-name", "old", "-name", "new"}));
  std::vector<uint8_t> der;
  ASSERT_TRUE(ReadBytesFromFile(out_path, &der));
  bssl::UniquePtr<EVP_PKEY> key;
  bssl::UniquePtr<STACK_OF(X509)> certs;
  ASSERT_TRUE(ImportPkcs12(der, "outpw", &key, &certs));
  ASSERT_EQ(1u, sk_X509_num(certs.get()));
  int len = 0;
  const uint8_t *alias = X509_alias_get0(sk_X509_value(certs.get(), 0), &len);
  ASSERT_NE(nullptr, alias);
  EXPECT_EQ("new", std::string(reinterpret_cast<const char *>(alias), len));
}

// -password is never used as -passin in -export mode, unlike import mode.
TEST_F(PKCS12ExportTest, PasswordDoesNotActAsPassin) {
  ASSERT_TRUE(
      WritePemBundle(in_path, rsa_key.get(), "keypassword", {rsa_cert.get()}));
  ASSERT_TRUE(WriteBytesToFile(out_path, {'k', 'e', 'e', 'p'}));

  EXPECT_EQ(kToolExitFailure,
            pkcs12Tool({"-export", "-in", in_path, "-password",
                        "pass:keypassword", "-out", out_path}));
  EXPECT_EQ(ReadFileToString(out_path), "keep");
  ERR_clear_error();

  EXPECT_EQ(kToolExitSuccess, pkcs12Tool({"-export", "-in", in_path, "-passin",
                                          "pass:keypassword", "-password",
                                          "pass:outpw", "-out", out_path}));
}

// With neither -passout nor -password given, the output password defaults
// to empty -- an intentional AWS-LC difference from upstream OpenSSL, which
// prompts interactively (see EmptyPasswordDefaultedWhenOmitted for the
// import-side default).
TEST_F(PKCS12ExportTest, DefaultPasswordsAreEmpty) {
  ASSERT_TRUE(WriteBaselineRsaBundle());
  ASSERT_EQ(kToolExitSuccess,
            pkcs12Tool({"-export", "-in", in_path, "-out", out_path}));

  std::vector<uint8_t> der;
  ASSERT_TRUE(ReadBytesFromFile(out_path, &der));
  bssl::UniquePtr<EVP_PKEY> key;
  bssl::UniquePtr<STACK_OF(X509)> certs;
  EXPECT_TRUE(ImportPkcs12(der, "", &key, &certs));
  key.reset();
  certs.reset();
  EXPECT_FALSE(ImportPkcs12(der, "notempty", &key, &certs));
  ERR_clear_error();
}

// -passin decrypts the input key (default empty, no prompts), whether it
// comes from a separate -inkey file or is embedded in -in.
TEST_F(PKCS12ExportTest, EncryptedInputKeyRequiresPassin) {
  for (bool separate_inkey : {false, true}) {
    SCOPED_TRACE(separate_inkey);
    if (separate_inkey) {
      ASSERT_TRUE(WritePemBundle(inkey_path, rsa_key.get(), "keypw", {}));
      ASSERT_TRUE(WritePemBundle(in_path, nullptr, nullptr, {rsa_cert.get()}));
    } else {
      ASSERT_TRUE(
          WritePemBundle(in_path, rsa_key.get(), "keypw", {rsa_cert.get()}));
    }
    args_list_t extra;
    if (separate_inkey) {
      extra = {"-inkey", inkey_path};
    }

    args_list_t base = {"-export",    "-in",  in_path, "-passout",
                        "pass:outpw", "-out", out_path};
    base.insert(base.end(), extra.begin(), extra.end());
    ASSERT_TRUE(WriteBytesToFile(out_path, {'k', 'e', 'e', 'p'}));
    EXPECT_EQ(kToolExitFailure, pkcs12Tool(base));  // Default-empty -passin.
    EXPECT_EQ("keep", ReadFileToString(out_path));
    ERR_clear_error();
    args_list_t wrong = base;
    wrong.insert(wrong.end(), {"-passin", "pass:wrong"});
    EXPECT_EQ(kToolExitFailure, pkcs12Tool(wrong));
    EXPECT_EQ("keep", ReadFileToString(out_path));
    ERR_clear_error();

    extra.insert(extra.end(), {"-passin", "pass:keypw"});
    ExpectExportRoundTrips(extra, "outpw", rsa_key.get(), {rsa_cert.get()});
  }
}

#if !defined(OPENSSL_WINDOWS)
TEST_F(PKCS12ExportTest, PasswordSourcesFileEnvAndFd) {
  ASSERT_TRUE(WriteBaselineRsaBundle());

  {
    SCOPED_TRACE("passout file:");
    char passout_file[PATH_MAX];
    ASSERT_GT(createTempFILEpath(passout_file), 0u);
    ASSERT_TRUE(WriteBytesToFile(passout_file, {'f', 'i', 'l', 'e', 'p', 'w'}));
    ExpectExportRoundTrips({}, "filepw", rsa_key.get(), {rsa_cert.get()},
                           (std::string("file:") + passout_file).c_str());
    RemoveFile(passout_file);
  }
  {
    SCOPED_TRACE("passout env:");
    setenv("AWSLC_PKCS12_TEST_PASSOUT", "envpw", 1);
    ExpectExportRoundTrips({}, "envpw", rsa_key.get(), {rsa_cert.get()},
                           "env:AWSLC_PKCS12_TEST_PASSOUT");
    unsetenv("AWSLC_PKCS12_TEST_PASSOUT");
  }
  {
    SCOPED_TRACE("passin fd:");
    ASSERT_TRUE(
        WritePemBundle(in_path, rsa_key.get(), "keypw", {rsa_cert.get()}));
    char passin_file[PATH_MAX];
    ASSERT_GT(createTempFILEpath(passin_file), 0u);
    ASSERT_TRUE(WriteBytesToFile(passin_file, {'k', 'e', 'y', 'p', 'w'}));
    int fd = open(passin_file, O_RDONLY);
    ASSERT_GE(fd, 0);
    ExpectExportRoundTrips({"-passin", "fd:" + std::to_string(fd)}, "outpw",
                           rsa_key.get(), {rsa_cert.get()});
    close(fd);
    RemoveFile(passin_file);
  }
}
#endif  // !OPENSSL_WINDOWS

// Every kind of export failure must leave a pre-existing -out untouched, and
// a validation failure must be caught before -out is even opened.
TEST_F(PKCS12ExportTest, FailedExportLeavesExistingOutfileUnchanged) {
  ASSERT_TRUE(WriteBytesToFile(out_path, {'k', 'e', 'e', 'p'}));

  {
    SCOPED_TRACE("bad key: -in is not valid PEM");
    ASSERT_TRUE(WriteBytesToFile(
        in_path, {0x00, 0x01, 0x02, 'n', 'o', 't', ' ', 'p', 'e', 'm'}));
    EXPECT_EQ(kToolExitFailure,
              pkcs12Tool({"-export", "-in", in_path, "-passout", "pass:x",
                          "-out", out_path}));
    EXPECT_EQ(ReadFileToString(out_path), "keep");
    ERR_clear_error();
  }
  {
    SCOPED_TRACE("bad password: encrypted key, -passin omitted");
    ASSERT_TRUE(WritePemBundle(in_path, rsa_key.get(), "realpassword",
                               {rsa_cert.get()}));
    EXPECT_EQ(kToolExitFailure,
              pkcs12Tool({"-export", "-in", in_path, "-passout", "pass:x",
                          "-out", out_path}));
    EXPECT_EQ(ReadFileToString(out_path), "keep");
    ERR_clear_error();
  }
  {
    SCOPED_TRACE("bad path: -in does not exist");
    EXPECT_EQ(kToolExitFailure,
              pkcs12Tool({"-export", "-in", "/nonexistent/path/to/file.pem",
                          "-passout", "pass:x", "-out", out_path}));
    EXPECT_EQ(ReadFileToString(out_path), "keep");
  }
  {
    SCOPED_TRACE("bad PBE: unrecognized -certpbe name");
    ASSERT_TRUE(WriteBaselineRsaBundle());
    EXPECT_EQ(kToolExitFailure,
              pkcs12Tool({"-export", "-in", in_path, "-passout", "pass:x",
                          "-certpbe", "not-a-real-pbe", "-out", out_path}));
    EXPECT_EQ(ReadFileToString(out_path), "keep");
    ERR_clear_error();
  }
  {
    SCOPED_TRACE("unsupported: recognized but unsupported PBES2 cipher");
    EXPECT_EQ(kToolExitFailure,
              pkcs12Tool({"-export", "-in", in_path, "-passout", "pass:x",
                          "-keypbe", "aes-256-cbc", "-out", out_path}));
    EXPECT_EQ(ReadFileToString(out_path), "keep");
    ERR_clear_error();
  }
  {
    SCOPED_TRACE("validation failure: does not even create -out");
    RemoveFile(out_path);
    EXPECT_EQ(kToolExitFailure,
              pkcs12Tool({"-export", "-in", in_path, "-nokeys", "-nocerts",
                          "-passout", "pass:x", "-out", out_path}));
    struct stat sb;
    EXPECT_NE(0, stat(out_path, &sb))
        << "-out should not have been created for a validation failure";
  }
}

TEST_F(PKCS12ExportTest, DefaultUsesLegacyAlgorithmsAndIteration2048) {
  ASSERT_TRUE(WriteBaselineRsaBundle());
  ASSERT_EQ(kToolExitSuccess, pkcs12Tool({"-export", "-in", in_path, "-passout",
                                          "pass:outpw", "-out", out_path}));

  std::vector<uint8_t> der;
  ASSERT_TRUE(ReadBytesFromFile(out_path, &der));
  Pkcs12AlgorithmInfo algs;
  ASSERT_TRUE(ParseExportedAlgorithms(der, &algs));

  ASSERT_TRUE(algs.cert_present);
  EXPECT_TRUE(algs.cert_encrypted);
  EXPECT_EQ(OidBytes(kPbeSha1Rc2_40Oid), algs.cert_pbe_oid);
  EXPECT_EQ(2048u, algs.cert_iterations);

  ASSERT_TRUE(algs.key_present);
  EXPECT_TRUE(algs.key_encrypted);
  EXPECT_EQ(OidBytes(kPbeSha1_3DesOid), algs.key_pbe_oid);
  EXPECT_EQ(2048u, algs.key_iterations);

  ASSERT_TRUE(algs.mac_present);
  EXPECT_EQ(OidBytes(kSha1Oid), algs.mac_digest_oid);
  EXPECT_EQ(2048u, algs.mac_iterations);
}

// -descert and -certpbe/-keypbe select the cert/key PBE (accepting only
// "PBE-SHA1-3DES", "PBE-SHA1-RC2-40", or "NONE"); when -descert and
// -certpbe conflict, whichever is last on the command line wins.
TEST_F(PKCS12ExportTest, PbeSelectionAndOrderingMatchesFlags) {
  ASSERT_TRUE(WriteBaselineRsaBundle());
  struct Case {
    const char *trace;
    args_list_t flags;
    bool cert_encrypted;
    std::vector<uint8_t> cert_oid;
    bool key_encrypted;
    std::vector<uint8_t> key_oid;
  };
  const Case cases[] = {
      {"descert",
       {"-descert"},
       true,
       OidBytes(kPbeSha1_3DesOid),
       true,
       OidBytes(kPbeSha1_3DesOid)},
      {"explicit swap",
       {"-certpbe", "PBE-SHA1-3DES", "-keypbe", "PBE-SHA1-RC2-40"},
       true,
       OidBytes(kPbeSha1_3DesOid),
       true,
       OidBytes(kPbeSha1Rc2_40Oid)},
      {"none", {"-certpbe", "NONE", "-keypbe", "NONE"}, false, {}, false, {}},
      {"descert then certpbe: certpbe wins",
       {"-descert", "-certpbe", "PBE-SHA1-RC2-40"},
       true,
       OidBytes(kPbeSha1Rc2_40Oid),
       true,
       OidBytes(kPbeSha1_3DesOid)},
      {"certpbe then descert: descert wins",
       {"-certpbe", "PBE-SHA1-RC2-40", "-descert"},
       true,
       OidBytes(kPbeSha1_3DesOid),
       true,
       OidBytes(kPbeSha1_3DesOid)},
  };
  for (const auto &c : cases) {
    SCOPED_TRACE(c.trace);
    args_list_t args = {"-export",    "-in",  in_path, "-passout",
                        "pass:outpw", "-out", out_path};
    args.insert(args.end(), c.flags.begin(), c.flags.end());
    ASSERT_EQ(kToolExitSuccess, pkcs12Tool(args));

    std::vector<uint8_t> der;
    ASSERT_TRUE(ReadBytesFromFile(out_path, &der));
    Pkcs12AlgorithmInfo algs;
    ASSERT_TRUE(ParseExportedAlgorithms(der, &algs));
    EXPECT_EQ(c.cert_encrypted, algs.cert_encrypted);
    EXPECT_EQ(c.key_encrypted, algs.key_encrypted);
    if (c.cert_encrypted) {
      EXPECT_EQ(c.cert_oid, algs.cert_pbe_oid);
    }
    if (c.key_encrypted) {
      EXPECT_EQ(c.key_oid, algs.key_pbe_oid);
    }

    // Content round-trips regardless of which PBE (or none) was used.
    bssl::UniquePtr<EVP_PKEY> key;
    bssl::UniquePtr<STACK_OF(X509)> certs;
    ASSERT_TRUE(ImportPkcs12(der, "outpw", &key, &certs));
    EXPECT_TRUE(PrivateKeysEqual(key.get(), rsa_key.get()));
    ASSERT_EQ(1u, sk_X509_num(certs.get()));
    EXPECT_EQ(0, X509_cmp(sk_X509_value(certs.get(), 0), rsa_cert.get()));
  }
}

// A totally unknown -certpbe/-keypbe name, a recognized-but-unsupported
// PBES2 cipher name (AWS-LC's PKCS12_create has no PBES2/AES support), and
// an out-of-range -iter must all fail rather than silently falling back.
TEST_F(PKCS12ExportTest, InvalidFlagValuesFail) {
  ASSERT_TRUE(WriteBaselineRsaBundle());
  ASSERT_TRUE(WriteBytesToFile(out_path, {'k', 'e', 'e', 'p'}));

  struct Case {
    const char *flag;
    const char *value;
  };
  const Case cases[] = {
      {"-certpbe", "not-a-real-pbe-name"},
      {"-certpbe", "aes-256-cbc"},
      {"-keypbe", "aes-128-cbc"},
      {"-iter", "0"},
      {"-iter", "-5"},
      {"-iter", "not-a-number"},
      {"-iter", "2147483648"},
      {"-iter", "999999999999999999999999"},
      {"-iter", ""},
      {"-certpbe", ""},
      {"-passout", ""},
      {"-password", ""},
      {"-passin", ""},
      {"-inkey", ""},
      {"-certfile", ""},
  };
  for (const auto &c : cases) {
    SCOPED_TRACE(std::string(c.flag) + " " + c.value);
    EXPECT_EQ(kToolExitFailure,
              pkcs12Tool({"-export", "-in", in_path, "-passout", "pass:outpw",
                          c.flag, c.value, "-out", out_path}));
    EXPECT_EQ(ReadFileToString(out_path), "keep");
    ERR_clear_error();
  }
}

// -iter/-noiter/-maciter/-nomaciter follow OpenSSL 3's CLI semantics.
TEST_F(PKCS12ExportTest, IterationFlagsFollowOpenSsl3Semantics) {
  ASSERT_TRUE(WriteBaselineRsaBundle());

  auto run_and_parse = [&](const args_list_t &extra_args,
                           Pkcs12AlgorithmInfo *out) {
    args_list_t args = {"-export",    "-in",  in_path, "-passout",
                        "pass:outpw", "-out", out_path};
    args.insert(args.end(), extra_args.begin(), extra_args.end());
    std::vector<uint8_t> der;
    return kToolExitSuccess == pkcs12Tool(args) &&
           ReadBytesFromFile(out_path, &der) &&
           ParseExportedAlgorithms(der, out);
  };

  const struct {
    const char *trace;
    args_list_t flags;
    uint64_t want_cert_iter, want_key_iter, want_mac_iter;
  } cases[] = {
      {"default", {}, 2048, 2048, 2048},
      {"-iter 500 sets cert, key, and mac", {"-iter", "500"}, 500, 500, 500},
      {"-noiter sets only cert/key", {"-noiter"}, 1, 1, 2048},
      {"-nomaciter sets only mac", {"-nomaciter"}, 2048, 2048, 1},
      {"-maciter alone is a documented no-op", {"-maciter"}, 2048, 2048, 2048},
      {"last iter wins", {"-noiter", "-nomaciter", "-iter", "7"}, 7, 7, 7},
      {"noiter overrides iter", {"-iter", "7", "-noiter"}, 1, 1, 7},
      {"maciter does not reset",
       {"-iter", "7", "-nomaciter", "-maciter"},
       7,
       7,
       1},
  };
  for (const auto &c : cases) {
    SCOPED_TRACE(c.trace);
    Pkcs12AlgorithmInfo algs;
    ASSERT_TRUE(run_and_parse(c.flags, &algs));
    EXPECT_EQ(c.want_cert_iter, algs.cert_iterations);
    EXPECT_EQ(c.want_key_iter, algs.key_iterations);
    EXPECT_EQ(c.want_mac_iter, algs.mac_iterations);
  }
}

// -name is encoded as a friendlyName bag attribute; AWS-LC's own parser
// surfaces it back as an X509 alias on the leaf certificate.
TEST_F(PKCS12ExportTest, NamePreservedAsFriendlyNameAlias) {
  ASSERT_TRUE(WriteBaselineRsaBundle());
  ASSERT_EQ(kToolExitSuccess,
            pkcs12Tool({"-export", "-in", in_path, "-passout", "pass:outpw",
                        "-name", "my friendly name", "-out", out_path}));

  std::vector<uint8_t> der;
  ASSERT_TRUE(ReadBytesFromFile(out_path, &der));
  bssl::UniquePtr<EVP_PKEY> key;
  bssl::UniquePtr<STACK_OF(X509)> certs;
  ASSERT_TRUE(ImportPkcs12(der, "outpw", &key, &certs));
  ASSERT_EQ(1u, sk_X509_num(certs.get()));

  int alias_len = 0;
  const uint8_t *alias =
      X509_alias_get0(sk_X509_value(certs.get(), 0), &alias_len);
  ASSERT_TRUE(alias != nullptr);
  EXPECT_EQ("my friendly name",
            std::string(reinterpret_cast<const char *>(alias), alias_len));
}

// -nodes has no meaning for -export (key protection comes from -keypbe);
// it must be accepted with a warning and have no effect on the output.
TEST_F(PKCS12ExportTest, NodesIgnoredWithWarningButKeyStaysEncrypted) {
  ASSERT_TRUE(WriteBaselineRsaBundle());

  testing::internal::CaptureStderr();
  int result = pkcs12Tool({"-export", "-nodes", "-in", in_path, "-passout",
                           "pass:outpw", "-out", out_path});
  std::string stderr_output = testing::internal::GetCapturedStderr();

  EXPECT_EQ(kToolExitSuccess, result);
  EXPECT_NE(stderr_output.find("arning"), std::string::npos)
      << stderr_output;  // Matches "warning"/"Warning".

  std::vector<uint8_t> der;
  ASSERT_TRUE(ReadBytesFromFile(out_path, &der));
  bssl::UniquePtr<EVP_PKEY> key;
  bssl::UniquePtr<STACK_OF(X509)> certs;
  EXPECT_FALSE(ImportPkcs12(der, "", &key, &certs));
  ERR_clear_error();
  ASSERT_TRUE(ImportPkcs12(der, "outpw", &key, &certs));
  EXPECT_TRUE(PrivateKeysEqual(key.get(), rsa_key.get()));
}

// -legacy remains a no-op for -export too, exactly as for import
// (LegacyIsAcceptedNoOp).
TEST_F(PKCS12ExportTest, LegacyIsNoOpForExport) {
  ASSERT_TRUE(WriteBaselineRsaBundle());
  char out_path_legacy[PATH_MAX];
  ASSERT_GT(createTempFILEpath(out_path_legacy), 0u);

  ASSERT_EQ(kToolExitSuccess, pkcs12Tool({"-export", "-in", in_path, "-passout",
                                          "pass:outpw", "-out", out_path}));
  ASSERT_EQ(kToolExitSuccess,
            pkcs12Tool({"-export", "-legacy", "-in", in_path, "-passout",
                        "pass:outpw", "-out", out_path_legacy}));

  std::vector<uint8_t> der, der_legacy;
  ASSERT_TRUE(ReadBytesFromFile(out_path, &der));
  ASSERT_TRUE(ReadBytesFromFile(out_path_legacy, &der_legacy));
  Pkcs12AlgorithmInfo algs, algs_legacy;
  ASSERT_TRUE(ParseExportedAlgorithms(der, &algs));
  ASSERT_TRUE(ParseExportedAlgorithms(der_legacy, &algs_legacy));

  EXPECT_EQ(algs.cert_pbe_oid, algs_legacy.cert_pbe_oid);
  EXPECT_EQ(algs.key_pbe_oid, algs_legacy.key_pbe_oid);
  EXPECT_EQ(algs.cert_iterations, algs_legacy.cert_iterations);
  EXPECT_EQ(algs.key_iterations, algs_legacy.key_iterations);
  EXPECT_EQ(algs.mac_iterations, algs_legacy.mac_iterations);
  RemoveFile(out_path_legacy);
}

// New flags that only make sense for -export must also fail without
// -export (beyond -export/-descert/etc. already covered by
// UnsupportedFlagsFail).
TEST_F(PKCS12Test, NewExportOnlyFlagsFailWithoutExport) {
  ASSERT_TRUE(WriteCertOnlyBundle("certsonly"));

  const std::vector<args_list_t> unsupported_without_export = {
      {"-inkey", "somekey.pem"},
      {"-certfile", "somecerts.pem"},
      {"-name", "somename"},
      {"-certpbe", "PBE-SHA1-3DES"},
      {"-keypbe", "PBE-SHA1-3DES"},
      {"-iter", "1000"},
      {"-noiter"},
      {"-maciter"},
      {"-nomaciter"},
  };
  for (const auto &flags : unsupported_without_export) {
    SCOPED_TRACE(flags[0]);
    args_list_t args = {"-in",  in_path, "-password", "pass:certsonly",
                        "-out", out_path};
    args.insert(args.end(), flags.begin(), flags.end());
    EXPECT_EQ(kToolExitFailure, pkcs12Tool(args));
  }
}

// Explicit 3DES matches the deployment command and avoids needing OpenSSL 3's
// legacy provider to import RC2. Default algorithms are tested above.
TEST_F(PKCS12ComparisonTest, OpenSSLImportsOurExport) {
  bssl::UniquePtr<X509> chain_cert;
  CreateAndSignX509Certificate(chain_cert, nullptr);
  ASSERT_TRUE(chain_cert);
  char chain_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(chain_path), 0u);
  {
    bssl::UniquePtr<BIO> bio(BIO_new_file(chain_path, "wb"));
    ASSERT_TRUE(bio);
    ASSERT_TRUE(PEM_write_bio_X509(bio.get(), chain_cert.get()));
  }

  for (bool with_chain : {false, true}) {
    SCOPED_TRACE(with_chain);
    std::string tool_export_command =
        ShellEscape(tool_executable_path) +
        " pkcs12 -keypbe PBE-SHA1-3DES -certpbe PBE-SHA1-3DES -export -inkey " +
        ShellEscape(key_path) + " -in " + ShellEscape(cert_path) +
        (with_chain ? " -certfile " + ShellEscape(chain_path) : "") +
        " -passout pass:exportpw -out " + ShellEscape(p12_path);
    ASSERT_EQ(0, ExecuteCommand(tool_export_command)) << tool_export_command;

    std::string openssl_command =
        ShellEscape(openssl_executable_path) + " pkcs12 -nokeys -in " +
        ShellEscape(p12_path) + " -passin pass:exportpw -out " +
        ShellEscape(out_path_openssl);
    ASSERT_EQ(0, ExecuteCommand(openssl_command)) << openssl_command;

    auto openssl_certs = ParseAllCertsFromPEMFile(out_path_openssl);
    ASSERT_EQ(with_chain ? 2u : 1u, openssl_certs.size());
    EXPECT_EQ(0, X509_cmp(openssl_certs[0].get(), cert.get()));
    if (with_chain) {
      EXPECT_EQ(0, X509_cmp(openssl_certs[1].get(), chain_cert.get()));
    }
  }
  RemoveFile(chain_path);
}

// The reverse direction of the chain check: the reference tool exports with
// -certfile, and both tools' imports must agree on cert count and order.
TEST_F(PKCS12ComparisonTest, ImportWithCertfileChainMatchesOpenSSL) {
  bssl::UniquePtr<X509> chain_cert;
  CreateAndSignX509Certificate(chain_cert, nullptr);
  ASSERT_TRUE(chain_cert);
  char chain_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(chain_path), 0u);
  {
    bssl::UniquePtr<BIO> bio(BIO_new_file(chain_path, "wb"));
    ASSERT_TRUE(bio);
    ASSERT_TRUE(PEM_write_bio_X509(bio.get(), chain_cert.get()));
  }

  std::string export_command =
      ShellEscape(openssl_executable_path) +
      " pkcs12 -keypbe PBE-SHA1-3DES -certpbe PBE-SHA1-3DES -export -inkey " +
      ShellEscape(key_path) + " -in " + ShellEscape(cert_path) + " -certfile " +
      ShellEscape(chain_path) + " -passout pass:exportpw -out " +
      ShellEscape(p12_path);
  ASSERT_EQ(0, ExecuteCommand(export_command)) << export_command;

  std::string tool_command = ShellEscape(tool_executable_path) +
                             " pkcs12 -nokeys -in " + ShellEscape(p12_path) +
                             " -password pass:exportpw -out " +
                             ShellEscape(out_path_tool);
  std::string openssl_command = ShellEscape(openssl_executable_path) +
                                " pkcs12 -nokeys -in " + ShellEscape(p12_path) +
                                " -password pass:exportpw -out " +
                                ShellEscape(out_path_openssl);
  ASSERT_EQ(0, ExecuteCommand(tool_command)) << tool_command;
  ASSERT_EQ(0, ExecuteCommand(openssl_command)) << openssl_command;

  auto tool_certs = ParseAllCertsFromPEMFile(out_path_tool);
  auto openssl_certs = ParseAllCertsFromPEMFile(out_path_openssl);
  ASSERT_EQ(2u, openssl_certs.size());
  ASSERT_EQ(tool_certs.size(), openssl_certs.size());
  for (size_t i = 0; i < tool_certs.size(); i++) {
    EXPECT_EQ(0, X509_cmp(tool_certs[i].get(), openssl_certs[i].get()));
  }
  RemoveFile(chain_path);
}

// -name's friendlyName must be visible to the reference tool too: real
// OpenSSL prints "Bag Attributes\n    friendlyName: ..." ahead of each PEM
// block that has one, unconditionally (not gated by -info). This also
// covers key-content interop for our -export (see OpenSSLImportsOurExport).
TEST_F(PKCS12ComparisonTest, OpenSSLSeesOurFriendlyName) {
  std::string tool_export_command =
      ShellEscape(tool_executable_path) +
      " pkcs12 -keypbe PBE-SHA1-3DES -certpbe PBE-SHA1-3DES -export -inkey " +
      ShellEscape(key_path) + " -in " + ShellEscape(cert_path) + " -name " +
      ShellEscape("comparison friendly name") +
      " -passout pass:exportpw -out " + ShellEscape(p12_path);
  ASSERT_EQ(0, ExecuteCommand(tool_export_command)) << tool_export_command;

  std::string openssl_command = ShellEscape(openssl_executable_path) +
                                " pkcs12 -nodes -in " + ShellEscape(p12_path) +
                                " -passin pass:exportpw -out " +
                                ShellEscape(out_path_openssl);
  ASSERT_EQ(0, ExecuteCommand(openssl_command)) << openssl_command;

  std::string output = ReadFileToString(out_path_openssl);
  EXPECT_NE(output.find("friendlyName: comparison friendly name"),
            std::string::npos)
      << output;

  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path_openssl, "rb"));
  ASSERT_TRUE(bio);
  bssl::UniquePtr<X509> skip(
      PEM_read_bio_X509(bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(skip);
  bssl::UniquePtr<EVP_PKEY> openssl_key(
      PEM_read_bio_PrivateKey(bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(openssl_key);
  EXPECT_TRUE(PrivateKeysEqual(openssl_key.get(), key.get()));
}
