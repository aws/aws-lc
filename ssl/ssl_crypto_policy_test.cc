// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

// These tests cover the system crypto-policies reader implemented in
// ssl/crypto_policy.cc. That code, and the internal declarations it relies on,
// only exist when built with -DENABLE_CRYPTO_POLICIES, so the whole body is
// guarded to keep this an (almost) empty translation unit otherwise.

#if defined(AWSLC_CRYPTO_POLICIES)

#include <stdlib.h>
#include <string.h>

#include <string>

#include <openssl/ssl.h>

#include "../crypto/test/file_util.h"
#include "internal.h"

BSSL_NAMESPACE_BEGIN

namespace {

// The Amazon Linux 2023 / Fedora DEFAULT policy, copied as crypto-policies
// writes it.
const char kDefaultPolicy[] =
    "# crypto-policies OpenSSL back-end (test fixture)\n"
    "CipherString = @SECLEVEL=2:kEECDH:kRSA:kEDH:kPSK:kDHEPSK:kECDHEPSK:"
    "kRSAPSK:-aDSS:-3DES:!DES:!RC4:!RC2:!IDEA:-SEED:!eNULL:!aNULL:!MD5:"
    "-SHA384:-CAMELLIA:-ARIA:-AESCCM8\n"
    "Ciphersuites = TLS_AES_256_GCM_SHA384:TLS_CHACHA20_POLY1305_SHA256:TLS_AES_128_GCM_SHA256\n"
    "TLS.MinProtocol = TLSv1.2\n"
    "TLS.MaxProtocol = TLSv1.3\n"
    "DTLS.MinProtocol = DTLSv1.2\n"
    "DTLS.MaxProtocol = DTLSv1.2\n"
    "SignatureAlgorithms = ECDSA+SHA256:ECDSA+SHA384:ECDSA+SHA512:ed25519:"
    "ed448:rsa_pss_pss_sha256:rsa_pss_pss_sha384:rsa_pss_pss_sha512:"
    "rsa_pss_rsae_sha256:rsa_pss_rsae_sha384:rsa_pss_rsae_sha512:RSA+SHA256:"
    "RSA+SHA384:RSA+SHA512:ECDSA+SHA224:RSA+SHA224\n"
    "Groups = X25519:secp256r1:X448:secp521r1:secp384r1:ffdhe2048:ffdhe3072:"
    "ffdhe4096:ffdhe6144:ffdhe8192\n";

// The expected parse of |kDefaultPolicy|, directive by directive.
const char kDefaultCipherString[] =
    "@SECLEVEL=2:kEECDH:kRSA:kEDH:kPSK:kDHEPSK:kECDHEPSK:kRSAPSK:-aDSS:-3DES:"
    "!DES:!RC4:!RC2:!IDEA:-SEED:!eNULL:!aNULL:!MD5:-SHA384:-CAMELLIA:-ARIA:"
    "-AESCCM8";
const char kDefaultCiphersuites[] =
    "TLS_AES_256_GCM_SHA384:TLS_CHACHA20_POLY1305_SHA256:TLS_AES_128_GCM_SHA256";
const char kDefaultSigalgs[] =
    "ECDSA+SHA256:ECDSA+SHA384:ECDSA+SHA512:ed25519:ed448:rsa_pss_pss_sha256:"
    "rsa_pss_pss_sha384:rsa_pss_pss_sha512:rsa_pss_rsae_sha256:"
    "rsa_pss_rsae_sha384:rsa_pss_rsae_sha512:RSA+SHA256:RSA+SHA384:RSA+SHA512:"
    "ECDSA+SHA224:RSA+SHA224";
const char kDefaultGroups[] =
    "X25519:secp256r1:X448:secp521r1:secp384r1:ffdhe2048:ffdhe3072:ffdhe4096:"
    "ffdhe6144:ffdhe8192";

// A path no policy file will ever occupy.
const char kNoSuchPath[] = "/nonexistent/aws-lc/crypto-policy/does-not-exist";

// WriteTempPolicy writes |content| to a fresh temporary file and returns it.
// On platforms where temp files are unavailable the test is skipped.
bool WriteTempPolicy(TemporaryFile *out, const std::string &content) {
  if (SkipTempFileTests()) {
    return false;
  }
  return out->Init(content);
}

// ScopedEnv saves an environment variable on construction and restores it (to
// set-with-the-same-value or unset) on destruction, so a test can never leak
// policy-path state into a later one.
class ScopedEnv {
 public:
  explicit ScopedEnv(const char *name) : name_(name) {
    const char *v = getenv(name);
    had_ = v != nullptr;
    if (had_) {
      saved_ = v;
    }
  }
  ~ScopedEnv() {
    if (had_) {
      setenv(name_, saved_.c_str(), /*overwrite=*/1);
    } else {
      unsetenv(name_);
    }
  }
  ScopedEnv(const ScopedEnv &) = delete;
  ScopedEnv &operator=(const ScopedEnv &) = delete;

  void Set(const char *value) { setenv(name_, value, /*overwrite=*/1); }
  void Unset() { unsetenv(name_); }

 private:
  const char *name_;
  bool had_ = false;
  std::string saved_;
};

}  // namespace

TEST(CryptoPolicyParseTest, FullPolicy) {
  TemporaryFile file;
  if (!WriteTempPolicy(&file, kDefaultPolicy)) {
    GTEST_SKIP() << "temporary files unavailable";
  }

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));

  EXPECT_STREQ(kDefaultCipherString, cfg.cipher_string);
  EXPECT_STREQ(kDefaultCiphersuites, cfg.ciphersuites);
  EXPECT_STREQ(kDefaultSigalgs, cfg.sigalgs);
  EXPECT_STREQ(kDefaultGroups, cfg.groups);
  EXPECT_STREQ("TLSv1.2", cfg.tls_min);
  EXPECT_STREQ("TLSv1.3", cfg.tls_max);
  EXPECT_STREQ("DTLSv1.2", cfg.dtls_min);
  EXPECT_STREQ("DTLSv1.2", cfg.dtls_max);
}

TEST(CryptoPolicyParseTest, MissingFileFails) {
  CryptoPolicyConfig cfg = {};
  EXPECT_FALSE(ssl_crypto_policy_parse_file(kNoSuchPath, &cfg));
  EXPECT_STREQ("", cfg.cipher_string);
}

TEST(CryptoPolicyParseTest, NullArgumentsFail) {
  CryptoPolicyConfig cfg = {};
  EXPECT_FALSE(ssl_crypto_policy_parse_file(nullptr, &cfg));
  EXPECT_FALSE(ssl_crypto_policy_parse_file(kNoSuchPath, nullptr));
}

TEST(CryptoPolicyParseTest, EmptyFileLeavesConfigEmpty) {
  TemporaryFile file;
  if (!WriteTempPolicy(&file, "")) {
    GTEST_SKIP() << "temporary files unavailable";
  }

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));
  EXPECT_STREQ("", cfg.cipher_string);
  EXPECT_STREQ("", cfg.ciphersuites);
  EXPECT_STREQ("", cfg.sigalgs);
  EXPECT_STREQ("", cfg.groups);
  EXPECT_STREQ("", cfg.tls_min);
  EXPECT_STREQ("", cfg.tls_max);
  EXPECT_STREQ("", cfg.dtls_min);
  EXPECT_STREQ("", cfg.dtls_max);
}

// crypto-policies emits section headers and comments, and OpenSSL config files
// carry keys from every back-end. None of it may derail the directives that
// follow.
TEST(CryptoPolicyParseTest, IgnoresCommentsSectionsAndUnknownKeys) {
  TemporaryFile file;
  if (!WriteTempPolicy(&file,
                       "# a comment\n"
                       "\n"
                       "[openssl_init]\n"
                       "providers = provider_sect\n"
                       "MinProtocol = TLSv1.1\n"  // No TLS./DTLS. prefix.
                       "ciphersuites = TLS_AES_128_CCM_SHA256\n"  // Wrong case.
                       "TLS.MinProtocol = TLSv1.2\n"
                       "no equals sign here\n"
                       "= value with no key\n"
                       "Groups = X25519\n")) {
    GTEST_SKIP() << "temporary files unavailable";
  }

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));
  EXPECT_STREQ("TLSv1.2", cfg.tls_min);
  EXPECT_STREQ("X25519", cfg.groups);
  EXPECT_STREQ("", cfg.ciphersuites);
}

TEST(CryptoPolicyParseTest, TrimsWhitespace) {
  TemporaryFile file;
  if (!WriteTempPolicy(&file,
                       "   Groups\t =\t X25519   \n"
                       "\tTLS.MinProtocol   =TLSv1.2\r\n"
                       "Ciphersuites=TLS_AES_128_GCM_SHA256\n")) {
    GTEST_SKIP() << "temporary files unavailable";
  }

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));
  EXPECT_STREQ("X25519", cfg.groups);
  EXPECT_STREQ("TLSv1.2", cfg.tls_min);
  EXPECT_STREQ("TLS_AES_128_GCM_SHA256", cfg.ciphersuites);
}

TEST(CryptoPolicyParseTest, StripsOneLayerOfQuotes) {
  TemporaryFile file;
  if (!WriteTempPolicy(&file,
                       "Groups = \"X25519\"\n"
                       "TLS.MinProtocol = 'TLSv1.2'\n"
                       "TLS.MaxProtocol = \"TLSv1.3\n"     // Unbalanced.
                       "Ciphersuites = \"'quoted'\"\n")) {  // Only the outer pair.
    GTEST_SKIP() << "temporary files unavailable";
  }

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));
  EXPECT_STREQ("X25519", cfg.groups);
  EXPECT_STREQ("TLSv1.2", cfg.tls_min);
  EXPECT_STREQ("\"TLSv1.3", cfg.tls_max);
  EXPECT_STREQ("'quoted'", cfg.ciphersuites);
}

TEST(CryptoPolicyParseTest, LastOccurrenceWins) {
  TemporaryFile file;
  if (!WriteTempPolicy(&file,
                       "Groups = X25519\n"
                       "Groups = secp384r1\n")) {
    GTEST_SKIP() << "temporary files unavailable";
  }

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));
  EXPECT_STREQ("secp384r1", cfg.groups);
}

// Half a group list is not a weaker version of the operator's policy, it is a
// different policy nobody chose, so an over-long value is dropped whole and the
// field left empty.
TEST(CryptoPolicyParseTest, OverlongValueIsDroppedNotTruncated) {
  std::string content = "Groups = ";
  content.append(AWSLC_CRYPTO_POLICY_MAX_VALUE + 1, 'X');
  content += "\nTLS.MinProtocol = TLSv1.2\n";

  TemporaryFile file;
  if (!WriteTempPolicy(&file, content)) {
    GTEST_SKIP() << "temporary files unavailable";
  }

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));
  EXPECT_STREQ("", cfg.groups);
  // The rest of the file still parses.
  EXPECT_STREQ("TLSv1.2", cfg.tls_min);
}

// A line longer than the read buffer is consumed to its newline rather than
// split, so its tail cannot be mistaken for a directive of its own.
TEST(CryptoPolicyParseTest, OverlongLineIsSkippedWhole) {
  std::string content = "Ciphersuites = ";
  content.append(9000, 'X');
  content += ":TLS.MinProtocol = TLSv1.1\nTLS.MinProtocol = TLSv1.2\n";

  TemporaryFile file;
  if (!WriteTempPolicy(&file, content)) {
    GTEST_SKIP() << "temporary files unavailable";
  }

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));
  EXPECT_STREQ("", cfg.ciphersuites);
  EXPECT_STREQ("TLSv1.2", cfg.tls_min);
}

// A file whose last line has no newline is still a complete line.
TEST(CryptoPolicyParseTest, FinalLineWithoutNewline) {
  TemporaryFile file;
  if (!WriteTempPolicy(&file, "Groups = X25519")) {
    GTEST_SKIP() << "temporary files unavailable";
  }

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));
  EXPECT_STREQ("X25519", cfg.groups);
}

TEST(CryptoPolicyParseTest, DefaultPathHonorsEnvOverride) {
  ScopedEnv env("AWSLC_CRYPTO_POLICY_FILE");

  env.Set("/tmp/some-policy.config");
  EXPECT_STREQ("/tmp/some-policy.config", ssl_crypto_policy_default_path());

  // An unset or empty override falls back to the compile-time default.
  env.Unset();
  EXPECT_STREQ(AWSLC_CRYPTO_POLICY_DEFAULT_FILE,
               ssl_crypto_policy_default_path());
  env.Set("");
  EXPECT_STREQ(AWSLC_CRYPTO_POLICY_DEFAULT_FILE,
               ssl_crypto_policy_default_path());
}

BSSL_NAMESPACE_END

#endif  // AWSLC_CRYPTO_POLICIES
