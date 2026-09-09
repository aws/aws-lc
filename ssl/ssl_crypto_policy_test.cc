// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

// These tests cover the opt-in system crypto-policies seeding implemented in
// ssl/crypto_policy.cc. That code, and the internal declarations it relies on,
// only exist when built with -DENABLE_CRYPTO_POLICIES, so the whole body is
// guarded to keep this an (almost) empty translation unit otherwise.

#if defined(AWSLC_CRYPTO_POLICIES)

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <string>

#include <openssl/err.h>
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

// A path no policy file will ever occupy, used both to make seeding a no-op and
// as the subject of MissingFileIsIgnored.
const char kNoSuchPath[] = "/nonexistent/aws-lc/crypto-policy/does-not-exist";

// WriteTempPolicy writes |content| to a fresh temporary file and returns it.
// On platforms where temp files are unavailable the test is skipped.
bool WriteTempPolicy(TemporaryFile *out, const std::string &content) {
  if (SkipTempFileTests()) {
    return false;
  }
  return out->Init(content);
}

bool CtxHasCipherNamed(const SSL_CTX *ctx, const char *name) {
  const STACK_OF(SSL_CIPHER) *ciphers = SSL_CTX_get_ciphers(ctx);
  for (size_t i = 0; i < sk_SSL_CIPHER_num(ciphers); i++) {
    const SSL_CIPHER *c = sk_SSL_CIPHER_value(ciphers, i);
    if (strcmp(SSL_CIPHER_get_name(c), name) == 0) {
      return true;
    }
  }
  return false;
}

// ScopedEnv saves an environment variable on construction and restores it (to
// set-with-the-same-value or unset) on destruction. Tests that touch
// AWSLC_CRYPTO_POLICY_FILE must use this so they never leak policy-path state
// into later tests, whose SSL_CTX objects would then be seeded unexpectedly.
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

// A file that errors part way through is not a policy that simply ended: the
// directives read so far are half of somebody's policy. Opening a directory is
// the portable way to make the read fail.
TEST(CryptoPolicyParseTest, ReadErrorFails) {
  FILE *dir = fopen("/tmp", "r");
  if (dir == nullptr) {
    GTEST_SKIP() << "cannot open a directory as a file";
  }
  fclose(dir);

  CryptoPolicyConfig cfg = {};
  EXPECT_FALSE(ssl_crypto_policy_parse_file("/tmp", &cfg));
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

// CryptoPolicyTest points AWSLC_CRYPTO_POLICY_FILE at a path that does not
// exist, so an |SSL_CTX_new| inside a test is never seeded from whatever policy
// the host happens to have installed. Tests that assert on built-in defaults
// would otherwise pass only on machines with no crypto-policies configuration --
// that is, everywhere except the platforms this feature targets. Tests that want
// seeding drive it explicitly, either by calling
// |ssl_ctx_apply_crypto_policy| or by repointing |env_| at a fixture.
class CryptoPolicyTest : public ::testing::Test {
 protected:
  CryptoPolicyTest() : env_("AWSLC_CRYPTO_POLICY_FILE") {
    env_.Set(kNoSuchPath);
  }

  ScopedEnv env_;
};

TEST_F(CryptoPolicyTest, FullPolicyTLS) {
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, kDefaultPolicy)) {
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), TLS1_2_VERSION);
  EXPECT_EQ(SSL_CTX_get_max_proto_version(ctx.get()), TLS1_3_VERSION);
  EXPECT_GT(sk_SSL_CIPHER_num(SSL_CTX_get_ciphers(ctx.get())), 0u);

  // A valid policy leaves the error queue clean.
  EXPECT_EQ(ERR_peek_error(), 0u);
}

TEST_F(CryptoPolicyTest, SecLevelPrefixIsStripped) {
  const std::string content =
      "CipherString = @SECLEVEL=3:ECDHE-RSA-AES128-GCM-SHA256\n";
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, content)) {
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);
  // The named cipher survived, proving the leading @SECLEVEL token was stripped
  // rather than causing the whole rule string to be rejected.
  EXPECT_TRUE(CtxHasCipherNamed(ctx.get(), "ECDHE-RSA-AES128-GCM-SHA256"));
  EXPECT_EQ(ERR_peek_error(), 0u);

  // Negative control: the raw string (with the @SECLEVEL token) is rejected by
  // the cipher-list parser, which is exactly why stripping is required.
  bssl::UniquePtr<SSL_CTX> ctx2(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx2);
  EXPECT_FALSE(SSL_CTX_set_cipher_list(
      ctx2.get(), "@SECLEVEL=3:ECDHE-RSA-AES128-GCM-SHA256"));
  ERR_clear_error();
}

TEST_F(CryptoPolicyTest, MissingFileIsIgnored) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  const uint16_t min_before = SSL_CTX_get_min_proto_version(ctx.get());

  ssl_ctx_apply_crypto_policy(ctx.get(), kNoSuchPath,
                              /*is_dtls=*/false, /*version_locked=*/false);
  // Built-in defaults are untouched and no spurious errors are left behind.
  EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), min_before);
  EXPECT_EQ(ERR_peek_error(), 0u);
}

TEST_F(CryptoPolicyTest, MalformedFileIsBestEffort) {
  const std::string content =
      "this line has no equals sign\n"
      "# a comment\n"
      "[ crypto_policy ]\n"
      "UnknownDirective = whatever\n"
      "TLS.MinProtocol = TLSv1.2\n"
      // Forces a setter failure: kEDH and aDSS select FFDHE and DSS ciphers,
      // neither of which AWS-LC has, so the rule resolves to the empty set.
      "CipherString = @SECLEVEL=2:kEDH:-aDSS\n";
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, content)) {
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);
  // The valid directive still applied; the bogus one was dropped; no crash and
  // the error queue is clean.
  EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), TLS1_2_VERSION);
  EXPECT_EQ(ERR_peek_error(), 0u);
}

TEST_F(CryptoPolicyTest, DTLSMethodUsesDTLSDirectives) {
  const std::string content =
      "TLS.MinProtocol = TLSv1.3\n"     // must be ignored for a DTLS context
      "DTLS.MinProtocol = DTLSv1.2\n"
      "DTLS.MaxProtocol = DTLSv1.3\n";  // unrecognized -> skipped
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, content)) {
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(DTLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/true, /*version_locked=*/false);
  EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), DTLS1_2_VERSION);
  // DTLSv1.3 has no constant, so max was left at the built-in default.
  EXPECT_EQ(SSL_CTX_get_max_proto_version(ctx.get()), 0u);
  EXPECT_EQ(ERR_peek_error(), 0u);
}

TEST_F(CryptoPolicyTest, EnvOverrideDrivesSSLCTXNew) {
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, kDefaultPolicy)) {
    GTEST_SKIP();
  }

  env_.Set(policy.path().c_str());

  // SSL_CTX_new should now seed from the fixture via the env override.
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), TLS1_2_VERSION);
  EXPECT_EQ(SSL_CTX_get_max_proto_version(ctx.get()), TLS1_3_VERSION);
}

// End-to-end against the real system policy file, if one is present. This is
// what makes the Amazon Linux 2023 CI job validate
// /etc/crypto-policies/back-ends/opensslcnf.config; elsewhere it is a harmless
// skip. The env variable is restored on scope exit so this test never leaves
// seeding active for subsequent tests.
TEST_F(CryptoPolicyTest, SystemPolicyIfPresent) {
  // Read the compiled default path, ignoring the fixture's env override.
  env_.Unset();

  const char *path = ssl_crypto_policy_default_path();
  CryptoPolicyConfig cfg = {};
  if (!ssl_crypto_policy_parse_file(path, &cfg)) {
    GTEST_SKIP() << "no system crypto-policies file at " << path;
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  EXPECT_GT(sk_SSL_CIPHER_num(SSL_CTX_get_ciphers(ctx.get())), 0u);
  // If the system policy declared a TLS floor we recognize, it must have been
  // applied (a non-default, non-zero minimum version).
  if (cfg.tls_min[0] != '\0') {
    EXPECT_NE(SSL_CTX_get_min_proto_version(ctx.get()), 0u);
  }
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// A context from a version-locked SSL_METHOD keeps its pin. SSL_CTX_new sets
// both bounds to method->version, but the public setters validate against the
// protocol method's whole range, so a policy would otherwise widen the pin and
// hand back a version the caller deliberately excluded.
TEST_F(CryptoPolicyTest, VersionLockedMethodKeepsItsPin) {
  const std::string content =
      "TLS.MinProtocol = TLSv1.2\n"
      "TLS.MaxProtocol = TLSv1.3\n";
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, content)) {
    GTEST_SKIP();
  }

  // Negative control: the setter itself does not enforce the pin, which is why
  // ssl_ctx_apply_crypto_policy has to skip the directives.
  bssl::UniquePtr<SSL_CTX> unpinned(SSL_CTX_new(TLSv1_2_method()));
  ASSERT_TRUE(unpinned);
  EXPECT_TRUE(SSL_CTX_set_max_proto_version(unpinned.get(), TLS1_3_VERSION));
  EXPECT_EQ(SSL_CTX_get_max_proto_version(unpinned.get()), TLS1_3_VERSION);

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLSv1_2_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/true);

  // A pinned context reports 0 from the public getters, deferring to the
  // method's own bounds; this is what SSLTest.DefaultVersion asserts. Seeding a
  // bound would have replaced that with an explicit, wider ceiling.
  EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), 0u);
  EXPECT_EQ(SSL_CTX_get_max_proto_version(ctx.get()), 0u);
  // The effective bounds, which the handshake actually reads, are still TLS 1.2.
  EXPECT_EQ(ctx->conf_min_version, TLS1_2_VERSION);
  EXPECT_EQ(ctx->conf_max_version, TLS1_2_VERSION);
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// SSL_CTX_new applies the pin through the same path, so a version-locked
// context is unaffected by a policy delivered via the env override.
TEST_F(CryptoPolicyTest, VersionLockedMethodKeepsItsPinViaSSLCTXNew) {
  const std::string content = "TLS.MaxProtocol = TLSv1.3\n";
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, content)) {
    GTEST_SKIP();
  }

  env_.Set(policy.path().c_str());

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLSv1_2_method()));
  ASSERT_TRUE(ctx);
  EXPECT_EQ(SSL_CTX_get_max_proto_version(ctx.get()), 0u);
  EXPECT_EQ(ctx->conf_max_version, TLS1_2_VERSION);

  // Control: an unlocked method in the same process does pick the policy up, so
  // the assertion above reflects the pin and not seeding being inert.
  bssl::UniquePtr<SSL_CTX> unlocked(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(unlocked);
  EXPECT_EQ(SSL_CTX_get_max_proto_version(unlocked.get()), TLS1_3_VERSION);
}

// A CipherString whose tokens AWS-LC cannot satisfy must leave the built-in
// cipher list alone. Ignoring the setter's return value is not enough:
// ssl_create_cipher_list installs its empty result before reporting failure, so
// the context would be left unable to complete any handshake.
TEST_F(CryptoPolicyTest, UnsatisfiableCipherStringKeepsDefaults) {
  // kEDH and aDSS select FFDHE and DSS ciphers, neither of which AWS-LC has, so
  // the rule resolves to the empty set.
  const std::string content = "CipherString = @SECLEVEL=2:kEDH:-aDSS\n";
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, content)) {
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> baseline(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(baseline);
  const size_t default_count =
      sk_SSL_CIPHER_num(SSL_CTX_get_ciphers(baseline.get()));
  ASSERT_GT(default_count, 0u);

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);
  EXPECT_EQ(sk_SSL_CIPHER_num(SSL_CTX_get_ciphers(ctx.get())), default_count);
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// Likewise for Ciphersuites: a TLS 1.3 list AWS-LC cannot satisfy must not empty
// out the TLS 1.3 suites that SSL_CTX_new merged in.
TEST_F(CryptoPolicyTest, UnsatisfiableCiphersuitesKeepsDefaults) {
  const std::string content = "Ciphersuites = TLS_NONEXISTENT_SUITE_SHA256\n";
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, content)) {
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> baseline(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(baseline);
  const size_t default_count =
      sk_SSL_CIPHER_num(SSL_CTX_get_ciphers(baseline.get()));

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);
  EXPECT_EQ(sk_SSL_CIPHER_num(SSL_CTX_get_ciphers(ctx.get())), default_count);
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// Seeding must not swallow errors the caller queued beforehand. The cipher rule
// here resolves to the empty set, so seeding queues errors of its own and the
// cleanup path is exercised rather than skipped.
TEST_F(CryptoPolicyTest, CallerErrorQueueIsPreserved) {
  const std::string content = "CipherString = @SECLEVEL=2:kEDH:-aDSS\n";
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, content)) {
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);

  // A reason seeding cannot itself produce, so an error left behind by seeding is
  // distinguishable from the caller's.
  ERR_clear_error();
  OPENSSL_PUT_ERROR(SSL, SSL_R_BAD_ALERT);
  const uint32_t queued = ERR_peek_error();
  ASSERT_NE(queued, 0u);

  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  // The caller's error is still there, and it is also the newest, so nothing was
  // piled on top of it.
  EXPECT_EQ(ERR_peek_error(), queued);
  EXPECT_EQ(ERR_peek_last_error(), queued);
  ERR_clear_error();
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// The caller's queue must come back byte-identical, not merely equal. Rebuilding
// it -- which is what saving and restoring the queue does -- reallocates each
// entry's data string, so a pointer the caller is already holding from
// |ERR_peek_error_line_data| would dangle after an |SSL_CTX_new|.
TEST_F(CryptoPolicyTest, CallerErrorDataPointerSurvives) {
  const std::string content = "CipherString = @SECLEVEL=2:kEDH:-aDSS\n";
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, content)) {
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);

  ERR_clear_error();
  OPENSSL_PUT_ERROR(SSL, SSL_R_NO_CIPHER_MATCH);
  ERR_add_error_data(1, "caller data");
  const char *data_before;
  ASSERT_NE(ERR_peek_error_line_data(nullptr, nullptr, &data_before, nullptr),
            0u);
  ASSERT_STREQ(data_before, "caller data");

  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  const char *data_after;
  ASSERT_NE(ERR_peek_error_line_data(nullptr, nullptr, &data_after, nullptr),
            0u);
  EXPECT_EQ(data_before, data_after);
  EXPECT_STREQ(data_after, "caller data");
  ERR_clear_error();
}

// Seeding runs inside SSL_CTX_new, so a caller that brackets that call in its
// own error-queue mark must find the mark intact afterwards. ERR_set_mark flags
// a single queue entry rather than pushing a stack, so seeding cannot use it.
TEST_F(CryptoPolicyTest, CallerErrorMarkIsPreserved) {
  const std::string content = "CipherString = @SECLEVEL=2:kEDH:-aDSS\n";
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, content)) {
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);

  ERR_clear_error();
  OPENSSL_PUT_ERROR(SSL, SSL_R_NO_CIPHER_MATCH);
  const uint32_t queued = ERR_peek_error();
  ASSERT_NE(queued, 0u);
  ASSERT_TRUE(ERR_set_mark());

  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  // The mark still marks the caller's error, so popping to it keeps that error
  // instead of draining the queue.
  EXPECT_TRUE(ERR_pop_to_mark());
  EXPECT_EQ(ERR_peek_error(), queued);
  ERR_clear_error();
}

// A policy whose floor sits above its ceiling must be dropped whole. The public
// setters check each bound against the method's entire version range and never
// against each other, so applying the two independently would leave the context
// with an empty range and fail every later handshake.
TEST_F(CryptoPolicyTest, InvertedVersionBoundsAreIgnored) {
  const std::string content =
      "TLS.MinProtocol = TLSv1.3\n"
      "TLS.MaxProtocol = TLSv1.1\n";
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, content)) {
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  // Neither bound was touched, so both getters still defer to the method.
  EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), 0u);
  EXPECT_EQ(SSL_CTX_get_max_proto_version(ctx.get()), 0u);
  // The effective range the handshake reads is the built-in one, and non-empty.
  EXPECT_EQ(ctx->conf_min_version, TLS1_VERSION);
  EXPECT_EQ(ctx->conf_max_version, TLS1_3_VERSION);
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// The same for DTLS, where wire values run backwards: DTLS 1.0 is 0xfeff and
// DTLS 1.2 is 0xfefd. Comparing raw wire values would accept this inverted pair
// and reject the valid one below, so both directions are pinned here.
TEST_F(CryptoPolicyTest, InvertedDTLSVersionBoundsAreIgnored) {
  const std::string inverted =
      "DTLS.MinProtocol = DTLSv1.2\n"
      "DTLS.MaxProtocol = DTLSv1\n";
  TemporaryFile bad_policy;
  if (!WriteTempPolicy(&bad_policy, inverted)) {
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(DTLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), bad_policy.path().c_str(),
                              /*is_dtls=*/true, /*version_locked=*/false);
  EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), 0u);
  EXPECT_EQ(SSL_CTX_get_max_proto_version(ctx.get()), 0u);
  EXPECT_EQ(ctx->conf_min_version, DTLS1_VERSION);
  EXPECT_EQ(ctx->conf_max_version, DTLS1_2_VERSION);

  // Control: the well-ordered pair is still applied.
  const std::string ordered =
      "DTLS.MinProtocol = DTLSv1\n"
      "DTLS.MaxProtocol = DTLSv1.2\n";
  TemporaryFile good_policy;
  if (!WriteTempPolicy(&good_policy, ordered)) {
    GTEST_SKIP();
  }
  bssl::UniquePtr<SSL_CTX> ok(SSL_CTX_new(DTLS_method()));
  ASSERT_TRUE(ok);
  ssl_ctx_apply_crypto_policy(ok.get(), good_policy.path().c_str(),
                              /*is_dtls=*/true, /*version_locked=*/false);
  EXPECT_EQ(SSL_CTX_get_min_proto_version(ok.get()), DTLS1_VERSION);
  EXPECT_EQ(SSL_CTX_get_max_proto_version(ok.get()), DTLS1_2_VERSION);
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// A bound the policy supplies alone must still be checked against the bound the
// context already has, or a one-sided directive can invert the range by itself.
TEST_F(CryptoPolicyTest, OneSidedBoundBelowExistingFloorIsIgnored) {
  const std::string content =
      "TLS.MinProtocol = TLSv1.3\n"
      "TLS.MaxProtocol = TLSv1.3\n";
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, content)) {
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);
  ASSERT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), TLS1_3_VERSION);

  // The context now has a TLS 1.3 floor. A policy naming only a TLS 1.2 ceiling
  // would drop below it, so it must be refused.
  const std::string ceiling_only = "TLS.MaxProtocol = TLSv1.2\n";
  TemporaryFile second;
  if (!WriteTempPolicy(&second, ceiling_only)) {
    GTEST_SKIP();
  }
  ssl_ctx_apply_crypto_policy(ctx.get(), second.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);
  EXPECT_EQ(ctx->conf_min_version, TLS1_3_VERSION);
  EXPECT_EQ(ctx->conf_max_version, TLS1_3_VERSION);
  EXPECT_EQ(ERR_peek_error(), 0u);
}

BSSL_NAMESPACE_END

#endif  // AWSLC_CRYPTO_POLICIES
