// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

// These tests cover the opt-in system crypto-policies seeding implemented in
// ssl/crypto_policy.cc. That code, and the internal declarations it relies on,
// only exist when built with -DENABLE_CRYPTO_POLICIES, so the whole body is
// guarded to keep this an (almost) empty translation unit otherwise.

#if defined(AWSLC_CRYPTO_POLICIES)

#include <stdlib.h>
#include <string.h>

#include <string>

#include <openssl/err.h>
#include <openssl/ssl.h>

#include "../crypto/test/file_util.h"
#include "internal.h"

BSSL_NAMESPACE_BEGIN

namespace {

// A realistic Amazon Linux 2023 / Fedora DEFAULT policy fragment.
const char kDefaultPolicy[] =
    "# crypto-policies OpenSSL back-end (test fixture)\n"
    "CipherString = @SECLEVEL=2:kEECDH:kRSA:kEDH:-aDSS:-3DES:!DES:!RC4:!MD5:-SHA384\n"
    "Ciphersuites = TLS_AES_256_GCM_SHA384:TLS_CHACHA20_POLY1305_SHA256:TLS_AES_128_GCM_SHA256\n"
    "TLS.MinProtocol = TLSv1.2\n"
    "TLS.MaxProtocol = TLSv1.3\n"
    "DTLS.MinProtocol = DTLSv1.2\n"
    "DTLS.MaxProtocol = DTLSv1.2\n"
    "SignatureAlgorithms = ECDSA+SHA256:RSA+SHA256:rsa_pss_rsae_sha256\n"
    "Groups = X25519:secp256r1:secp384r1\n";

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

// WriteTempPolicy writes |content| to a fresh temporary file and returns it.
// On platforms where temp files are unavailable the test is skipped.
bool WriteTempPolicy(TemporaryFile *out, const std::string &content) {
  if (SkipTempFileTests()) {
    return false;
  }
  return out->Init(content);
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

TEST(CryptoPolicyTest, FullPolicyTLS) {
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, kDefaultPolicy)) {
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false);

  EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), TLS1_2_VERSION);
  EXPECT_EQ(SSL_CTX_get_max_proto_version(ctx.get()), TLS1_3_VERSION);
  EXPECT_GT(sk_SSL_CIPHER_num(SSL_CTX_get_ciphers(ctx.get())), 0u);
  // A valid policy leaves the error queue clean.
  EXPECT_EQ(ERR_peek_error(), 0u);
}

TEST(CryptoPolicyTest, SecLevelPrefixIsStripped) {
  const std::string content =
      "CipherString = @SECLEVEL=3:ECDHE-RSA-AES128-GCM-SHA256\n";
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, content)) {
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false);
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

TEST(CryptoPolicyTest, MissingFileIsIgnored) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  const uint16_t min_before = SSL_CTX_get_min_proto_version(ctx.get());

  CryptoPolicyConfig cfg;
  EXPECT_FALSE(ssl_crypto_policy_parse_file(
      "/nonexistent/aws-lc/crypto-policy/does-not-exist", &cfg));

  ssl_ctx_apply_crypto_policy(
      ctx.get(), "/nonexistent/aws-lc/crypto-policy/does-not-exist",
      /*is_dtls=*/false);
  // Built-in defaults are untouched and no spurious errors are left behind.
  EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), min_before);
  EXPECT_EQ(ERR_peek_error(), 0u);
}

TEST(CryptoPolicyTest, MalformedFileIsBestEffort) {
  const std::string content =
      "this line has no equals sign\n"
      "# a comment\n"
      "[ crypto_policy ]\n"
      "UnknownDirective = whatever\n"
      "TLS.MinProtocol = TLSv1.2\n"
      // Forces a setter failure: unknown signature algorithm tokens cause the
      // whole SignatureAlgorithms directive to be dropped.
      "SignatureAlgorithms = totally-bogus-alg:another-bogus-alg\n";
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, content)) {
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false);
  // The valid directive still applied; the bogus one was dropped; no crash and
  // the error queue is clean.
  EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), TLS1_2_VERSION);
  EXPECT_EQ(ERR_peek_error(), 0u);
}

TEST(CryptoPolicyTest, DTLSMethodUsesDTLSDirectives) {
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
                              /*is_dtls=*/true);
  EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), DTLS1_2_VERSION);
  // DTLSv1.3 has no constant, so max was left at the built-in default.
  EXPECT_EQ(SSL_CTX_get_max_proto_version(ctx.get()), 0u);
  EXPECT_EQ(ERR_peek_error(), 0u);
}

TEST(CryptoPolicyTest, EnvOverrideDrivesSSLCTXNew) {
  TemporaryFile policy;
  if (!WriteTempPolicy(&policy, kDefaultPolicy)) {
    GTEST_SKIP();
  }

  ScopedEnv env("AWSLC_CRYPTO_POLICY_FILE");
  env.Set(policy.path().c_str());

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
TEST(CryptoPolicyTest, SystemPolicyIfPresent) {
  // Read the compiled default path, ignoring any env override for this test.
  ScopedEnv env("AWSLC_CRYPTO_POLICY_FILE");
  env.Unset();

  const char *path = ssl_crypto_policy_default_path();
  CryptoPolicyConfig cfg;
  if (!ssl_crypto_policy_parse_file(path, &cfg)) {
    GTEST_SKIP() << "no system crypto-policies file at " << path;
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  EXPECT_GT(sk_SSL_CIPHER_num(SSL_CTX_get_ciphers(ctx.get())), 0u);
  // If the system policy declared a TLS floor we recognize, it must have been
  // applied (a non-default, non-zero minimum version).
  if (!cfg.tls_min.empty()) {
    EXPECT_NE(SSL_CTX_get_min_proto_version(ctx.get()), 0u);
  }
  EXPECT_EQ(ERR_peek_error(), 0u);
}

BSSL_NAMESPACE_END

#endif  // AWSLC_CRYPTO_POLICIES
