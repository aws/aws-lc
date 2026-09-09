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

#include <algorithm>
#include <string>
#include <vector>

#include <openssl/err.h>
#include <openssl/ssl.h>

#include "../crypto/test/file_util.h"
#include "internal.h"

BSSL_NAMESPACE_BEGIN

namespace {

// The Amazon Linux 2023 / Fedora DEFAULT policy, copied byte for byte from
// /usr/share/crypto-policies/DEFAULT/opensslcnf.txt with a comment line added.
// Trimming it to what AWS-LC implements would defeat its purpose: Ciphersuites
// names a suite AWS-LC lacks, Groups carries crypto-policies' '*' key-share
// marker, and Groups and SignatureAlgorithms both name algorithms AWS-LC does
// not implement (X448 and the FFDHE groups; Ed448, the RSA-PSS-PSS algorithms,
// the SHA-224 pairs). A tidier fixture would exercise none of the filtering
// those directives need to take effect at all.
const char kDefaultPolicy[] =
    "# crypto-policies OpenSSL back-end (test fixture)\n"
    "CipherString = @SECLEVEL=2:kEECDH:kRSA:kEDH:kPSK:kDHEPSK:kECDHEPSK:"
    "kRSAPSK:-aDSS:-3DES:!DES:!RC4:!RC2:!IDEA:-SEED:!eNULL:!aNULL:!MD5:"
    "-SHA384:-CAMELLIA:-ARIA:-AESCCM8\n"
    "Ciphersuites = TLS_AES_256_GCM_SHA384:TLS_CHACHA20_POLY1305_SHA256:"
    "TLS_AES_128_GCM_SHA256:TLS_AES_128_CCM_SHA256\n"
    "TLS.MinProtocol = TLSv1.2\n"
    "TLS.MaxProtocol = TLSv1.3\n"
    "DTLS.MinProtocol = DTLSv1.2\n"
    "DTLS.MaxProtocol = DTLSv1.2\n"
    "SignatureAlgorithms = ECDSA+SHA256:ECDSA+SHA384:ECDSA+SHA512:ed25519:"
    "ed448:rsa_pss_pss_sha256:rsa_pss_pss_sha384:rsa_pss_pss_sha512:"
    "rsa_pss_rsae_sha256:rsa_pss_rsae_sha384:rsa_pss_rsae_sha512:RSA+SHA256:"
    "RSA+SHA384:RSA+SHA512:ECDSA+SHA224:RSA+SHA224\n"
    "Groups = *X25519:secp256r1:X448:secp521r1:secp384r1:ffdhe2048:ffdhe3072:"
    "ffdhe4096:ffdhe6144:ffdhe8192\n";

// The expected parse of |kDefaultPolicy|, directive by directive.
const char kDefaultCipherString[] =
    "@SECLEVEL=2:kEECDH:kRSA:kEDH:kPSK:kDHEPSK:kECDHEPSK:kRSAPSK:-aDSS:-3DES:"
    "!DES:!RC4:!RC2:!IDEA:-SEED:!eNULL:!aNULL:!MD5:-SHA384:-CAMELLIA:-ARIA:"
    "-AESCCM8";
const char kDefaultCiphersuites[] =
    "TLS_AES_256_GCM_SHA384:TLS_CHACHA20_POLY1305_SHA256:"
    "TLS_AES_128_GCM_SHA256:TLS_AES_128_CCM_SHA256";
const char kDefaultSigalgs[] =
    "ECDSA+SHA256:ECDSA+SHA384:ECDSA+SHA512:ed25519:ed448:rsa_pss_pss_sha256:"
    "rsa_pss_pss_sha384:rsa_pss_pss_sha512:rsa_pss_rsae_sha256:"
    "rsa_pss_rsae_sha384:rsa_pss_rsae_sha512:RSA+SHA256:RSA+SHA384:RSA+SHA512:"
    "ECDSA+SHA224:RSA+SHA224";
const char kDefaultGroups[] =
    "*X25519:secp256r1:X448:secp521r1:secp384r1:ffdhe2048:ffdhe3072:ffdhe4096:"
    "ffdhe6144:ffdhe8192";

// A path no policy file will ever occupy, used both to make seeding a no-op and
// as the subject of MissingFileIsIgnored.
const char kNoSuchPath[] = "/nonexistent/aws-lc/crypto-policy/does-not-exist";

// PolicyProtoVersion returns the AWS-LC version constant the crypto-policies
// protocol name |name| denotes, or 0 for a name AWS-LC has no version for. The
// table is spelled out rather than shared with the library so a test of the
// mapping is not a test against itself.
uint16_t PolicyProtoVersion(const char *name) {
  static const struct {
    const char *name;
    uint16_t version;
  } kVersions[] = {
      {"TLSv1", TLS1_VERSION},         {"TLSv1.1", TLS1_1_VERSION},
      {"TLSv1.2", TLS1_2_VERSION},     {"TLSv1.3", TLS1_3_VERSION},
      {"DTLSv1", DTLS1_VERSION},       {"DTLSv1.2", DTLS1_2_VERSION},
  };
  for (const auto &candidate : kVersions) {
    if (strcmp(candidate.name, name) == 0) {
      return candidate.version;
    }
  }
  return 0;
}

std::vector<std::string> CipherNames(const SSL_CTX *ctx) {
  std::vector<std::string> names;
  const STACK_OF(SSL_CIPHER) *ciphers = SSL_CTX_get_ciphers(ctx);
  for (size_t i = 0; i < sk_SSL_CIPHER_num(ciphers); i++) {
    names.push_back(SSL_CIPHER_get_name(sk_SSL_CIPHER_value(ciphers, i)));
  }
  return names;
}

// ToVector copies an |Array| out so gtest can print and compare it.
std::vector<uint16_t> ToVector(const Array<uint16_t> &in) {
  return std::vector<uint16_t>(in.begin(), in.end());
}

bool Contains(const Array<uint16_t> &haystack, uint16_t needle) {
  return std::find(haystack.begin(), haystack.end(), needle) != haystack.end();
}

// PolicyRequests reports whether the ':'-separated |value| asks for |name|. A
// '*' or '?' modifier still asks for the group; a '-' removes it, so the token
// is compared with the prefix left on and does not match.
bool PolicyRequests(const char *value, const char *name) {
  for (const char *tok = value;;) {
    const char *end = strchr(tok, ':');
    size_t len = end != nullptr ? static_cast<size_t>(end - tok) : strlen(tok);
    if (len > 0 && (tok[0] == '*' || tok[0] == '?')) {
      tok++;
      len--;
    }
    if (len == strlen(name) && strncmp(tok, name, len) == 0) {
      return true;
    }
    if (end == nullptr) {
      return false;
    }
    tok = end + 1;
  }
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

// Temporary files are unavailable in an Android APK context, which is the only
// platform limitation these tests tolerate. Skipping once here means every
// |TemporaryFile::Init| below is a real failure.
class CryptoPolicyParseTest : public ::testing::Test {
 protected:
  void SetUp() override {
    if (SkipTempFileTests()) {
      GTEST_SKIP();
    }
  }
};

TEST_F(CryptoPolicyParseTest, FullPolicy) {
  TemporaryFile file;
  ASSERT_TRUE(file.Init(kDefaultPolicy));

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
  EXPECT_STREQ("", cfg.post_quantum);
}

TEST_F(CryptoPolicyParseTest, PostQuantumDirective) {
  TemporaryFile file;
  ASSERT_TRUE(file.Init("AWSLC.PostQuantum = off\n"));

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));
  EXPECT_STREQ("off", cfg.post_quantum);
}

TEST_F(CryptoPolicyParseTest, MissingFileFails) {
  CryptoPolicyConfig cfg = {};
  EXPECT_FALSE(ssl_crypto_policy_parse_file(kNoSuchPath, &cfg));
  EXPECT_STREQ("", cfg.cipher_string);
}

// A file that errors part way through is not a policy that simply ended: the
// directives read so far are half of somebody's policy. Opening a directory is
// the portable way to make the read fail.
TEST_F(CryptoPolicyParseTest, ReadErrorFails) {
  FILE *dir = fopen("/tmp", "r");
  if (dir == nullptr) {
    GTEST_SKIP() << "cannot open a directory as a file";
  }
  fclose(dir);

  CryptoPolicyConfig cfg = {};
  EXPECT_FALSE(ssl_crypto_policy_parse_file("/tmp", &cfg));
}

TEST_F(CryptoPolicyParseTest, NullArgumentsFail) {
  CryptoPolicyConfig cfg = {};
  EXPECT_FALSE(ssl_crypto_policy_parse_file(nullptr, &cfg));
  EXPECT_FALSE(ssl_crypto_policy_parse_file(kNoSuchPath, nullptr));
}

TEST_F(CryptoPolicyParseTest, EmptyFileLeavesConfigEmpty) {
  TemporaryFile file;
  ASSERT_TRUE(file.Init(""));

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
TEST_F(CryptoPolicyParseTest, IgnoresCommentsSectionsAndUnknownKeys) {
  TemporaryFile file;
  ASSERT_TRUE(file.Init("# a comment\n"
                        "\n"
                        "[openssl_init]\n"
                        "providers = provider_sect\n"
                        "MinProtocol = TLSv1.1\n"  // No TLS./DTLS. prefix.
                        "ciphersuites = TLS_AES_128_CCM_SHA256\n"  // Wrong case
                        "TLS.MinProtocol = TLSv1.2\n"
                        "no equals sign here\n"
                        "= value with no key\n"
                        "Groups = X25519\n"));

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));
  EXPECT_STREQ("TLSv1.2", cfg.tls_min);
  EXPECT_STREQ("X25519", cfg.groups);
  EXPECT_STREQ("", cfg.ciphersuites);
}

TEST_F(CryptoPolicyParseTest, TrimsWhitespace) {
  TemporaryFile file;
  ASSERT_TRUE(file.Init("   Groups\t =\t X25519   \n"
                        "\tTLS.MinProtocol   =TLSv1.2\r\n"
                        "Ciphersuites=TLS_AES_128_GCM_SHA256\n"));

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));
  EXPECT_STREQ("X25519", cfg.groups);
  EXPECT_STREQ("TLSv1.2", cfg.tls_min);
  EXPECT_STREQ("TLS_AES_128_GCM_SHA256", cfg.ciphersuites);
}

TEST_F(CryptoPolicyParseTest, StripsOneLayerOfQuotes) {
  TemporaryFile file;
  ASSERT_TRUE(file.Init("Groups = \"X25519\"\n"
                        "TLS.MinProtocol = 'TLSv1.2'\n"
                        "TLS.MaxProtocol = \"TLSv1.3\n"      // Unbalanced.
                        "Ciphersuites = \"'quoted'\"\n"));  // Outer pair only.

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));
  EXPECT_STREQ("X25519", cfg.groups);
  EXPECT_STREQ("TLSv1.2", cfg.tls_min);
  EXPECT_STREQ("\"TLSv1.3", cfg.tls_max);
  EXPECT_STREQ("'quoted'", cfg.ciphersuites);
}

TEST_F(CryptoPolicyParseTest, LastOccurrenceWins) {
  TemporaryFile file;
  ASSERT_TRUE(file.Init("Groups = X25519\n"
                        "Groups = secp384r1\n"));

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));
  EXPECT_STREQ("secp384r1", cfg.groups);
}

// Half a group list is not a weaker version of the operator's policy, it is a
// different policy nobody chose, so an over-long value is dropped whole and the
// field left empty.
TEST_F(CryptoPolicyParseTest, OverlongValueIsDroppedNotTruncated) {
  std::string content = "Groups = ";
  content.append(AWSLC_CRYPTO_POLICY_MAX_VALUE + 1, 'X');
  content += "\nTLS.MinProtocol = TLSv1.2\n";

  TemporaryFile file;
  ASSERT_TRUE(file.Init(content));

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));
  EXPECT_STREQ("", cfg.groups);
  // The rest of the file still parses.
  EXPECT_STREQ("TLSv1.2", cfg.tls_min);
}

// A line longer than the read buffer is consumed to its newline rather than
// split, so its tail cannot be mistaken for a directive of its own.
TEST_F(CryptoPolicyParseTest, OverlongLineIsSkippedWhole) {
  std::string content = "Ciphersuites = ";
  content.append(9000, 'X');
  content += ":TLS.MinProtocol = TLSv1.1\nTLS.MinProtocol = TLSv1.2\n";

  TemporaryFile file;
  ASSERT_TRUE(file.Init(content));

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));
  EXPECT_STREQ("", cfg.ciphersuites);
  EXPECT_STREQ("TLSv1.2", cfg.tls_min);
}

// A file whose last line has no newline is still a complete line.
TEST_F(CryptoPolicyParseTest, FinalLineWithoutNewline) {
  TemporaryFile file;
  ASSERT_TRUE(file.Init("Groups = X25519"));

  CryptoPolicyConfig cfg = {};
  ASSERT_TRUE(ssl_crypto_policy_parse_file(file.path().c_str(), &cfg));
  EXPECT_STREQ("X25519", cfg.groups);
}

TEST_F(CryptoPolicyParseTest, DefaultPathHonorsEnvOverride) {
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

  void SetUp() override {
    if (SkipTempFileTests()) {
      GTEST_SKIP();
    }
  }

  ScopedEnv env_;
};

TEST_F(CryptoPolicyTest, FullPolicyTLS) {
  TemporaryFile policy;
  ASSERT_TRUE(policy.Init(kDefaultPolicy));

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), TLS1_2_VERSION);
  EXPECT_EQ(SSL_CTX_get_max_proto_version(ctx.get()), TLS1_3_VERSION);
  EXPECT_GT(sk_SSL_CIPHER_num(SSL_CTX_get_ciphers(ctx.get())), 0u);

  // Groups and SignatureAlgorithms took effect, keeping the policy's order and
  // dropping only what AWS-LC cannot do. This policy says nothing about
  // post-quantum algorithms, so AWS-LC's own are kept: the hybrids ahead of the
  // classical groups and ML-DSA after the classical algorithms, as in the
  // built-in defaults.
  EXPECT_EQ(ToVector(ctx->supported_group_list),
            (std::vector<uint16_t>{
                SSL_GROUP_X25519_MLKEM768, SSL_GROUP_SECP256R1_MLKEM768,
                SSL_GROUP_SECP384R1_MLKEM1024, SSL_GROUP_X25519,
                SSL_GROUP_SECP256R1, SSL_GROUP_SECP521R1, SSL_GROUP_SECP384R1}));
  const std::vector<uint16_t> expected_sigalgs = {
      SSL_SIGN_ECDSA_SECP256R1_SHA256, SSL_SIGN_ECDSA_SECP384R1_SHA384,
      SSL_SIGN_ECDSA_SECP521R1_SHA512, SSL_SIGN_ED25519,
      SSL_SIGN_RSA_PSS_RSAE_SHA256,    SSL_SIGN_RSA_PSS_RSAE_SHA384,
      SSL_SIGN_RSA_PSS_RSAE_SHA512,    SSL_SIGN_RSA_PKCS1_SHA256,
      SSL_SIGN_RSA_PKCS1_SHA384,       SSL_SIGN_RSA_PKCS1_SHA512,
      SSL_SIGN_MLDSA44,                SSL_SIGN_MLDSA65,
      SSL_SIGN_MLDSA87};
  EXPECT_EQ(ToVector(ctx->verify_sigalgs), expected_sigalgs);
  EXPECT_EQ(ToVector(ctx->cert->sigalgs), expected_sigalgs);

  // A valid policy leaves the error queue clean.
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// The two directives that need filtering. Without it a stock policy value is
// rejected whole and the directive silently does nothing, which is what the
// negative controls here assert about the unfiltered value.
TEST_F(CryptoPolicyTest, UnsupportedGroupsAndSigalgsAreFiltered) {
  bssl::UniquePtr<SSL_CTX> raw(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(raw);
  EXPECT_FALSE(SSL_CTX_set1_groups_list(raw.get(), kDefaultGroups));
  EXPECT_FALSE(SSL_CTX_set1_sigalgs_list(raw.get(), kDefaultSigalgs));
  ERR_clear_error();

  const std::string content = std::string("Groups = ") + kDefaultGroups + "\n" +
                              "SignatureAlgorithms = " + kDefaultSigalgs + "\n";
  TemporaryFile policy;
  ASSERT_TRUE(policy.Init(content));

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  // P-256 is present, so the crypto-policies spelling "secp256r1" was translated
  // rather than dropped.
  EXPECT_EQ(ToVector(ctx->supported_group_list),
            (std::vector<uint16_t>{
                SSL_GROUP_X25519_MLKEM768, SSL_GROUP_SECP256R1_MLKEM768,
                SSL_GROUP_SECP384R1_MLKEM1024, SSL_GROUP_X25519,
                SSL_GROUP_SECP256R1, SSL_GROUP_SECP521R1, SSL_GROUP_SECP384R1}));
  EXPECT_EQ(ctx->verify_sigalgs.size(), 13u);
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// The OpenSSL 3.5 group-list modifiers. '*' and '?' decorate a group that is
// still wanted, so keeping the prefix would drop it; '-' excludes one.
TEST_F(CryptoPolicyTest, GroupListModifiers) {
  // Post-quantum off so the assertion is the policy's own list, without the
  // hybrids the defaults would prepend.
  const std::string content =
      "Groups = *X25519:?secp384r1:-secp521r1:secp256r1\n"
      "AWSLC.PostQuantum = off\n";
  TemporaryFile policy;
  ASSERT_TRUE(policy.Init(content));

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  EXPECT_EQ(ToVector(ctx->supported_group_list),
            (std::vector<uint16_t>{SSL_GROUP_X25519, SSL_GROUP_SECP384R1,
                                   SSL_GROUP_SECP256R1}));
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// A directive naming nothing AWS-LC implements is dropped, leaving the built-in
// defaults in force. In particular no post-quantum algorithm is merged into an
// otherwise empty result, which would leave the context offering ML-DSA and
// nothing else.
TEST_F(CryptoPolicyTest, WhollyUnsupportedDirectivesKeepDefaults) {
  const std::string content =
      "Groups = X448:ffdhe2048:ffdhe3072\n"
      "SignatureAlgorithms = ed448:ECDSA+SHA224:rsa_pss_pss_sha256\n";
  TemporaryFile policy;
  ASSERT_TRUE(policy.Init(content));

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  EXPECT_TRUE(ctx->supported_group_list.empty());
  EXPECT_TRUE(ctx->cert->sigalgs.empty());
  EXPECT_TRUE(ctx->verify_sigalgs.empty());
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// Two spellings of one group collapse to a single entry. |SSL_CTX_set1_group_ids|
// rejects a list naming the same ID twice, so without this the whole directive
// would be dropped.
TEST_F(CryptoPolicyTest, RepeatedGroupSpellingsCollapse) {
  const std::string content = "Groups = secp256r1:prime256v1:P-256:X25519\n";
  TemporaryFile policy;
  ASSERT_TRUE(policy.Init(content));

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  // The P-384 hybrid is not restored: the policy dropped P-384, and restoring it
  // would put P-384 key exchange back under another name.
  EXPECT_EQ(ToVector(ctx->supported_group_list),
            (std::vector<uint16_t>{SSL_GROUP_X25519_MLKEM768,
                                   SSL_GROUP_SECP256R1_MLKEM768,
                                   SSL_GROUP_SECP256R1, SSL_GROUP_X25519}));
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// Every stock crypto-policies value predates ML-KEM and ML-DSA and so names
// neither. Since both setters replace AWS-LC's list rather than intersecting with
// it, such a policy would otherwise strip post-quantum support from every
// context that seeds from it.
TEST_F(CryptoPolicyTest, PolicySilentOnPQKeepsPQDefaults) {
  TemporaryFile policy;
  ASSERT_TRUE(policy.Init(kDefaultPolicy));

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  for (uint16_t group :
       {SSL_GROUP_X25519_MLKEM768, SSL_GROUP_SECP256R1_MLKEM768,
        SSL_GROUP_SECP384R1_MLKEM1024}) {
    EXPECT_TRUE(Contains(ctx->supported_group_list, group)) << group;
  }
  for (uint16_t sigalg :
       {SSL_SIGN_MLDSA44, SSL_SIGN_MLDSA65, SSL_SIGN_MLDSA87}) {
    EXPECT_TRUE(Contains(ctx->cert->sigalgs, sigalg)) << sigalg;
    EXPECT_TRUE(Contains(ctx->verify_sigalgs, sigalg)) << sigalg;
  }
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// The only way to turn post-quantum off through the policy. The crypto-policies
// directives are plain preference lists with no syntax for excluding an
// algorithm, so silence cannot mean "no".
TEST_F(CryptoPolicyTest, PostQuantumOffDropsPQDefaults) {
  const std::string content =
      std::string(kDefaultPolicy) + "AWSLC.PostQuantum = off\n";
  TemporaryFile policy;
  ASSERT_TRUE(policy.Init(content));

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  EXPECT_EQ(ToVector(ctx->supported_group_list),
            (std::vector<uint16_t>{SSL_GROUP_X25519, SSL_GROUP_SECP256R1,
                                   SSL_GROUP_SECP521R1, SSL_GROUP_SECP384R1}));
  EXPECT_EQ(ctx->verify_sigalgs.size(), 10u);
  for (uint16_t sigalg :
       {SSL_SIGN_MLDSA44, SSL_SIGN_MLDSA65, SSL_SIGN_MLDSA87}) {
    EXPECT_FALSE(Contains(ctx->cert->sigalgs, sigalg)) << sigalg;
  }
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// Any other value, including a misspelling, leaves the defaults in force. Turning
// post-quantum off is the surprising outcome, so it takes the exact spelling.
TEST_F(CryptoPolicyTest, PostQuantumOtherValuesKeepPQDefaults) {
  for (const char *value : {"on", "ON", "yes", "0", "false", ""}) {
    SCOPED_TRACE(value);
    const std::string content = std::string(kDefaultPolicy) +
                               "AWSLC.PostQuantum = " + value + "\n";
    TemporaryFile policy;
    ASSERT_TRUE(policy.Init(content));

    bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ctx);
    ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                                /*is_dtls=*/false, /*version_locked=*/false);

    EXPECT_TRUE(
        Contains(ctx->supported_group_list, SSL_GROUP_X25519_MLKEM768));
    EXPECT_TRUE(Contains(ctx->cert->sigalgs, SSL_SIGN_MLDSA65));
  }
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// "off" is matched without regard to case, as config-file tokens do not carry it
// reliably.
TEST_F(CryptoPolicyTest, PostQuantumOffIsCaseInsensitive) {
  const std::string content =
      std::string(kDefaultPolicy) + "AWSLC.PostQuantum = OFF\n";
  TemporaryFile policy;
  ASSERT_TRUE(policy.Init(content));

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  EXPECT_FALSE(Contains(ctx->supported_group_list, SSL_GROUP_X25519_MLKEM768));
  EXPECT_FALSE(Contains(ctx->cert->sigalgs, SSL_SIGN_MLDSA65));
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// Only the hybrids whose classical half the policy kept come back. An operator
// who dropped a curve did not ask for it back inside a hybrid.
TEST_F(CryptoPolicyTest, HybridNeedsItsClassicalHalf) {
  const std::string content = "Groups = secp384r1\n";
  TemporaryFile policy;
  ASSERT_TRUE(policy.Init(content));

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  EXPECT_EQ(ToVector(ctx->supported_group_list),
            (std::vector<uint16_t>{SSL_GROUP_SECP384R1_MLKEM1024,
                                   SSL_GROUP_SECP384R1}));
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// A policy that names one post-quantum group has an opinion about them, so the
// others are not added back.
TEST_F(CryptoPolicyTest, PolicyNamingPQGroupIsAuthoritative) {
  const std::string content =
      "Groups = X25519MLKEM768:X25519:secp256r1:secp384r1\n";
  TemporaryFile policy;
  ASSERT_TRUE(policy.Init(content));

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  EXPECT_EQ(ToVector(ctx->supported_group_list),
            (std::vector<uint16_t>{SSL_GROUP_X25519_MLKEM768, SSL_GROUP_X25519,
                                   SSL_GROUP_SECP256R1, SSL_GROUP_SECP384R1}));
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// Removing a hybrid with the '-' modifier is an opinion about it too, so it
// must not come back with the defaults. The other hybrids do.
TEST_F(CryptoPolicyTest, PolicyRemovingPQGroupKeepsItOut) {
  const std::string content =
      "Groups = X25519:secp256r1:secp384r1:-X25519MLKEM768\n";
  TemporaryFile policy;
  ASSERT_TRUE(policy.Init(content));

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  EXPECT_FALSE(Contains(ctx->supported_group_list, SSL_GROUP_X25519_MLKEM768));
  EXPECT_TRUE(
      Contains(ctx->supported_group_list, SSL_GROUP_SECP256R1_MLKEM768));
  EXPECT_TRUE(Contains(ctx->supported_group_list, SSL_GROUP_X25519));
  EXPECT_EQ(ERR_peek_error(), 0u);
}

TEST_F(CryptoPolicyTest, PolicyNamingMLDSAIsAuthoritative) {
  const std::string content = "SignatureAlgorithms = mldsa65:ECDSA+SHA256\n";
  TemporaryFile policy;
  ASSERT_TRUE(policy.Init(content));

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  EXPECT_EQ(ToVector(ctx->cert->sigalgs),
            (std::vector<uint16_t>{SSL_SIGN_MLDSA65,
                                   SSL_SIGN_ECDSA_SECP256R1_SHA256}));
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// The crypto-policies framework hyphenates the post-quantum names and does not
// fix their case, so these spellings must resolve for a PQ-aware policy to be
// recognized as one at all.
TEST_F(CryptoPolicyTest, CryptoPoliciesPQSpellingsResolve) {
  const std::string content =
      "Groups = X25519-MLKEM768:SECP256R1-MLKEM768:secp384r1-mlkem1024\n"
      "SignatureAlgorithms = ML-DSA-44:ml-dsa-65:ML-DSA-87\n";
  TemporaryFile policy;
  ASSERT_TRUE(policy.Init(content));

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);

  EXPECT_EQ(ToVector(ctx->supported_group_list),
            (std::vector<uint16_t>{SSL_GROUP_X25519_MLKEM768,
                                   SSL_GROUP_SECP256R1_MLKEM768,
                                   SSL_GROUP_SECP384R1_MLKEM1024}));
  EXPECT_EQ(ToVector(ctx->cert->sigalgs),
            (std::vector<uint16_t>{SSL_SIGN_MLDSA44, SSL_SIGN_MLDSA65,
                                   SSL_SIGN_MLDSA87}));
  EXPECT_EQ(ERR_peek_error(), 0u);
}

TEST_F(CryptoPolicyTest, SecLevelPrefixIsStripped) {
  const std::string content =
      "CipherString = @SECLEVEL=3:ECDHE-RSA-AES128-GCM-SHA256\n";
  TemporaryFile policy;
  ASSERT_TRUE(policy.Init(content));

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
  ASSERT_TRUE(policy.Init(content));

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
  ASSERT_TRUE(policy.Init(content));

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
  ASSERT_TRUE(policy.Init(kDefaultPolicy));

  env_.Set(policy.path().c_str());

  // SSL_CTX_new should now seed from the fixture via the env override.
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), TLS1_2_VERSION);
  EXPECT_EQ(SSL_CTX_get_max_proto_version(ctx.get()), TLS1_3_VERSION);
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
  ASSERT_TRUE(policy.Init(content));

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
  ASSERT_TRUE(policy.Init(content));

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
  ASSERT_TRUE(policy.Init(content));

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
  ASSERT_TRUE(policy.Init(content));

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
  ASSERT_TRUE(policy.Init(content));

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
  ASSERT_TRUE(policy.Init(content));

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
  ASSERT_TRUE(policy.Init(content));

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
  ASSERT_TRUE(policy.Init(content));

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
  ASSERT_TRUE(bad_policy.Init(inverted));

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
  ASSERT_TRUE(good_policy.Init(ordered));
  bssl::UniquePtr<SSL_CTX> ok(SSL_CTX_new(DTLS_method()));
  ASSERT_TRUE(ok);
  ssl_ctx_apply_crypto_policy(ok.get(), good_policy.path().c_str(),
                              /*is_dtls=*/true, /*version_locked=*/false);
  EXPECT_EQ(SSL_CTX_get_min_proto_version(ok.get()), DTLS1_VERSION);
  EXPECT_EQ(SSL_CTX_get_max_proto_version(ok.get()), DTLS1_2_VERSION);
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// The policy file is read once per path, so every |SSL_CTX_new| after the first
// costs no I/O. Overwriting the file in place is therefore not picked up, while
// a policy at a different path -- which is how the AWSLC_CRYPTO_POLICY_FILE
// override reaches us -- is.
TEST_F(CryptoPolicyTest, PolicyFileIsReadOncePerPath) {
  static const char kRaisedFloor[] = "TLS.MinProtocol = TLSv1.3\n";

  TemporaryFile policy;
  ASSERT_TRUE(policy.Init("TLS.MinProtocol = TLSv1.2\n"));
  TemporaryFile other;
  ASSERT_TRUE(other.Init(kRaisedFloor));

  // All three contexts are created up front: the cache holds one entry, and
  // |SSL_CTX_new| seeds from the fixture's path, which would evict it.
  bssl::UniquePtr<SSL_CTX> first(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> same_path(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> new_path(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(first);
  ASSERT_TRUE(same_path);
  ASSERT_TRUE(new_path);

  ssl_ctx_apply_crypto_policy(first.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);
  ASSERT_EQ(SSL_CTX_get_min_proto_version(first.get()), TLS1_2_VERSION);

  const size_t len = sizeof(kRaisedFloor) - 1;
  ScopedFILE f = policy.Open("w");
  ASSERT_TRUE(f);
  ASSERT_EQ(fwrite(kRaisedFloor, 1, len, f.get()), len);
  f.reset();

  ssl_ctx_apply_crypto_policy(same_path.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);
  EXPECT_EQ(SSL_CTX_get_min_proto_version(same_path.get()), TLS1_2_VERSION);

  ssl_ctx_apply_crypto_policy(new_path.get(), other.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);
  EXPECT_EQ(SSL_CTX_get_min_proto_version(new_path.get()), TLS1_3_VERSION);
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// A bound the policy supplies alone must still be checked against the bound the
// context already has, or a one-sided directive can invert the range by itself.
TEST_F(CryptoPolicyTest, OneSidedBoundBelowExistingFloorIsIgnored) {
  const std::string content =
      "TLS.MinProtocol = TLSv1.3\n"
      "TLS.MaxProtocol = TLSv1.3\n";
  TemporaryFile policy;
  ASSERT_TRUE(policy.Init(content));

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ssl_ctx_apply_crypto_policy(ctx.get(), policy.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);
  ASSERT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), TLS1_3_VERSION);

  // The context now has a TLS 1.3 floor. A policy naming only a TLS 1.2 ceiling
  // would drop below it, so it must be refused.
  const std::string ceiling_only = "TLS.MaxProtocol = TLSv1.2\n";
  TemporaryFile second;
  ASSERT_TRUE(second.Init(ceiling_only));
  ssl_ctx_apply_crypto_policy(ctx.get(), second.path().c_str(),
                              /*is_dtls=*/false, /*version_locked=*/false);
  EXPECT_EQ(ctx->conf_min_version, TLS1_3_VERSION);
  EXPECT_EQ(ctx->conf_max_version, TLS1_3_VERSION);
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// CryptoPolicySystemTest runs against the policy file the host actually has,
// with seeding live: no environment override, so |SSL_CTX_new| reads the path a
// real consumer would. Every other test here writes its own fixture file and so
// can only confirm AWS-LC's reading of a policy the test itself composed;
// nothing there notices when the framework writes something AWS-LC mishandles.
//
// AWSLC_CRYPTO_POLICY_TEST_REQUIRE_SYSTEM, which the Amazon Linux 2023 CI job
// sets, makes a missing file a failure. Without it the suite skips, since most
// hosts have no crypto-policies installation.
class CryptoPolicySystemTest : public ::testing::Test {
 protected:
  void SetUp() override {
    // Copied, not aliased: the path may point into the environment block, which
    // a later |setenv| is free to move.
    path_ = ssl_crypto_policy_default_path();
    if (!ssl_crypto_policy_parse_file(path_.c_str(), &cfg_)) {
      if (getenv("AWSLC_CRYPTO_POLICY_TEST_REQUIRE_SYSTEM") != nullptr) {
        FAIL() << "no readable crypto-policies file at " << path_;
      }
      GTEST_SKIP() << "no crypto-policies file at " << path_;
    }
  }

  std::string path_;
  CryptoPolicyConfig cfg_ = {};
};

TEST_F(CryptoPolicySystemTest, SeedsVersionBoundsAndCiphers) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  ASSERT_GT(sk_SSL_CIPHER_num(SSL_CTX_get_ciphers(ctx.get())), 0u);

  const uint16_t min_version = PolicyProtoVersion(cfg_.tls_min);
  const uint16_t max_version = PolicyProtoVersion(cfg_.tls_max);
  if (min_version != 0) {
    EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), min_version);
  }
  if (max_version != 0) {
    EXPECT_EQ(SSL_CTX_get_max_proto_version(ctx.get()), max_version);
  }

  // Seeding at |SSL_CTX_new| must come to the same thing as applying the file
  // by hand. The reference context starts unseeded, so a difference here is in
  // the wiring rather than in the reading -- the half no fixture file checks.
  ScopedEnv env("AWSLC_CRYPTO_POLICY_FILE");
  env.Set(kNoSuchPath);
  bssl::UniquePtr<SSL_CTX> ref(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ref);
  ssl_ctx_apply_crypto_policy(ref.get(), path_.c_str(), /*is_dtls=*/false,
                              /*version_locked=*/false);
  EXPECT_EQ(CipherNames(ctx.get()), CipherNames(ref.get()));
  EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()),
            SSL_CTX_get_min_proto_version(ref.get()));
  EXPECT_EQ(SSL_CTX_get_max_proto_version(ctx.get()),
            SSL_CTX_get_max_proto_version(ref.get()));
  EXPECT_EQ(ERR_peek_error(), 0u);
}

// A fixture is written to be resolvable, so nothing above notices when
// crypto-policies spells a group in a way AWS-LC cannot read. Every group and
// signature algorithm the system policy asks for that AWS-LC implements must
// survive into the seeded context.
TEST_F(CryptoPolicySystemTest, SeedsGroupsAndSigalgs) {
  static const struct {
    const char *name;
    uint16_t id;
  } kGroups[] = {
      {"X25519", SSL_GROUP_X25519},
      {"secp256r1", SSL_GROUP_SECP256R1},
      {"secp384r1", SSL_GROUP_SECP384R1},
      {"secp521r1", SSL_GROUP_SECP521R1},
  };
  static const struct {
    const char *name;
    uint16_t id;
  } kSigalgs[] = {
      {"ECDSA+SHA256", SSL_SIGN_ECDSA_SECP256R1_SHA256},
      {"ECDSA+SHA384", SSL_SIGN_ECDSA_SECP384R1_SHA384},
      {"ECDSA+SHA512", SSL_SIGN_ECDSA_SECP521R1_SHA512},
      {"ed25519", SSL_SIGN_ED25519},
      {"rsa_pss_rsae_sha256", SSL_SIGN_RSA_PSS_RSAE_SHA256},
      {"RSA+SHA256", SSL_SIGN_RSA_PKCS1_SHA256},
  };

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);

  for (const auto &group : kGroups) {
    if (PolicyRequests(cfg_.groups, group.name)) {
      EXPECT_TRUE(Contains(ctx->supported_group_list, group.id)) << group.name;
    }
  }
  for (const auto &sigalg : kSigalgs) {
    if (PolicyRequests(cfg_.sigalgs, sigalg.name)) {
      EXPECT_TRUE(Contains(ctx->verify_sigalgs, sigalg.id)) << sigalg.name;
      EXPECT_TRUE(Contains(ctx->cert->sigalgs, sigalg.id)) << sigalg.name;
    }
  }
  EXPECT_EQ(ERR_peek_error(), 0u);
}

TEST_F(CryptoPolicySystemTest, SeedsDTLSVersionBounds) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(DTLS_method()));
  ASSERT_TRUE(ctx);

  const uint16_t min_version = PolicyProtoVersion(cfg_.dtls_min);
  const uint16_t max_version = PolicyProtoVersion(cfg_.dtls_max);
  if (min_version != 0) {
    EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), min_version);
  }
  if (max_version != 0) {
    EXPECT_EQ(SSL_CTX_get_max_proto_version(ctx.get()), max_version);
  }
  EXPECT_EQ(ERR_peek_error(), 0u);
}

BSSL_NAMESPACE_END

#endif  // AWSLC_CRYPTO_POLICIES
