// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/ssl.h>

#include <errno.h>
#include <stdio.h>
#include <string.h>

#include <string>
#include <vector>

#include <gtest/gtest.h>

#include <openssl/err.h>

#include "../crypto/test/test_util.h"
#include "internal.h"

#if defined(OPENSSL_WINDOWS)
#include <direct.h>
#else
#include <sys/stat.h>
#endif

BSSL_NAMESPACE_BEGIN

#if defined(AWSLC_ENABLE_DISTRIBUTION_TLS_POLICY)

namespace {

static std::vector<std::string> CipherNames(
    const STACK_OF(SSL_CIPHER) *ciphers) {
  std::vector<std::string> names;
  for (size_t i = 0; i < sk_SSL_CIPHER_num(ciphers); i++) {
    names.push_back(SSL_CIPHER_get_name(sk_SSL_CIPHER_value(ciphers, i)));
  }
  return names;
}

static bool CreateDirectory(const std::string &path) {
#if defined(OPENSSL_WINDOWS)
  return _mkdir(path.c_str()) == 0 || errno == EEXIST;
#else
  return mkdir(path.c_str(), 0700) == 0 || errno == EEXIST;
#endif
}

static bool EnsureParentDirectories(const std::string &path) {
  size_t search_start = 0;
  while (true) {
    const size_t slash = path.find('/', search_start);
    if (slash == std::string::npos) {
      return true;
    }
    if (slash > 0 && !CreateDirectory(path.substr(0, slash))) {
      return false;
    }
    search_start = slash + 1;
  }
}

static std::string ReadSingleWarning() {
  const char *file = nullptr;
  const char *data = nullptr;
  int line = 0;
  int flags = 0;
  const uint32_t err = ERR_get_error_line_data(&file, &line, &data, &flags);
  EXPECT_NE(0u, err);
  EXPECT_EQ(ERR_LIB_SSL, ERR_GET_LIB(err));
  EXPECT_EQ(ERR_R_INTERNAL_ERROR, ERR_GET_REASON(err));
  EXPECT_EQ(0u, ERR_peek_error());
  if ((flags & ERR_TXT_STRING) == 0 || data == nullptr) {
    return std::string();
  }
  return data;
}

class SSLSystemPolicyTest : public testing::Test {
 protected:
  void SetUp() override {
    ASSERT_NE(static_cast<size_t>(0), createTempDirPath(root_buffer_));
    root_ = root_buffer_;
    ERR_clear_error();
  }

  void TearDown() override {
    ssl_set_distribution_tls_policy_test_root(nullptr);
    ERR_clear_error();
  }

  std::string RootPath(const std::string &suffix) const {
    return root_ + suffix;
  }

  void WriteFile(const std::string &suffix, const std::string &contents) {
    const std::string path = RootPath(suffix);
    ASSERT_TRUE(EnsureParentDirectories(path));
    FILE *file = fopen(path.c_str(), "wb");
    ASSERT_NE(nullptr, file);
    ASSERT_EQ(contents.size(),
              fwrite(contents.data(), 1, contents.size(), file));
    ASSERT_EQ(0, fclose(file));
  }

  void WriteAmazonLinux2023ReleaseFiles() {
    WriteFile("/etc/os-release", "ID=amzn\nVERSION_ID=2023\n");
  }

  void WriteFedoraReleaseFile() {
    WriteFile("/etc/os-release", "ID=fedora\nVERSION_ID=40\n");
  }

  void WritePolicy(const std::string &contents,
                   const std::string &name = "opensslcnf.config") {
    WriteFile("/etc/crypto-policies/back-ends/" + name, contents);
  }

  void UseTestRoot() {
    ssl_set_distribution_tls_policy_test_root(root_.c_str());
    ERR_clear_error();
  }

  char root_buffer_[PATH_MAX];
  std::string root_;
};

TEST_F(SSLSystemPolicyTest, AppliesAmazonLinux2023Policy) {
  WriteAmazonLinux2023ReleaseFiles();
  WritePolicy(
      "MinProtocol = TLSv1.2\n"
      "MaxProtocol = TLSv1.3\n"
      "CipherString = ECDHE-RSA-AES256-GCM-SHA384:ECDHE-RSA-AES128-GCM-SHA256\n"
      "Ciphersuites = TLS_AES_256_GCM_SHA384:TLS_AES_128_GCM_SHA256\n");
  UseTestRoot();

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  EXPECT_EQ(TLS1_2_VERSION, SSL_CTX_get_min_proto_version(ctx.get()));
  EXPECT_EQ(TLS1_3_VERSION, SSL_CTX_get_max_proto_version(ctx.get()));

  EXPECT_EQ((std::vector<std::string>{
                "TLS_AES_256_GCM_SHA384", "TLS_AES_128_GCM_SHA256",
                "ECDHE-RSA-AES256-GCM-SHA384", "ECDHE-RSA-AES128-GCM-SHA256"}),
            CipherNames(ctx->cipher_list->ciphers.get()));
  EXPECT_EQ((std::vector<std::string>{"TLS_AES_256_GCM_SHA384",
                                      "TLS_AES_128_GCM_SHA256"}),
            CipherNames(ctx->tls13_cipher_list->ciphers.get()));
  EXPECT_EQ(0u, ERR_peek_error());
}

TEST_F(SSLSystemPolicyTest, AcceptsFedoraBackendFormat) {
  WriteFedoraReleaseFile();
  WritePolicy("TLS.MinProtocol = TLSv1.2\n", "openssl.config");
  UseTestRoot();

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  EXPECT_EQ(TLS1_2_VERSION, SSL_CTX_get_min_proto_version(ctx.get()));
  EXPECT_EQ(0u, ERR_peek_error());
}

TEST_F(SSLSystemPolicyTest, InvalidCipherStringPreservesDefaultsAndWarns) {
  ssl_set_distribution_tls_policy_test_root(nullptr);
  bssl::UniquePtr<SSL_CTX> defaults(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(defaults);
  const std::vector<std::string> default_ciphers =
      CipherNames(defaults->cipher_list->ciphers.get());
  ERR_clear_error();

  WriteAmazonLinux2023ReleaseFiles();
  WritePolicy("CipherString = this-is-not-a-valid-cipher\n");
  UseTestRoot();

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  EXPECT_EQ(default_ciphers, CipherNames(ctx->cipher_list->ciphers.get()));

  const std::string warning = ReadSingleWarning();
  EXPECT_NE(std::string::npos, warning.find("CipherString"));
}

TEST_F(SSLSystemPolicyTest,
       UnsupportedDirectiveWarnsButAppliesSupportedSettings) {
  WriteAmazonLinux2023ReleaseFiles();
  WritePolicy("MinProtocol = TLSv1.2\nGroups = X25519:P-256\n");
  UseTestRoot();

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  EXPECT_EQ(TLS1_2_VERSION, SSL_CTX_get_min_proto_version(ctx.get()));

  const std::string warning = ReadSingleWarning();
  EXPECT_NE(std::string::npos, warning.find("Groups"));
}

TEST_F(SSLSystemPolicyTest, MissingPolicyFilesPreserveDefaults) {
  WriteAmazonLinux2023ReleaseFiles();
  UseTestRoot();

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  EXPECT_EQ(0, SSL_CTX_get_min_proto_version(ctx.get()));
  EXPECT_EQ(0, SSL_CTX_get_max_proto_version(ctx.get()));
  EXPECT_EQ(0u, ERR_peek_error());
}

TEST_F(SSLSystemPolicyTest, TestBuildDoesNotReadHostPolicyWithoutOverride) {
  WriteAmazonLinux2023ReleaseFiles();
  WritePolicy("MinProtocol = TLSv1.2\n");
  UseTestRoot();

  bssl::UniquePtr<SSL_CTX> ctx_with_override(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx_with_override);
  EXPECT_EQ(TLS1_2_VERSION,
            SSL_CTX_get_min_proto_version(ctx_with_override.get()));
  EXPECT_EQ(0u, ERR_peek_error());

  ssl_set_distribution_tls_policy_test_root(nullptr);
  bssl::UniquePtr<SSL_CTX> ctx_without_override(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx_without_override);
  EXPECT_EQ(0, SSL_CTX_get_min_proto_version(ctx_without_override.get()));
  EXPECT_EQ(0u, ERR_peek_error());
}

}  // namespace

#endif  // AWSLC_ENABLE_DISTRIBUTION_TLS_POLICY

BSSL_NAMESPACE_END
