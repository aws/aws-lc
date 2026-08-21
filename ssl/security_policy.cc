// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/ssl.h>

#include <ctype.h>
#include <stdio.h>
#include <string.h>

#include <algorithm>
#include <map>
#include <sstream>
#include <string>
#include <vector>

#include <openssl/crypto.h>
#include <openssl/err.h>

#include "internal.h"

BSSL_NAMESPACE_BEGIN

#if !defined(AWSLC_ENABLE_DISTRIBUTION_TLS_POLICY)

bool ssl_ctx_apply_distribution_tls_policy(SSL_CTX *ctx) {
  (void)ctx;
  return true;
}

void ssl_set_distribution_tls_policy_test_root(const char *path) { (void)path; }

#else

namespace {

struct DistributionPolicyCache {
  bool loaded = false;
  bool supported_distro = false;
  bool policy_found = false;
  bool has_min_version = false;
  uint16_t min_version = 0;
  bool has_max_version = false;
  uint16_t max_version = 0;
  bool has_cipher_string = false;
  std::string cipher_string;
  bool has_ciphersuites = false;
  std::string ciphersuites;
  std::string warnings;
};

struct PendingPolicy {
  bool has_min_version = false;
  std::string min_version;
  bool has_max_version = false;
  std::string max_version;
  bool has_cipher_string = false;
  std::string cipher_string;
  bool has_ciphersuites = false;
  std::string ciphersuites;
};

static struct CRYPTO_STATIC_MUTEX g_distribution_policy_lock =
    CRYPTO_STATIC_MUTEX_INIT;
static DistributionPolicyCache g_distribution_policy_cache;
#if defined(AWS_LC_TEST_ENV)
static std::string g_distribution_policy_test_root;
#endif

static std::string TrimASCII(const std::string &input) {
  size_t start = 0;
  while (start < input.size() &&
         isspace(static_cast<unsigned char>(input[start]))) {
    start++;
  }

  size_t end = input.size();
  while (end > start && isspace(static_cast<unsigned char>(input[end - 1]))) {
    end--;
  }

  return input.substr(start, end - start);
}

static std::string ToLowerASCII(const std::string &input) {
  std::string result = input;
  std::transform(result.begin(), result.end(), result.begin(),
                 [](unsigned char c) { return static_cast<char>(tolower(c)); });
  return result;
}

static std::string MaybeUnquote(const std::string &input) {
  if (input.size() >= 2 && ((input.front() == '"' && input.back() == '"') ||
                            (input.front() == '\'' && input.back() == '\''))) {
    return input.substr(1, input.size() - 2);
  }
  return input;
}

static std::string JoinRoot(const std::string &root, const char *path) {
  if (root.empty()) {
    return std::string(path);
  }
  return root + path;
}

static void AppendWarning(std::string *warnings, const std::string &warning) {
  if (!warnings->empty()) {
    warnings->append("; ");
  }
  warnings->append(warning);
}

static bool ReadFileToString(std::string *out, const std::string &path) {
  FILE *file = fopen(path.c_str(), "rb");
  if (file == nullptr) {
    return false;
  }

  out->clear();
  bool ok = true;
  for (;;) {
    char buffer[1024];
    const size_t bytes_read = fread(buffer, 1, sizeof(buffer), file);
    if (bytes_read > 0) {
      out->append(buffer, bytes_read);
    }
    if (bytes_read < sizeof(buffer)) {
      if (ferror(file)) {
        ok = false;
      }
      break;
    }
  }

  fclose(file);
  return ok;
}

static std::map<std::string, std::string> ParseAssignments(
    const std::string &contents) {
  std::map<std::string, std::string> values;
  std::istringstream stream(contents);
  std::string line;
  while (std::getline(stream, line)) {
    if (!line.empty() && line.back() == '\r') {
      line.pop_back();
    }
    const size_t comment = line.find('#');
    if (comment != std::string::npos) {
      line.resize(comment);
    }
    const size_t equals = line.find('=');
    if (equals == std::string::npos) {
      continue;
    }

    const std::string key = TrimASCII(line.substr(0, equals));
    if (key.empty()) {
      continue;
    }
    const std::string value = TrimASCII(line.substr(equals + 1));
    values[key] = MaybeUnquote(value);
  }
  return values;
}

static bool ParseProtocolVersionString(uint16_t *out,
                                       const std::string &value) {
  if (value == "TLSv1") {
    *out = TLS1_VERSION;
    return true;
  }
  if (value == "TLSv1.1") {
    *out = TLS1_1_VERSION;
    return true;
  }
  if (value == "TLSv1.2") {
    *out = TLS1_2_VERSION;
    return true;
  }
  if (value == "TLSv1.3") {
    *out = TLS1_3_VERSION;
    return true;
  }
  return false;
}

static const char *ProtocolVersionString(uint16_t version) {
  switch (version) {
    case TLS1_VERSION:
      return "TLSv1";
    case TLS1_1_VERSION:
      return "TLSv1.1";
    case TLS1_2_VERSION:
      return "TLSv1.2";
    case TLS1_3_VERSION:
      return "TLSv1.3";
    default:
      return "unknown";
  }
}

static std::vector<std::string> SplitOnColon(const std::string &value) {
  std::vector<std::string> tokens;
  size_t start = 0;
  for (;;) {
    size_t end = value.find(':', start);
    std::string token = TrimASCII(value.substr(start, end - start));
    if (!token.empty()) {
      tokens.push_back(token);
    }
    if (end == std::string::npos) {
      break;
    }
    start = end + 1;
  }
  return tokens;
}

static std::string JoinWithColon(const std::vector<std::string> &tokens) {
  std::string result;
  for (size_t i = 0; i < tokens.size(); i++) {
    if (i > 0) {
      result.push_back(':');
    }
    result.append(tokens[i]);
  }
  return result;
}

static bool IsSupportedTLS13Cipher(const std::string &token) {
  return token == "TLS_AES_128_GCM_SHA256" ||
         token == "TLS_AES_256_GCM_SHA384" ||
         token == "TLS_CHACHA20_POLY1305_SHA256";
}

static std::string SanitizeCipherString(const std::string &value,
                                        std::string *warnings) {
  std::vector<std::string> sanitized;
  for (std::string token : SplitOnColon(value)) {
    const size_t security_level = token.find("@SECLEVEL=");
    if (security_level != std::string::npos) {
      AppendWarning(warnings,
                    std::string("ignored unsupported CipherString fragment '") +
                        token + "'");
      token = TrimASCII(token.substr(0, security_level));
      if (token.empty()) {
        continue;
      }
    }
    sanitized.push_back(token);
  }
  return JoinWithColon(sanitized);
}

static std::string SanitizeTLS13Ciphersuites(const std::string &value,
                                             std::string *warnings) {
  std::vector<std::string> sanitized;
  for (const std::string &token : SplitOnColon(value)) {
    if (IsSupportedTLS13Cipher(token)) {
      sanitized.push_back(token);
    } else {
      AppendWarning(warnings,
                    std::string("ignored unsupported Ciphersuites entry '") +
                        token + "'");
    }
  }
  return JoinWithColon(sanitized);
}

static void ParsePolicyFile(const std::string &contents,
                            DistributionPolicyCache *out) {
  PendingPolicy pending;
  std::istringstream stream(contents);
  std::string line;
  while (std::getline(stream, line)) {
    if (!line.empty() && line.back() == '\r') {
      line.pop_back();
    }

    const size_t comment = line.find('#');
    if (comment != std::string::npos) {
      line.resize(comment);
    }
    line = TrimASCII(line);
    if (line.empty()) {
      continue;
    }
    if (line.front() == '[' && line.back() == ']') {
      continue;
    }

    const size_t equals = line.find('=');
    if (equals == std::string::npos) {
      AppendWarning(
          &out->warnings,
          std::string("ignored malformed policy line '") + line + "'");
      continue;
    }

    const std::string key = TrimASCII(line.substr(0, equals));
    const std::string value = TrimASCII(line.substr(equals + 1));
    if (key.empty()) {
      AppendWarning(
          &out->warnings,
          std::string("ignored malformed policy line '") + line + "'");
      continue;
    }

    if (key == "MinProtocol" || key == "TLS.MinProtocol") {
      pending.has_min_version = true;
      pending.min_version = value;
      continue;
    }
    if (key == "MaxProtocol" || key == "TLS.MaxProtocol") {
      pending.has_max_version = true;
      pending.max_version = value;
      continue;
    }
    if (key == "CipherString") {
      pending.has_cipher_string = true;
      pending.cipher_string = value;
      continue;
    }
    if (key == "Ciphersuites") {
      pending.has_ciphersuites = true;
      pending.ciphersuites = value;
      continue;
    }

    AppendWarning(
        &out->warnings,
        std::string("ignored unsupported policy directive '") + key + "'");
  }

  if (pending.has_min_version) {
    if (!pending.min_version.empty() &&
        ParseProtocolVersionString(&out->min_version, pending.min_version)) {
      out->has_min_version = true;
    } else {
      AppendWarning(&out->warnings,
                    std::string("ignored invalid MinProtocol value '") +
                        pending.min_version + "'");
    }
  }

  if (pending.has_max_version) {
    if (!pending.max_version.empty() &&
        ParseProtocolVersionString(&out->max_version, pending.max_version)) {
      out->has_max_version = true;
    } else {
      AppendWarning(&out->warnings,
                    std::string("ignored invalid MaxProtocol value '") +
                        pending.max_version + "'");
    }
  }

  if (pending.has_cipher_string) {
    if (pending.cipher_string.empty()) {
      AppendWarning(&out->warnings, "ignored empty CipherString directive");
    } else {
      out->cipher_string =
          SanitizeCipherString(pending.cipher_string, &out->warnings);
      out->has_cipher_string = !out->cipher_string.empty();
    }
  }

  if (pending.has_ciphersuites) {
    if (pending.ciphersuites.empty()) {
      AppendWarning(&out->warnings, "ignored empty Ciphersuites directive");
    } else {
      out->ciphersuites =
          SanitizeTLS13Ciphersuites(pending.ciphersuites, &out->warnings);
      out->has_ciphersuites = !out->ciphersuites.empty();
    }
  }
}

static bool IsAmazonLinux2023(const std::string &root) {
  std::string cpe;
  if (ReadFileToString(&cpe, JoinRoot(root, "/etc/amazon-linux-release-cpe"))) {
    const std::string lowered = ToLowerASCII(cpe);
    if (lowered.find("amazon") != std::string::npos &&
        lowered.find("2023") != std::string::npos) {
      return true;
    }
  }

  std::string os_release;
  if (!ReadFileToString(&os_release, JoinRoot(root, "/etc/os-release"))) {
    return false;
  }
  const std::map<std::string, std::string> values =
      ParseAssignments(os_release);
  const auto id_iter = values.find("ID");
  const auto version_iter = values.find("VERSION_ID");
  if (id_iter == values.end() || version_iter == values.end()) {
    return false;
  }
  return ToLowerASCII(id_iter->second) == "amzn" &&
         version_iter->second == "2023";
}

static bool IsFedora(const std::string &root) {
  std::string os_release;
  if (!ReadFileToString(&os_release, JoinRoot(root, "/etc/os-release"))) {
    return false;
  }
  const std::map<std::string, std::string> values =
      ParseAssignments(os_release);
  const auto id_iter = values.find("ID");
  return id_iter != values.end() && ToLowerASCII(id_iter->second) == "fedora";
}

static bool LoadPolicyFile(std::string *contents, const std::string &root) {
  static const char *kCandidates[] = {
      "/etc/crypto-policies/back-ends/opensslcnf.config",
      "/etc/crypto-policies/back-ends/openssl.config",
  };

  for (const char *candidate : kCandidates) {
    if (ReadFileToString(contents, JoinRoot(root, candidate))) {
      return true;
    }
  }
  return false;
}

static const char *DefaultTLS13Ciphersuites(const SSL_CTX *ctx) {
  const bool has_aes_hw = ctx->aes_hw_override ? ctx->aes_hw_override_value
                                               : EVP_has_aes_hardware();
  return has_aes_hw ? TLS13_DEFAULT_CIPHER_LIST_AES_HW
                    : TLS13_DEFAULT_CIPHER_LIST_NO_AES_HW;
}

static std::string CurrentPolicyRootLocked() {
#if defined(AWS_LC_TEST_ENV)
  return g_distribution_policy_test_root;
#else
  return std::string();
#endif
}

static DistributionPolicyCache LoadDistributionPolicyLocked() {
  DistributionPolicyCache cache;
  cache.loaded = true;

  const std::string root = CurrentPolicyRootLocked();
#if defined(AWS_LC_TEST_ENV)
  if (root.empty()) {
    return cache;
  }
#endif

  if (IsAmazonLinux2023(root) || IsFedora(root)) {
    cache.supported_distro = true;
  } else {
    return cache;
  }

  std::string contents;
  if (!LoadPolicyFile(&contents, root)) {
    return cache;
  }

  cache.policy_found = true;
  ParsePolicyFile(contents, &cache);
  return cache;
}

static DistributionPolicyCache GetDistributionPolicy() {
  CRYPTO_STATIC_MUTEX_lock_write(&g_distribution_policy_lock);
  if (!g_distribution_policy_cache.loaded) {
    g_distribution_policy_cache = LoadDistributionPolicyLocked();
  }
  DistributionPolicyCache cache = g_distribution_policy_cache;
  CRYPTO_STATIC_MUTEX_unlock_write(&g_distribution_policy_lock);
  return cache;
}

static void ReportPolicyWarning(const std::string &warnings) {
  if (warnings.empty()) {
    return;
  }
  OPENSSL_PUT_ERROR(SSL, ERR_R_INTERNAL_ERROR);
  ERR_add_error_data(2, "distribution TLS policy: ", warnings.c_str());
}

}  // namespace

bool ssl_ctx_apply_distribution_tls_policy(SSL_CTX *ctx) {
  DistributionPolicyCache cache = GetDistributionPolicy();
  if (!cache.supported_distro || !cache.policy_found) {
    return true;
  }

  std::string warnings = cache.warnings;
  if (cache.has_min_version && cache.has_max_version &&
      cache.min_version > cache.max_version) {
    AppendWarning(&warnings,
                  std::string("ignored conflicting protocol bounds '") +
                      ProtocolVersionString(cache.min_version) + "' and '" +
                      ProtocolVersionString(cache.max_version) + "'");
  } else {
    if (cache.has_min_version &&
        !SSL_CTX_set_min_proto_version(ctx, cache.min_version)) {
      ERR_clear_error();
      (void)SSL_CTX_set_min_proto_version(ctx, 0);
      AppendWarning(&warnings, std::string("failed to apply MinProtocol '") +
                                   ProtocolVersionString(cache.min_version) +
                                   "'");
    }

    if (cache.has_max_version &&
        !SSL_CTX_set_max_proto_version(ctx, cache.max_version)) {
      ERR_clear_error();
      (void)SSL_CTX_set_max_proto_version(ctx, 0);
      AppendWarning(&warnings, std::string("failed to apply MaxProtocol '") +
                                   ProtocolVersionString(cache.max_version) +
                                   "'");
    }
  }

  if (cache.has_cipher_string &&
      !SSL_CTX_set_strict_cipher_list(ctx, cache.cipher_string.c_str())) {
    ERR_clear_error();
    (void)SSL_CTX_set_strict_cipher_list(ctx, SSL_DEFAULT_CIPHER_LIST);
    AppendWarning(&warnings, std::string("failed to apply CipherString '") +
                                 cache.cipher_string + "'");
  }

  if (cache.has_ciphersuites &&
      !SSL_CTX_set_ciphersuites(ctx, cache.ciphersuites.c_str())) {
    ERR_clear_error();
    (void)SSL_CTX_set_ciphersuites(ctx, DefaultTLS13Ciphersuites(ctx));
    AppendWarning(&warnings, std::string("failed to apply Ciphersuites '") +
                                 cache.ciphersuites + "'");
  }

  ReportPolicyWarning(warnings);
  return true;
}

void ssl_set_distribution_tls_policy_test_root(const char *path) {
#if defined(AWS_LC_TEST_ENV)
  CRYPTO_STATIC_MUTEX_lock_write(&g_distribution_policy_lock);
  g_distribution_policy_test_root = path == nullptr ? "" : path;
  g_distribution_policy_cache = DistributionPolicyCache();
  CRYPTO_STATIC_MUTEX_unlock_write(&g_distribution_policy_lock);
#else
  (void)path;
#endif
}

#endif  // AWSLC_ENABLE_DISTRIBUTION_TLS_POLICY

BSSL_NAMESPACE_END
