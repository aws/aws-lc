// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/ssl.h>

#include "internal.h"

// This file implements opt-in seeding of new |SSL_CTX| objects from the system
// crypto-policies OpenSSL back-end (Amazon Linux 2023 and Fedora). It is only
// compiled with -DENABLE_CRYPTO_POLICIES; otherwise it is an (almost) empty
// translation unit. |internal.h| is included unconditionally so the unit always
// carries declarations and never trips empty-translation-unit diagnostics.

#if defined(AWSLC_CRYPTO_POLICIES)

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <string>

#include <openssl/err.h>

BSSL_NAMESPACE_BEGIN

namespace {

// TrimAsciiWhitespace returns |s| with leading and trailing spaces, tabs,
// carriage returns, and newlines removed.
std::string TrimAsciiWhitespace(const std::string &s) {
  size_t start = 0, end = s.size();
  auto is_ws = [](char c) {
    return c == ' ' || c == '\t' || c == '\r' || c == '\n';
  };
  while (start < end && is_ws(s[start])) {
    start++;
  }
  while (end > start && is_ws(s[end - 1])) {
    end--;
  }
  return s.substr(start, end - start);
}

// CryptoPolicyProtoVersion maps a crypto-policies protocol token (e.g.
// "TLSv1.2", "DTLSv1.2") to the corresponding AWS-LC version constant, or 0 if
// the token is unrecognized or unsupported (e.g. "DTLSv1.3", for which AWS-LC
// has no constant).
uint16_t CryptoPolicyProtoVersion(const std::string &tok, bool is_dtls) {
  if (is_dtls) {
    if (tok == "DTLSv1" || tok == "DTLSv1.0") {
      return DTLS1_VERSION;
    }
    if (tok == "DTLSv1.2") {
      return DTLS1_2_VERSION;
    }
    return 0;
  }
  if (tok == "TLSv1" || tok == "TLSv1.0") {
    return TLS1_VERSION;
  }
  if (tok == "TLSv1.1") {
    return TLS1_1_VERSION;
  }
  if (tok == "TLSv1.2") {
    return TLS1_2_VERSION;
  }
  if (tok == "TLSv1.3") {
    return TLS1_3_VERSION;
  }
  return 0;
}

}  // namespace

bool ssl_crypto_policy_parse_file(const char *path, CryptoPolicyConfig *out) {
  if (path == nullptr || out == nullptr) {
    return false;
  }

  FILE *f = fopen(path, "r");
  if (f == nullptr) {
    return false;
  }

  char buf[8192];
  while (fgets(buf, sizeof(buf), f) != nullptr) {
    size_t len = strlen(buf);
    bool had_newline = len > 0 && buf[len - 1] == '\n';
    // Skip over-long lines: if the buffer filled without reaching a newline and
    // we are not at end-of-file, consume the rest of the line and ignore it.
    if (!had_newline && feof(f) == 0) {
      int c;
      while ((c = fgetc(f)) != EOF && c != '\n') {
      }
      continue;
    }

    std::string line(buf, len);
    // Trim leading whitespace so indented directives and section fragments are
    // recognized.
    size_t s = 0;
    while (s < line.size() && (line[s] == ' ' || line[s] == '\t')) {
      s++;
    }
    line.erase(0, s);
    if (line.empty() || line[0] == '#' || line[0] == '[') {
      continue;
    }

    size_t eq = line.find('=');
    if (eq == std::string::npos) {
      continue;
    }
    std::string key = TrimAsciiWhitespace(line.substr(0, eq));
    std::string val = TrimAsciiWhitespace(line.substr(eq + 1));
    // Strip a single pair of surrounding quotes, if present.
    if (val.size() >= 2 && (val.front() == '"' || val.front() == '\'') &&
        val.front() == val.back()) {
      val = val.substr(1, val.size() - 2);
    }

    // Recognized directives; the last occurrence of a key wins. Unknown keys
    // are ignored.
    if (key == "CipherString") {
      out->cipher_string = val;
    } else if (key == "Ciphersuites") {
      out->ciphersuites = val;
    } else if (key == "TLS.MinProtocol") {
      out->tls_min = val;
    } else if (key == "TLS.MaxProtocol") {
      out->tls_max = val;
    } else if (key == "DTLS.MinProtocol") {
      out->dtls_min = val;
    } else if (key == "DTLS.MaxProtocol") {
      out->dtls_max = val;
    } else if (key == "SignatureAlgorithms") {
      out->sigalgs = val;
    } else if (key == "Groups") {
      out->groups = val;
    }
  }

  fclose(f);
  return true;
}

const char *ssl_crypto_policy_default_path(void) {
  const char *env = getenv("AWSLC_CRYPTO_POLICY_FILE");
  if (env != nullptr && env[0] != '\0') {
    return env;
  }
  return AWSLC_CRYPTO_POLICY_PATH;
}

void ssl_ctx_apply_crypto_policy(SSL_CTX *ctx, const char *path, bool is_dtls) {
  if (ctx == nullptr || path == nullptr) {
    return;
  }

  CryptoPolicyConfig cfg;
  if (!ssl_crypto_policy_parse_file(path, &cfg)) {
    // Missing or unreadable policy file: keep the built-in defaults.
    ERR_clear_error();
    return;
  }

  // CipherString. crypto-policies emits a leading "@SECLEVEL=N" token; AWS-LC
  // has no security levels and its cipher-list parser rejects '@' rules other
  // than "@STRENGTH", so the token must be stripped before the remainder is
  // applied. The non-strict setter is used deliberately so cipher aliases
  // AWS-LC does not recognize (e.g. "kEECDH", "-aDSS") are skipped rather than
  // fatal.
  if (!cfg.cipher_string.empty()) {
    const char *cs = cfg.cipher_string.c_str();
    if (strncmp(cs, "@SECLEVEL=", 10) == 0) {
      const char *colon = strchr(cs, ':');
      cs = colon != nullptr ? colon + 1 : "";
    }
    if (*cs != '\0' && !SSL_CTX_set_cipher_list(ctx, cs)) {
      ERR_clear_error();
    }
  }

  // Ciphersuites (TLS 1.3).
  if (!cfg.ciphersuites.empty() &&
      !SSL_CTX_set_ciphersuites(ctx, cfg.ciphersuites.c_str())) {
    ERR_clear_error();
  }

  // Protocol version floor/ceiling. Select TLS.* vs DTLS.* per the method.
  const std::string &min_tok = is_dtls ? cfg.dtls_min : cfg.tls_min;
  const std::string &max_tok = is_dtls ? cfg.dtls_max : cfg.tls_max;
  if (!min_tok.empty()) {
    uint16_t v = CryptoPolicyProtoVersion(min_tok, is_dtls);
    if (v != 0 && !SSL_CTX_set_min_proto_version(ctx, v)) {
      ERR_clear_error();
    }
  }
  if (!max_tok.empty()) {
    uint16_t v = CryptoPolicyProtoVersion(max_tok, is_dtls);
    if (v != 0 && !SSL_CTX_set_max_proto_version(ctx, v)) {
      ERR_clear_error();
    }
  }

  // SignatureAlgorithms. Note: the setter rejects the whole list on the first
  // unrecognized token, so a single unsupported algorithm drops the directive
  // and leaves the built-in default in place.
  if (!cfg.sigalgs.empty() &&
      !SSL_CTX_set1_sigalgs_list(ctx, cfg.sigalgs.c_str())) {
    ERR_clear_error();
  }

  // Groups. Same all-or-nothing behavior as SignatureAlgorithms.
  if (!cfg.groups.empty() &&
      !SSL_CTX_set1_groups_list(ctx, cfg.groups.c_str())) {
    ERR_clear_error();
  }
}

BSSL_NAMESPACE_END

#endif  // AWSLC_CRYPTO_POLICIES
