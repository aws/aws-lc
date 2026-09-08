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

#if !defined(OPENSSL_WINDOWS)
#include <unistd.h>
#endif

#include <openssl/err.h>

BSSL_NAMESPACE_BEGIN

namespace {

// IsAsciiWhitespace matches the horizontal and line-ending whitespace that can
// appear around a directive in an OpenSSL config file.
bool IsAsciiWhitespace(char c) {
  return c == ' ' || c == '\t' || c == '\r' || c == '\n';
}

// CopyPolicyValue copies the |len| bytes at |value| into |out|, which has
// capacity |out_size| including the NUL terminator. It returns true on success.
// An overlong value is rejected rather than truncated, leaving |out| untouched.
bool CopyPolicyValue(char *out, size_t out_size, const char *value,
                     size_t len) {
  if (len >= out_size) {
    return false;
  }
  OPENSSL_memcpy(out, value, len);
  out[len] = '\0';
  return true;
}

// CryptoPolicyProtoVersion maps a crypto-policies protocol token (e.g.
// "TLSv1.2", "DTLSv1.2") to the corresponding AWS-LC version constant, or 0 if
// the token is unrecognized or unsupported (e.g. "DTLSv1.3", for which AWS-LC
// has no constant).
uint16_t CryptoPolicyProtoVersion(const char *tok, bool is_dtls) {
  if (is_dtls) {
    if (strcmp(tok, "DTLSv1") == 0 || strcmp(tok, "DTLSv1.0") == 0) {
      return DTLS1_VERSION;
    }
    if (strcmp(tok, "DTLSv1.2") == 0) {
      return DTLS1_2_VERSION;
    }
    return 0;
  }
  if (strcmp(tok, "TLSv1") == 0 || strcmp(tok, "TLSv1.0") == 0) {
    return TLS1_VERSION;
  }
  if (strcmp(tok, "TLSv1.1") == 0) {
    return TLS1_1_VERSION;
  }
  if (strcmp(tok, "TLSv1.2") == 0) {
    return TLS1_2_VERSION;
  }
  if (strcmp(tok, "TLSv1.3") == 0) {
    return TLS1_3_VERSION;
  }
  return 0;
}

// CipherRuleIsUsable reports whether |rule| yields a non-empty cipher list for
// |ctx| under the same parameters the corresponding public setter would use.
//
// This check exists because a failing |SSL_CTX_set_cipher_list| is not a no-op:
// |ssl_create_cipher_list| installs its result, empty or not, before reporting
// failure, and the |update_cipher_list| call that merges the TLS 1.3 suites back
// in is then skipped. Applying a rule blind and ignoring the return value would
// leave |ctx| with no ciphers at all rather than the built-in defaults, so the
// rule is evaluated into a throwaway list first and only applied if it holds up.
bool CipherRuleIsUsable(const SSL_CTX *ctx, const char *rule,
                        bool config_tls13) {
  const bool has_aes_hw = ctx->aes_hw_override ? ctx->aes_hw_override_value
                                               : EVP_has_aes_hardware();
  UniquePtr<SSLCipherPreferenceList> probe;
  return ssl_create_cipher_list(&probe, has_aes_hw, rule,
                                false /* not strict */, config_tls13);
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

    // Trim leading whitespace so indented directives are recognized, then skip
    // blank lines, comments, and section headers.
    const char *line = buf;
    while (*line == ' ' || *line == '\t') {
      line++;
    }
    if (*line == '\0' || *line == '\n' || *line == '#' || *line == '[') {
      continue;
    }

    const char *eq = strchr(line, '=');
    if (eq == nullptr) {
      continue;
    }

    // Trim whitespace off both sides of the key.
    const char *key = line;
    const char *key_end = eq;
    while (key < key_end && IsAsciiWhitespace(*key)) {
      key++;
    }
    while (key_end > key && IsAsciiWhitespace(key_end[-1])) {
      key_end--;
    }

    // Trim whitespace off both sides of the value, then strip a single pair of
    // surrounding quotes if present.
    const char *val = eq + 1;
    const char *val_end = line + strlen(line);
    while (val < val_end && IsAsciiWhitespace(*val)) {
      val++;
    }
    while (val_end > val && IsAsciiWhitespace(val_end[-1])) {
      val_end--;
    }
    if (val_end - val >= 2 && (*val == '"' || *val == '\'') &&
        *val == val_end[-1]) {
      val++;
      val_end--;
    }

    const size_t key_len = static_cast<size_t>(key_end - key);
    const size_t val_len = static_cast<size_t>(val_end - val);

    // KeyIs compares the trimmed key against a literal directive name.
    auto key_is = [key, key_len](const char *name) {
      return strlen(name) == key_len && OPENSSL_memcmp(key, name, key_len) == 0;
    };

    // Recognized directives; the last occurrence of a key wins. Unknown keys,
    // and values too long to represent, are ignored.
    if (key_is("CipherString")) {
      CopyPolicyValue(out->cipher_string, sizeof(out->cipher_string), val,
                      val_len);
    } else if (key_is("Ciphersuites")) {
      CopyPolicyValue(out->ciphersuites, sizeof(out->ciphersuites), val,
                      val_len);
    } else if (key_is("TLS.MinProtocol")) {
      CopyPolicyValue(out->tls_min, sizeof(out->tls_min), val, val_len);
    } else if (key_is("TLS.MaxProtocol")) {
      CopyPolicyValue(out->tls_max, sizeof(out->tls_max), val, val_len);
    } else if (key_is("DTLS.MinProtocol")) {
      CopyPolicyValue(out->dtls_min, sizeof(out->dtls_min), val, val_len);
    } else if (key_is("DTLS.MaxProtocol")) {
      CopyPolicyValue(out->dtls_max, sizeof(out->dtls_max), val, val_len);
    } else if (key_is("SignatureAlgorithms")) {
      CopyPolicyValue(out->sigalgs, sizeof(out->sigalgs), val, val_len);
    } else if (key_is("Groups")) {
      CopyPolicyValue(out->groups, sizeof(out->groups), val, val_len);
    }
  }

  fclose(f);
  return true;
}

const char *ssl_crypto_policy_default_path(void) {
  // The compile-time default is a root-owned file under /etc; the environment is
  // not. Honoring the override in a set-uid or set-gid process would let an
  // unprivileged caller choose the TLS policy that privileged process runs
  // under, so the override is dropped across a privilege boundary.
  //
  // This compares the real and effective ids rather than using glibc's
  // secure_getenv so that no libc feature detection is needed. It therefore does
  // not catch the rarer AT_SECURE cases that leave the ids equal, such as file
  // capabilities; a packager shipping such a binary should build with
  // -DAWSLC_CRYPTO_POLICY_PATH and treat the compile-time path as the only one.
#if !defined(OPENSSL_WINDOWS)
  if (getuid() != geteuid() || getgid() != getegid()) {
    return AWSLC_CRYPTO_POLICY_PATH;
  }
#endif
  const char *env = getenv("AWSLC_CRYPTO_POLICY_FILE");
  if (env != nullptr && env[0] != '\0') {
    return env;
  }
  return AWSLC_CRYPTO_POLICY_PATH;
}

void ssl_ctx_apply_crypto_policy(SSL_CTX *ctx, const char *path, bool is_dtls,
                                 bool version_locked) {
  if (ctx == nullptr || path == nullptr) {
    return;
  }

  // Seeding is best-effort, so every failure below is swallowed. Mark the queue
  // first and pop back to the mark on the way out: |ERR_clear_error| would also
  // discard whatever the caller had queued before calling us. With an empty
  // queue no mark is set and |ERR_pop_to_mark| removes everything, which is the
  // same result.
  ERR_set_mark();

  CryptoPolicyConfig cfg = {};
  if (!ssl_crypto_policy_parse_file(path, &cfg)) {
    // Missing or unreadable policy file: keep the built-in defaults.
    ERR_pop_to_mark();
    return;
  }

  // CipherString. crypto-policies emits a leading "@SECLEVEL=N" token; AWS-LC
  // has no security levels and its cipher-list parser rejects '@' rules other
  // than "@STRENGTH", so the token must be stripped before the remainder is
  // applied. The non-strict setter is used deliberately so cipher aliases
  // AWS-LC does not recognize (e.g. "kEECDH", "-aDSS") are skipped rather than
  // fatal.
  if (cfg.cipher_string[0] != '\0') {
    const char *cs = cfg.cipher_string;
    if (strncmp(cs, "@SECLEVEL=", 10) == 0) {
      const char *colon = strchr(cs, ':');
      cs = colon != nullptr ? colon + 1 : "";
    }
    if (*cs != '\0' && CipherRuleIsUsable(ctx, cs, /*config_tls13=*/false)) {
      SSL_CTX_set_cipher_list(ctx, cs);
    }
  }

  // Ciphersuites (TLS 1.3).
  if (cfg.ciphersuites[0] != '\0' &&
      CipherRuleIsUsable(ctx, cfg.ciphersuites, /*config_tls13=*/true)) {
    SSL_CTX_set_ciphersuites(ctx, cfg.ciphersuites);
  }

  // Protocol version floor/ceiling. Select TLS.* vs DTLS.* per the method.
  //
  // A version-locked SSL_METHOD (TLSv1_2_method and friends) is skipped
  // entirely. |SSL_CTX_new| pins such a context by setting both bounds to
  // |method->version|, but the public setters validate only against the protocol
  // method's full version range, so applying a policy here would quietly raise
  // the ceiling and hand the caller a version they deliberately excluded.
  if (!version_locked) {
    const char *min_tok = is_dtls ? cfg.dtls_min : cfg.tls_min;
    const char *max_tok = is_dtls ? cfg.dtls_max : cfg.tls_max;
    if (min_tok[0] != '\0') {
      uint16_t v = CryptoPolicyProtoVersion(min_tok, is_dtls);
      if (v != 0) {
        SSL_CTX_set_min_proto_version(ctx, v);
      }
    }
    if (max_tok[0] != '\0') {
      uint16_t v = CryptoPolicyProtoVersion(max_tok, is_dtls);
      if (v != 0) {
        SSL_CTX_set_max_proto_version(ctx, v);
      }
    }
  }

  // SignatureAlgorithms. Note: the setter rejects the whole list on the first
  // unrecognized token, so a single unsupported algorithm drops the directive
  // and leaves the built-in default in place. It does not modify |ctx| when it
  // fails.
  if (cfg.sigalgs[0] != '\0') {
    SSL_CTX_set1_sigalgs_list(ctx, cfg.sigalgs);
  }

  // Groups. Same all-or-nothing behavior as SignatureAlgorithms.
  if (cfg.groups[0] != '\0') {
    SSL_CTX_set1_groups_list(ctx, cfg.groups);
  }

  ERR_pop_to_mark();
}

BSSL_NAMESPACE_END

#endif  // AWSLC_CRYPTO_POLICIES
