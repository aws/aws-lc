// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/ssl.h>

#include "internal.h"

// This file reads the system crypto-policies OpenSSL back-end (Amazon Linux 2023
// and Fedora). It is only compiled with -DENABLE_CRYPTO_POLICIES; otherwise it is
// an (almost) empty translation unit. |internal.h| is included unconditionally so
// the unit always carries declarations and never trips empty-translation-unit
// diagnostics.

#if defined(AWSLC_CRYPTO_POLICIES)

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if !defined(OPENSSL_WINDOWS)
#include <unistd.h>
#endif

#if defined(OPENSSL_LINUX)
#include "../crypto/fipsmodule/cpucap/cpu_getauxval_linux.h"
// AT_SECURE from the Linux kernel ABI (include/uapi/linux/auxvec.h); the shared
// helper defines only the entries its own callers use.
#if !defined(AT_SECURE)
#define AT_SECURE 23
#endif
#endif

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

  // |fgets| and |fgetc| stop on a read error exactly as they stop at end of
  // file, so without this a truncated read would pass for a whole policy.
  const bool ok = ferror(f) == 0;
  fclose(f);
  return ok;
}

const char *ssl_crypto_policy_default_path(void) {
  // The compile-time default is a root-owned file under /etc; the environment is
  // not. Honoring the override in a process that gained privileges on exec
  // would let an unprivileged caller choose the TLS policy that privileged
  // process runs under, so the override is dropped across a privilege boundary.
#if defined(OPENSSL_HAS_GETAUXVAL)
  // The kernel sets AT_SECURE for every secure execution and never clears it,
  // so this also covers what leaves the ids below equal: file capabilities, and
  // a set-uid program that has already dropped privileges.
  if (getauxval(AT_SECURE) != 0) {
    return AWSLC_CRYPTO_POLICY_DEFAULT_FILE;
  }
#endif
#if !defined(OPENSSL_WINDOWS)
  if (getuid() != geteuid() || getgid() != getegid()) {
    return AWSLC_CRYPTO_POLICY_DEFAULT_FILE;
  }
#endif
  const char *env = getenv("AWSLC_CRYPTO_POLICY_FILE");
  if (env != nullptr && env[0] != '\0') {
    return env;
  }
  return AWSLC_CRYPTO_POLICY_DEFAULT_FILE;
}

BSSL_NAMESPACE_END

#endif  // AWSLC_CRYPTO_POLICIES
