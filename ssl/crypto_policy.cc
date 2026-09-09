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

#include "../crypto/err/internal.h"

#if defined(OPENSSL_LINUX)
#include "../crypto/fipsmodule/cpucap/cpu_getauxval_linux.h"
#endif

BSSL_NAMESPACE_BEGIN

namespace {

// kMaxCachedPathLen bounds the policy path the cache can key on. A longer path
// is parsed uncached rather than rejected.
constexpr size_t kMaxCachedPathLen = 1023;

// PolicyCache holds the last policy file parsed, keyed on the path it came
// from. |valid| distinguishes an empty cache from one holding a negative
// result.
struct PolicyCache {
  char path[kMaxCachedPathLen + 1];
  CryptoPolicyConfig cfg;
  bool present;  // |path| named a readable file
  bool valid;    // the fields above are filled in
};

struct CRYPTO_STATIC_MUTEX g_policy_cache_lock = CRYPTO_STATIC_MUTEX_INIT;
PolicyCache g_policy_cache;  // Guarded by |g_policy_cache_lock|.

// LoadPolicy fills |out| with the policy at |path|, parsing the file only on a
// cache miss, and returns whether |path| named a readable file.
//
// The file is read once per process for a given path. OpenSSL likewise parses
// openssl.cnf at library init rather than per |SSL_CTX|, and
// update-crypto-policies already requires restarting consumers for a new policy
// to take effect, so nothing observes the difference. Keying on the path keeps
// the AWSLC_CRYPTO_POLICY_FILE override live: a changed path misses.
bool LoadPolicy(const char *path, CryptoPolicyConfig *out) {
  const size_t path_len = strlen(path);
  if (path_len > kMaxCachedPathLen) {
    return ssl_crypto_policy_parse_file(path, out);
  }

  CRYPTO_STATIC_MUTEX_lock_read(&g_policy_cache_lock);
  const bool hit =
      g_policy_cache.valid && strcmp(g_policy_cache.path, path) == 0;
  const bool present = g_policy_cache.present;
  if (hit) {
    OPENSSL_memcpy(out, &g_policy_cache.cfg, sizeof(*out));
  }
  CRYPTO_STATIC_MUTEX_unlock_read(&g_policy_cache_lock);
  if (hit) {
    return present;
  }

  CryptoPolicyConfig cfg = {};
  const bool parsed = ssl_crypto_policy_parse_file(path, &cfg);

  // A concurrent miss on a different path may have populated the cache in the
  // meantime; overwriting it is harmless, since either entry is correct for the
  // path it names.
  CRYPTO_STATIC_MUTEX_lock_write(&g_policy_cache_lock);
  OPENSSL_memcpy(g_policy_cache.path, path, path_len + 1);
  OPENSSL_memcpy(&g_policy_cache.cfg, &cfg, sizeof(cfg));
  g_policy_cache.present = parsed;
  g_policy_cache.valid = true;
  CRYPTO_STATIC_MUTEX_unlock_write(&g_policy_cache_lock);

  OPENSSL_memcpy(out, &cfg, sizeof(cfg));
  return parsed;
}

// IsAsciiWhitespace matches the horizontal and line-ending whitespace that can
// appear around a directive in an OpenSSL config file.
bool IsAsciiWhitespace(char c) {
  return c == ' ' || c == '\t' || c == '\r' || c == '\n';
}

// CopyPolicyValue copies the |len| bytes at |value| into |out|, which has
// capacity |out_size| including the NUL terminator. It returns true on success.
//
// An overlong value empties |out| rather than truncating it. The last occurrence
// of a directive is the one the operator chose, so leaving an earlier occurrence
// in place would apply a policy they had already replaced.
bool CopyPolicyValue(char *out, size_t out_size, const char *value,
                     size_t len) {
  if (len >= out_size) {
    out[0] = '\0';
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

// kMaxPolicyIds bounds the algorithm IDs kept from one policy directive. No
// directive can yield more than the number of groups or signature algorithms
// AWS-LC implements, which is well under this.
constexpr size_t kMaxPolicyIds = 64;

// GroupIdFromToken sets |*out| to the AWS-LC group ID named by the
// crypto-policies token |tok|, of length |len|, and returns false if AWS-LC has
// no such group.
bool GroupIdFromToken(uint16_t *out, const char *tok, size_t len) {
  // crypto-policies uses the IANA registry name for the NIST P-256 curve.
  // AWS-LC follows OpenSSL, which knows it as "P-256" and "prime256v1" only, so
  // without this the most widely deployed group in the list is the one that
  // throws the whole list away.
  static const char kSecp256r1[] = "secp256r1";
  if (len == strlen(kSecp256r1) && OPENSSL_memcmp(tok, kSecp256r1, len) == 0) {
    tok = "P-256";
    len = strlen(tok);
  }
  return ssl_name_to_group_id(out, tok, len);
}

// FilterPolicyIds resolves the ':'-separated tokens of |value| through |lookup|
// and writes the IDs that resolve into |out|, which holds |out_len| entries, in
// the order the policy gave them. It returns how many were written.
//
// The Groups and SignatureAlgorithms setters reject a whole list on the first
// entry they do not accept, and a stock crypto-policies value always names
// something AWS-LC does not implement: X448 and the FFDHE groups, Ed448, the
// SHA-224 pairs, and the RSA-PSS-PSS algorithms. Applying such a value as written
// therefore discards the operator's whole preference order. Dropping the
// unsupported tokens keeps the rest of it.
//
// Repeats are dropped for the same reason: two spellings of one group, such as
// "secp256r1" and "prime256v1", resolve to a single ID, and |SSL_CTX_set1_group_ids|
// rejects a list that names it twice.
size_t FilterPolicyIds(uint16_t *out, size_t out_len, const char *value,
                       bool (*lookup)(uint16_t *, const char *, size_t)) {
  size_t out_i = 0;
  for (const char *tok = value;;) {
    const char *end = strchr(tok, ':');
    const size_t len =
        end != nullptr ? static_cast<size_t>(end - tok) : strlen(tok);

    uint16_t id;
    if (len > 0 && out_i < out_len && lookup(&id, tok, len)) {
      bool seen = false;
      for (size_t i = 0; i < out_i; i++) {
        seen = seen || out[i] == id;
      }
      if (!seen) {
        out[out_i++] = id;
      }
    }

    if (end == nullptr) {
      break;
    }
    tok = end + 1;
  }
  return out_i;
}

// ApplyCipherRule applies the cipher rule |rule| to |ctx|, as
// |SSL_CTX_set_cipher_list| does when |config_tls13| is false and
// |SSL_CTX_set_ciphersuites| when it is true, and returns false having left |ctx|
// as it was if any step fails.
//
// Neither public setter is a no-op on failure. |ssl_create_cipher_list| installs
// its result, empty or not, before reporting that the rule matched nothing, and
// the |update_cipher_list| that merges the TLS 1.2 and TLS 1.3 lists back
// together allocates, so it can fail after the first list is already in place.
// Either way the context is left holding part of a policy it could not apply,
// which for the first is no ciphers at all. Building both lists aside and moving
// them in once every step has succeeded is what keeps a failure to the defaults.
bool ApplyCipherRule(SSL_CTX *ctx, const char *rule, bool config_tls13) {
  const bool has_aes_hw = ctx->aes_hw_override ? ctx->aes_hw_override_value
                                               : EVP_has_aes_hardware();
  UniquePtr<SSLCipherPreferenceList> configured;
  if (!ssl_create_cipher_list(&configured, has_aes_hw, rule,
                              false /* not strict */, config_tls13)) {
    return false;
  }

  UniquePtr<SSLCipherPreferenceList> &tls12_list =
      config_tls13 ? ctx->cipher_list : configured;
  UniquePtr<SSLCipherPreferenceList> &tls13_list =
      config_tls13 ? configured : ctx->tls13_cipher_list;
  UniquePtr<SSLCipherPreferenceList> merged;
  if (!update_cipher_list(merged, tls12_list, tls13_list)) {
    return false;
  }

  if (config_tls13) {
    ctx->tls13_cipher_list = std::move(configured);
  }
  ctx->cipher_list = std::move(merged);
  return true;
}

// ApplyPolicyVersionBounds seeds the protocol version floor and ceiling from
// |cfg|, choosing the TLS.* or DTLS.* directives per |is_dtls|.
void ApplyPolicyVersionBounds(SSL_CTX *ctx, const CryptoPolicyConfig &cfg,
                              bool is_dtls, bool version_locked) {
  // A version-locked SSL_METHOD (TLSv1_2_method and friends) is skipped
  // entirely. |SSL_CTX_new| pins such a context by setting both bounds to
  // |method->version|, but the public setters validate only against the protocol
  // method's full version range, so applying a policy here would quietly raise
  // the ceiling and hand the caller a version they deliberately excluded.
  if (version_locked) {
    return;
  }

  const uint16_t policy_min =
      CryptoPolicyProtoVersion(is_dtls ? cfg.dtls_min : cfg.tls_min, is_dtls);
  const uint16_t policy_max =
      CryptoPolicyProtoVersion(is_dtls ? cfg.dtls_max : cfg.tls_max, is_dtls);

  // The setters check each bound against the method's whole version range and
  // never against each other, so a policy whose floor sits above its ceiling
  // would be accepted and leave every later handshake failing with
  // SSL_R_NO_SUPPORTED_VERSIONS_ENABLED. Resolve the pair first, filling in
  // whichever end the policy omits from the bound the context already has, and
  // apply it only if the resulting range is non-empty.
  //
  // The comparison is on protocol versions rather than wire versions because
  // DTLS wire values run backwards -- DTLS 1.0 is 0xfeff and DTLS 1.2 is 0xfefd
  // -- so ordering the raw values would invert the test for DTLS.
  uint16_t min_proto, max_proto;
  if (!ssl_protocol_version_from_wire(
          &min_proto, policy_min != 0 ? policy_min : ctx->conf_min_version) ||
      !ssl_protocol_version_from_wire(
          &max_proto, policy_max != 0 ? policy_max : ctx->conf_max_version) ||
      min_proto > max_proto) {
    return;
  }

  // Each setter still refuses a version its method does not support, and the two
  // are independent, so a pair only one of them accepts would leave the context
  // with half a policy. Put the bounds back if either refuses.
  const uint16_t saved_min = ctx->conf_min_version;
  const uint16_t saved_max = ctx->conf_max_version;
  const bool saved_min_default = ctx->conf_min_version_use_default;
  const bool saved_max_default = ctx->conf_max_version_use_default;
  if ((policy_min != 0 && !SSL_CTX_set_min_proto_version(ctx, policy_min)) ||
      (policy_max != 0 && !SSL_CTX_set_max_proto_version(ctx, policy_max))) {
    ctx->conf_min_version = saved_min;
    ctx->conf_max_version = saved_max;
    ctx->conf_min_version_use_default = saved_min_default;
    ctx->conf_max_version_use_default = saved_max_default;
  }
}

// ApplyPolicyToCtx seeds |ctx| from the policy file at |path|. Seeding is
// best-effort: every failure is swallowed and the built-in default kept.
// |ssl_ctx_apply_crypto_policy| wraps this and cleans up the error queue.
void ApplyPolicyToCtx(SSL_CTX *ctx, const char *path, bool is_dtls,
                      bool version_locked) {
  CryptoPolicyConfig cfg = {};
  if (!LoadPolicy(path, &cfg)) {
    // Missing or unreadable policy file: keep the built-in defaults.
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
    if (*cs != '\0') {
      ApplyCipherRule(ctx, cs, /*config_tls13=*/false);
    }
  }

  // Ciphersuites (TLS 1.3).
  if (cfg.ciphersuites[0] != '\0') {
    ApplyCipherRule(ctx, cfg.ciphersuites, /*config_tls13=*/true);
  }

  ApplyPolicyVersionBounds(ctx, cfg, is_dtls, version_locked);

  // SignatureAlgorithms and Groups, each narrowed to the algorithms AWS-LC
  // implements. One buffer serves both since the directives are applied in turn.
  uint16_t ids[kMaxPolicyIds];
  if (cfg.sigalgs[0] != '\0') {
    const size_t n = FilterPolicyIds(ids, OPENSSL_ARRAY_SIZE(ids), cfg.sigalgs,
                                     ssl_sigalg_id_from_name);
    if (n > 0) {
      // Both preference lists, matching what |SSL_CTX_set1_sigalgs_list| writes.
      SSL_CTX_set_signing_algorithm_prefs(ctx, ids, n);
      SSL_CTX_set_verify_algorithm_prefs(ctx, ids, n);
    }
  }
  if (cfg.groups[0] != '\0') {
    const size_t n = FilterPolicyIds(ids, OPENSSL_ARRAY_SIZE(ids), cfg.groups,
                                     GroupIdFromToken);
    if (n > 0) {
      SSL_CTX_set1_group_ids(ctx, ids, n);
    }
  }
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

void ssl_ctx_apply_crypto_policy(SSL_CTX *ctx, const char *path, bool is_dtls,
                                 bool version_locked) {
  if (ctx == nullptr || path == nullptr) {
    return;
  }

  // Seeding is best-effort, so the errors its failures queue must not reach the
  // caller. Neither may the caller's own queue be disturbed, since this runs
  // inside |SSL_CTX_new|, which no caller expects to touch the error queue at
  // all. Suppressing rather than trimming afterward is what keeps that true for
  // a caller whose queue is already full: there, each error seeding raised would
  // evict one of theirs, and no trim can bring an evicted entry back.
  //
  // Seeding is what gives way when the scope cannot be opened, since running it
  // unprotected is the one outcome the caller must not see.
  ScopedErrorSuppression suppress;
  if (!suppress) {
    return;
  }

  ApplyPolicyToCtx(ctx, path, is_dtls, version_locked);
}

BSSL_NAMESPACE_END

#endif  // AWSLC_CRYPTO_POLICIES
