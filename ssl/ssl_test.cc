/* Copyright (c) 2014, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#include <limits.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include <algorithm>
#include <array>
#include <limits>
#include <string>
#include <utility>
#include <vector>

#include <gtest/gtest.h>

#include <openssl/aead.h>
#include <openssl/base64.h>
#include <openssl/bio.h>
#include <openssl/bytestring.h>
#include <openssl/cipher.h>
#include <openssl/crypto.h>
#include <openssl/curve25519.h>
#include <openssl/err.h>
#include <openssl/hmac.h>
#include <openssl/hpke.h>
#include <openssl/pem.h>
#include <openssl/rand.h>
#include <openssl/sha.h>
#include <openssl/ssl.h>
#include <openssl/x509.h>

#include "ssl_test_common.h"
#include "../crypto/internal.h"
#include "../crypto/test/file_util.h"
#include "../crypto/test/test_util.h"
#include "internal.h"
#include "../crypto/kyber/kem_kyber.h"
#include "../crypto/fipsmodule/ec/internal.h"

#if defined(OPENSSL_WINDOWS)
// Windows defines struct timeval in winsock2.h.
OPENSSL_MSVC_PRAGMA(warning(push, 3))
#include <winsock2.h>
OPENSSL_MSVC_PRAGMA(warning(pop))
#else
#include <sys/time.h>
#endif

#if defined(OPENSSL_THREADS)
#include <thread>
#endif

BSSL_NAMESPACE_BEGIN

namespace {

INSTANTIATE_TEST_SUITE_P(SSLTests, SSLTest, testing::ValuesIn(kSSLTestParams),
                         [](const testing::TestParamInfo<SSLTestParam> &i) {
                           if (i.param.transfer_ssl) {
                             return "SSL_Transfer";
                           } else {
                             return "NO_SSL_Transfer";
                           }
                         });

struct ExpectedCipher {
  unsigned long id;
  int in_group_flag;
};

struct CipherTest {
  // The rule string to apply.
  const char *rule;
  // The list of expected ciphers, in order.
  std::vector<ExpectedCipher> expected;
  // True if this cipher list should fail in strict mode.
  bool strict_fail;
};

struct CurveTest {
  // The rule string to apply.
  const char *rule;
  // The list of expected curves, in order.
  std::vector<uint16_t> expected;
};







static const CipherTest kCipherTests[] = {
    // Selecting individual ciphers should work.
    {
        "ECDHE-ECDSA-CHACHA20-POLY1305:"
        "ECDHE-RSA-CHACHA20-POLY1305:"
        "ECDHE-ECDSA-AES128-GCM-SHA256:"
        "ECDHE-RSA-AES128-SHA256:"
        "ECDHE-RSA-AES128-GCM-SHA256",
        {
            {TLS1_CK_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256, 0},
            {TLS1_CK_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_128_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_128_GCM_SHA256, 0},
        },
        false,
    },
    // + reorders selected ciphers to the end, keeping their relative order.
    {
        "ECDHE-ECDSA-CHACHA20-POLY1305:"
        "ECDHE-RSA-CHACHA20-POLY1305:"
        "ECDHE-ECDSA-AES128-GCM-SHA256:"
        "ECDHE-RSA-AES128-GCM-SHA256:"
        "+aRSA",
        {
            {TLS1_CK_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256, 0},
            {TLS1_CK_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_128_GCM_SHA256, 0},
        },
        false,
    },
    // ! banishes ciphers from future selections.
    {
        "!aRSA:"
        "ECDHE-ECDSA-CHACHA20-POLY1305:"
        "ECDHE-RSA-CHACHA20-POLY1305:"
        "ECDHE-ECDSA-AES128-GCM-SHA256:"
        "ECDHE-RSA-AES128-GCM-SHA256",
        {
            {TLS1_CK_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256, 0},
            {TLS1_CK_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256, 0},
        },
        false,
    },
    // Multiple masks can be ANDed in a single rule.
    {
        "kRSA+AESGCM+AES128",
        {
            {TLS1_CK_RSA_WITH_AES_128_GCM_SHA256, 0},
        },
        false,
    },
    // - removes selected ciphers, but preserves their order for future
    // selections. Select AES_128_GCM, but order the key exchanges RSA,
    // ECDHE_RSA.
    {
        "ALL:-kECDHE:"
        "-kRSA:-ALL:"
        "AESGCM+AES128+aRSA",
        {
            {TLS1_CK_RSA_WITH_AES_128_GCM_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_128_GCM_SHA256, 0},
        },
        false,
    },
    // Unknown selectors are no-ops, except in strict mode.
    {
        "ECDHE-ECDSA-CHACHA20-POLY1305:"
        "ECDHE-RSA-CHACHA20-POLY1305:"
        "ECDHE-ECDSA-AES128-GCM-SHA256:"
        "ECDHE-RSA-AES128-GCM-SHA256:"
        "BOGUS1",
        {
            {TLS1_CK_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256, 0},
            {TLS1_CK_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_128_GCM_SHA256, 0},
        },
        true,
    },
    // Unknown selectors are no-ops, except in strict mode.
    {
        "ECDHE-ECDSA-CHACHA20-POLY1305:"
        "ECDHE-RSA-CHACHA20-POLY1305:"
        "ECDHE-ECDSA-AES128-GCM-SHA256:"
        "ECDHE-RSA-AES128-GCM-SHA256:"
        "-BOGUS2:+BOGUS3:!BOGUS4",
        {
            {TLS1_CK_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256, 0},
            {TLS1_CK_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_128_GCM_SHA256, 0},
        },
        true,
    },
    // Square brackets specify equi-preference groups.
    {
        "[ECDHE-ECDSA-CHACHA20-POLY1305|ECDHE-ECDSA-AES128-GCM-SHA256]:"
        "[ECDHE-RSA-CHACHA20-POLY1305]:"
        "ECDHE-RSA-AES128-GCM-SHA256",
        {
            {TLS1_CK_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256, 1},
            {TLS1_CK_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_128_GCM_SHA256, 0},
        },
        false,
    },
    // Standard names may be used instead of OpenSSL names.
    {
        "[TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256|"
        "TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256]:"
        "[TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256]:"
        "TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256",
        {
            {TLS1_CK_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256, 1},
            {TLS1_CK_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_128_GCM_SHA256, 0},
        },
        false,
    },
    // @STRENGTH performs a stable strength-sort of the selected ciphers and
    // only the selected ciphers.
    {
        // To simplify things, banish all but {ECDHE_RSA,RSA} x
        // {CHACHA20,AES_256_CBC,AES_128_CBC} x SHA1.
        "!AESGCM:!3DES:"
        // Order some ciphers backwards by strength.
        "ALL:-CHACHA20:-AES256:-AES128:-ALL:"
        // Select ECDHE ones and sort them by strength. Ties should resolve
        // based on the order above.
        "kECDHE:@STRENGTH:-ALL:"
        // Now bring back everything uses RSA. ECDHE_RSA should be first, sorted
        // by strength. Then RSA, backwards by strength.
        "aRSA",
        {
            {TLS1_CK_ECDHE_RSA_WITH_AES_256_CBC_SHA, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_256_SHA384, 0},
            {TLS1_CK_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_128_CBC_SHA, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_128_SHA256, 0},
            {TLS1_CK_RSA_WITH_AES_128_SHA, 0},
            {TLS1_CK_RSA_WITH_AES_128_SHA256, 0},
            {TLS1_CK_RSA_WITH_AES_256_SHA, 0},
        },
        false,
    },
    // Additional masks after @STRENGTH get silently discarded.
    //
    // TODO(davidben): Make this an error. If not silently discarded, they get
    // interpreted as + opcodes which are very different.
    {
        "ECDHE-RSA-AES128-GCM-SHA256:"
        "ECDHE-RSA-AES256-GCM-SHA384:"
        "@STRENGTH+AES256",
        {
            {TLS1_CK_ECDHE_RSA_WITH_AES_256_GCM_SHA384, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_128_GCM_SHA256, 0},
        },
        false,
    },
    {
        "ECDHE-RSA-AES128-GCM-SHA256:"
        "ECDHE-RSA-AES256-GCM-SHA384:"
        "@STRENGTH+AES256:"
        "ECDHE-RSA-CHACHA20-POLY1305",
        {
            {TLS1_CK_ECDHE_RSA_WITH_AES_256_GCM_SHA384, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_128_GCM_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256, 0},
        },
        false,
    },
    // Exact ciphers may not be used in multi-part rules; they are treated
    // as unknown aliases.
    {
        "ECDHE-ECDSA-AES128-GCM-SHA256:"
        "ECDHE-RSA-AES128-GCM-SHA256:"
        "!ECDHE-RSA-AES128-GCM-SHA256+RSA:"
        "!ECDSA+ECDHE-ECDSA-AES128-GCM-SHA256",
        {
            {TLS1_CK_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_128_GCM_SHA256, 0},
        },
        true,
    },
    // SSLv3 matches everything that existed before TLS 1.2.
    {
        "AES128-SHA:AES128-SHA256:ECDHE-RSA-AES128-GCM-SHA256:!SSLv3",
        {
            {TLS1_CK_RSA_WITH_AES_128_SHA256, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_128_GCM_SHA256, 0},
        },
        false,
    },
    // TLSv1.2 matches everything added in TLS 1.2.
    {
        "AES128-SHA:AES128-SHA256:ECDHE-RSA-AES128-GCM-SHA256:!TLSv1.2",
        {
            {TLS1_CK_RSA_WITH_AES_128_SHA, 0},
        },
        false,
    },
    // The two directives have no intersection.  But each component is valid, so
    // even in strict mode it is accepted.
    {
        "AES128-SHA:ECDHE-RSA-AES128-GCM-SHA256:!TLSv1.2+SSLv3",
        {
            {TLS1_CK_RSA_WITH_AES_128_SHA, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_128_GCM_SHA256, 0},
        },
        false,
    },
    // Spaces, semi-colons and commas are separators.
    {
        "AES128-SHA: ECDHE-RSA-AES128-GCM-SHA256 AES256-SHA "
        ",ECDHE-ECDSA-AES128-GCM-SHA256 ; AES128-GCM-SHA256",
        {
            {TLS1_CK_RSA_WITH_AES_128_SHA, 0},
            {TLS1_CK_ECDHE_RSA_WITH_AES_128_GCM_SHA256, 0},
            {TLS1_CK_RSA_WITH_AES_256_SHA, 0},
            {TLS1_CK_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256, 0},
            {TLS1_CK_RSA_WITH_AES_128_GCM_SHA256, 0},
        },
        // …but not in strict mode.
        true,
    },
};

// In kTLSv13RuleOnly, |rule| of each CipherTest can only match TLSv1.3 ciphers.
// e.g. kTLSv13RuleOnly does not have rule "AESGCM+AES128", which can match
// some TLSv1.2 ciphers.
static const CipherTest kTLSv13RuleOnly[] = {
    // Selecting individual ciphers should work.
    {
        "TLS_AES_256_GCM_SHA384:"
        "TLS_CHACHA20_POLY1305_SHA256:"
        "TLS_AES_128_GCM_SHA256",
        {
            {TLS1_CK_AES_256_GCM_SHA384, 0},
            {TLS1_CK_CHACHA20_POLY1305_SHA256, 0},
            {TLS1_CK_AES_128_GCM_SHA256, 0},
        },
        false,
    },
    // + reorders selected ciphers to the end, keeping their relative order.
    {
        "TLS_AES_256_GCM_SHA384:"
        "TLS_CHACHA20_POLY1305_SHA256:"
        "TLS_AES_128_GCM_SHA256:"
        "+AES",
        {
            {TLS1_CK_CHACHA20_POLY1305_SHA256, 0},
            {TLS1_CK_AES_256_GCM_SHA384, 0},
            {TLS1_CK_AES_128_GCM_SHA256, 0},
        },
        false,
    },
    // ! banishes ciphers from future selections.
    {
        "!CHACHA20:"
        "TLS_AES_256_GCM_SHA384:"
        "TLS_CHACHA20_POLY1305_SHA256:"
        "TLS_AES_128_GCM_SHA256:"
        "TLS_CHACHA20_POLY1305_SHA256",
        {
            {TLS1_CK_AES_256_GCM_SHA384, 0},
            {TLS1_CK_AES_128_GCM_SHA256, 0},
        },
        false,
    },
    // Square brackets specify equi-preference groups.
    {
        "[TLS_AES_128_GCM_SHA256|TLS_AES_256_GCM_SHA384]:"
        "TLS_CHACHA20_POLY1305_SHA256",
        {
            {TLS1_CK_AES_128_GCM_SHA256, 1},
            {TLS1_CK_AES_256_GCM_SHA384, 0},
            {TLS1_CK_CHACHA20_POLY1305_SHA256, 0},
        },
        false,
    },
    // Spaces, semi-colons and commas are separators.
    {
        "TLS_AES_256_GCM_SHA384 ; "
        "TLS_CHACHA20_POLY1305_SHA256 , "
        "TLS_AES_128_GCM_SHA256",
        {
            {TLS1_CK_AES_256_GCM_SHA384, 0},
            {TLS1_CK_CHACHA20_POLY1305_SHA256, 0},
            {TLS1_CK_AES_128_GCM_SHA256, 0},
        },
        false,
    },
};

// Besides kTLSv13RuleOnly, additional rules can match TLSv1.3 ciphers.
static const CipherTest kTLSv13CipherTests[] = {
    // Multiple masks can be ANDed in a single rule.
    {
        "AESGCM+AES128",
        {
            {TLS1_CK_AES_128_GCM_SHA256, 0},
        },
        false,
    },
    // - removes selected ciphers, but preserves their order for future
    // selections. Select AES_128_GCM, but order the key exchanges RSA,
    // ECDHE_RSA.
    {
        "ALL:-AES",
        {
            {TLS1_CK_CHACHA20_POLY1305_SHA256, 0},
        },
        false,
    },
    // Unknown selectors or TLSv1.2 ciphers are no-ops.
    {
        "TLS_CHACHA20_POLY1305_SHA256:"
        "ECDHE-RSA-CHACHA20-POLY1305:"
        "BOGUS1",
        {
            {TLS1_CK_CHACHA20_POLY1305_SHA256, 0},
        },
        true,
    },
};

static const char *kBadRules[] = {
  // Invalid brackets.
  "[ECDHE-RSA-CHACHA20-POLY1305|ECDHE-RSA-AES128-GCM-SHA256",
  "RSA]",
  "[[RSA]]",
  // Operators inside brackets.
  "[+RSA]",
  // Unknown directive.
  "@BOGUS",
  "BOGUS",
  // COMPLEMENTOFDEFAULT is empty.
  "COMPLEMENTOFDEFAULT",
  // Invalid command.
  "?BAR",
  // Special operators are not allowed if equi-preference groups are used.
  "[ECDHE-RSA-CHACHA20-POLY1305|ECDHE-RSA-AES128-GCM-SHA256]:+FOO",
  "[ECDHE-RSA-CHACHA20-POLY1305|ECDHE-RSA-AES128-GCM-SHA256]:!FOO",
  "[ECDHE-RSA-CHACHA20-POLY1305|ECDHE-RSA-AES128-GCM-SHA256]:-FOO",
  "[ECDHE-RSA-CHACHA20-POLY1305|ECDHE-RSA-AES128-GCM-SHA256]:@STRENGTH",
  // Opcode supplied, but missing selector.
  "+",
  // Spaces are forbidden in equal-preference groups.
  "[AES128-SHA | AES128-SHA256]",
};

static const char *kMustNotIncludeNull[] = {
    "ALL",  "DEFAULT", "HIGH",  "FIPS",  "SHA",
    "SHA1", "RSA",     "SSLv3", "TLSv1", "TLSv1.2",
};

static const char *kTLSv13MustNotIncludeNull[] = {
    "ALL",
    "DEFAULT",
    "HIGH",
    "FIPS",
};

static const char *kMustNotInclude3DES[] = {
    "ALL", "DEFAULT", "HIGH", "FIPS", "SSLv3", "TLSv1", "TLSv1.2",
};

static const CurveTest kCurveTests[] = {
  {
    "P-256",
    {SSL_GROUP_SECP256R1},
  },
  {
    "P-256:P-384:P-521:X25519",
    {
      SSL_GROUP_SECP256R1,
      SSL_GROUP_SECP384R1,
      SSL_GROUP_SECP521R1,
      SSL_GROUP_X25519,
    },
  },
  {
    "prime256v1:secp384r1:secp521r1:x25519",
    {
      SSL_GROUP_SECP256R1,
      SSL_GROUP_SECP384R1,
      SSL_GROUP_SECP521R1,
      SSL_GROUP_X25519,
    },
  },
  {
    "SecP256r1Kyber768Draft00:prime256v1:secp384r1:secp521r1:x25519",
    {
      SSL_GROUP_SECP256R1_KYBER768_DRAFT00,
      SSL_GROUP_SECP256R1,
      SSL_GROUP_SECP384R1,
      SSL_GROUP_SECP521R1,
      SSL_GROUP_X25519,
    },
  },
  {
    "X25519Kyber768Draft00:prime256v1:secp384r1",
    {
      SSL_GROUP_X25519_KYBER768_DRAFT00,
      SSL_GROUP_SECP256R1,
      SSL_GROUP_SECP384R1,
    },
  },
  {
    "X25519:X25519Kyber768Draft00",
    {
      SSL_GROUP_X25519,
      SSL_GROUP_X25519_KYBER768_DRAFT00,
    },
  },
  {
    "X25519:SecP256r1Kyber768Draft00:prime256v1",
    {
      SSL_GROUP_X25519,
      SSL_GROUP_SECP256R1_KYBER768_DRAFT00,
      SSL_GROUP_SECP256R1,
    },
  },
  {
    "SecP256r1MLKEM768:prime256v1:secp384r1:secp521r1:x25519",
    {
      SSL_GROUP_SECP256R1_MLKEM768,
      SSL_GROUP_SECP256R1,
      SSL_GROUP_SECP384R1,
      SSL_GROUP_SECP521R1,
      SSL_GROUP_X25519,
    },
  },
  {
    "X25519MLKEM768:prime256v1:secp384r1",
    {
      SSL_GROUP_X25519_MLKEM768,
      SSL_GROUP_SECP256R1,
      SSL_GROUP_SECP384R1,
    },
  },
  {
    "X25519:X25519MLKEM768",
    {
      SSL_GROUP_X25519,
      SSL_GROUP_X25519_MLKEM768,
    },
  },
  {
    "X25519:SecP256r1MLKEM768:prime256v1",
    {
      SSL_GROUP_X25519,
      SSL_GROUP_SECP256R1_MLKEM768,
      SSL_GROUP_SECP256R1,
    },
  },
{
  "SecP384r1MLKEM1024:X25519MLKEM768:SecP256r1MLKEM768",
  {
    SSL_GROUP_SECP384R1_MLKEM1024,
    SSL_GROUP_X25519_MLKEM768,
    SSL_GROUP_SECP256R1_MLKEM768,
  },
},
};






static const char *kBadCurvesLists[] = {
  "",
  ":",
  "::",
  "P-256::X25519",
  "RSA:P-256",
  "P-256:RSA",
  "X25519:P-256:",
  ":X25519:P-256",
  "kyber768_r3",
  "x25519_kyber768:prime256v1",
  "mlkem768",
  "x25519_mlkem768:prime256v1",
};

static STACK_OF(SSL_CIPHER) *tls13_ciphers(const SSL_CTX *ctx) {
  return ctx->tls13_cipher_list->ciphers.get();
}

static std::string CipherListToString(SSL_CTX *ctx, bool tlsv13_ciphers) {
  bool in_group = false;
  std::string ret;
  const STACK_OF(SSL_CIPHER) *ciphers =
      tlsv13_ciphers ? tls13_ciphers(ctx) : SSL_CTX_get_ciphers(ctx);
  for (size_t i = 0; i < sk_SSL_CIPHER_num(ciphers); i++) {
    const SSL_CIPHER *cipher = sk_SSL_CIPHER_value(ciphers, i);
    if (!in_group && SSL_CTX_cipher_in_group(ctx, i)) {
      ret += "\t[\n";
      in_group = true;
    }
    ret += "\t";
    if (in_group) {
      ret += "  ";
    }
    ret += SSL_CIPHER_get_name(cipher);
    ret += "\n";
    if (in_group && !SSL_CTX_cipher_in_group(ctx, i)) {
      ret += "\t]\n";
      in_group = false;
    }
  }
  return ret;
}

static bool CipherListsEqual(SSL_CTX *ctx,
                             const std::vector<ExpectedCipher> &expected,
                             bool tlsv13_ciphers) {
  STACK_OF(SSL_CIPHER) *ciphers =
      tlsv13_ciphers ? tls13_ciphers(ctx) : SSL_CTX_get_ciphers(ctx);
  if (sk_SSL_CIPHER_num(ciphers) != expected.size()) {
    return false;
  }

  for (size_t i = 0; i < expected.size(); i++) {
    const SSL_CIPHER *cipher = sk_SSL_CIPHER_value(ciphers, i);
    if (expected[i].id != SSL_CIPHER_get_id(cipher) ||
        expected[i].in_group_flag !=
            !!SSL_CTX_cipher_in_group(ctx, i)) {
      return false;
    }
  }

  return true;
}

TEST(SSLTest, CipherRules) {
  for (const CipherTest &t : kCipherTests) {
    SCOPED_TRACE(t.rule);
    bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ctx);

    // We configure default TLS 1.3 ciphersuites in |SSL_CTX| which pollute
    // |ctx->cipher_list|. Set it to an empty list so we can test TLS 1.2
    // configurations.
    ASSERT_TRUE(SSL_CTX_set_ciphersuites(ctx.get(), ""));

    // Test lax mode.
    ASSERT_TRUE(SSL_CTX_set_cipher_list(ctx.get(), t.rule));
    EXPECT_TRUE(
        CipherListsEqual(ctx.get(), t.expected, false /* not TLSv1.3 only */))
        << "Cipher rule evaluated to:\n"
        << CipherListToString(ctx.get(), false /* not TLSv1.3 only */);

    // Test strict mode.
    if (t.strict_fail) {
      EXPECT_FALSE(SSL_CTX_set_strict_cipher_list(ctx.get(), t.rule));
    } else {
      ASSERT_TRUE(SSL_CTX_set_strict_cipher_list(ctx.get(), t.rule));
      EXPECT_TRUE(
          CipherListsEqual(ctx.get(), t.expected, false /* not TLSv1.3 only */))
          << "Cipher rule evaluated to:\n"
          << CipherListToString(ctx.get(), false /* not TLSv1.3 only */);
    }
  }

  for (const char *rule : kBadRules) {
    SCOPED_TRACE(rule);
    bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ctx);

    EXPECT_FALSE(SSL_CTX_set_cipher_list(ctx.get(), rule));
    ERR_clear_error();
  }

  // kTLSv13RuleOnly are valid test cases for |SSL_CTX_set_ciphersuites|,
  // which configures only TLSv1.3 ciphers.
  // |SSL_CTX_set_cipher_list| only supports TLSv1.2 and below ciphers
  // configuration. Accordingly, kTLSv13RuleOnly result in
  // |SSL_R_NO_CIPHER_MATCH|.
  for (const CipherTest &t : kTLSv13RuleOnly) {
    SCOPED_TRACE(t.rule);
    bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ctx);

    // We configure default TLS 1.3 ciphersuites in |SSL_CTX| which pollute
    // |ctx->cipher_list|. Set it to an empty list so we can test TLS 1.2
    // configurations.
    ASSERT_TRUE(SSL_CTX_set_ciphersuites(ctx.get(), ""));

    EXPECT_FALSE(SSL_CTX_set_cipher_list(ctx.get(), t.rule));
    ASSERT_EQ(ERR_GET_REASON(ERR_get_error()), SSL_R_NO_CIPHER_MATCH);
    ERR_clear_error();
  }

  for (const char *rule : kMustNotIncludeNull) {
    SCOPED_TRACE(rule);
    bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ctx);

    ASSERT_TRUE(SSL_CTX_set_strict_cipher_list(ctx.get(), rule));
    for (const SSL_CIPHER *cipher : SSL_CTX_get_ciphers(ctx.get())) {
      EXPECT_NE(NID_undef, SSL_CIPHER_get_cipher_nid(cipher));
    }
  }

  for (const char *rule : kMustNotInclude3DES) {
    SCOPED_TRACE(rule);
    bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ctx);

    ASSERT_TRUE(SSL_CTX_set_strict_cipher_list(ctx.get(), rule));
    for (const SSL_CIPHER *cipher : SSL_CTX_get_ciphers(ctx.get())) {
      EXPECT_NE(NID_des_ede3_cbc, SSL_CIPHER_get_cipher_nid(cipher));
    }
  }
}

static std::vector<CipherTest> combine_tests(const CipherTest *c1,
                                             size_t size_1,
                                             const CipherTest *c2,
                                             size_t size_2) {
  std::vector<CipherTest> ret(size_1 + size_2);
  size_t j = 0;
  for (size_t i = 0; i < size_1; i++) {
    ret[j++] = c1[i];
  }
  for (size_t i = 0; i < size_2; i++) {
    ret[j++] = c2[i];
  }
  return ret;
}

TEST(SSLTest, TLSv13CipherRules) {
  std::vector<CipherTest> cipherRules =
      combine_tests(kTLSv13RuleOnly, OPENSSL_ARRAY_SIZE(kTLSv13RuleOnly),
                    kTLSv13CipherTests, OPENSSL_ARRAY_SIZE(kTLSv13CipherTests));
  for (const CipherTest &t : cipherRules) {
    SCOPED_TRACE(t.rule);
    bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ctx);
    bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
    ASSERT_TRUE(ssl);

    // Test lax mode.
    ASSERT_TRUE(SSL_CTX_set_ciphersuites(ctx.get(), t.rule));
    ASSERT_TRUE(SSL_set_ciphersuites(ssl.get(), t.rule));
    EXPECT_TRUE(
        CipherListsEqual(ctx.get(), t.expected, true /* TLSv1.3 only */))
        << "Cipher rule evaluated to:\n"
        << CipherListToString(ctx.get(), true /* TLSv1.3 only */);

    // TODO: add |SSL_CTX_set_strict_ciphersuites| and test strict mode.
  }

  for (const char *rule : kBadRules) {
    SCOPED_TRACE(rule);
    bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ctx);
    bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
    ASSERT_TRUE(ssl);

    EXPECT_FALSE(SSL_CTX_set_ciphersuites(ctx.get(), rule));
    EXPECT_FALSE(SSL_set_ciphersuites(ssl.get(), rule));
    ERR_clear_error();
  }

  for (const char *rule : kTLSv13MustNotIncludeNull) {
    SCOPED_TRACE(rule);
    bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ctx);
    bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
    ASSERT_TRUE(ssl);

    ASSERT_TRUE(SSL_CTX_set_ciphersuites(ctx.get(), rule));
    ASSERT_TRUE(SSL_set_ciphersuites(ssl.get(), rule));
    // Currenly, only three TLSv1.3 ciphers are supported.
    EXPECT_EQ(3u, sk_SSL_CIPHER_num(tls13_ciphers(ctx.get())));
    for (const SSL_CIPHER *cipher : tls13_ciphers(ctx.get())) {
      EXPECT_NE(NID_undef, SSL_CIPHER_get_cipher_nid(cipher));
    }
  }

  // kCipherTests are valid test cases for |SSL_CTX_set_cipher_list|,
  // which configures only TLSv1.2 and below ciphers.
  // |SSL_CTX_set_ciphersuites| only supports TLSv1.3 ciphers configuration.
  // Accordingly, kCipherTests result in |SSL_R_NO_CIPHER_MATCH|.
  // If kCipherTests starts to include rules that can match TLSv1.3 ciphers,
  // kCipherTests should get splitted.
  for (const CipherTest &t : kCipherTests) {
    SCOPED_TRACE(t.rule);
    bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ctx);
    bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
    ASSERT_TRUE(ssl);

    EXPECT_FALSE(SSL_CTX_set_ciphersuites(ctx.get(), t.rule));
    EXPECT_FALSE(SSL_set_ciphersuites(ssl.get(), t.rule));
    ASSERT_EQ(ERR_GET_REASON(ERR_get_error()), SSL_R_NO_CIPHER_MATCH);
    ERR_clear_error();
  }
}

TEST(SSLTest, CurveRules) {
  for (const CurveTest &t : kCurveTests) {
    SCOPED_TRACE(t.rule);
    bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ctx);

    ASSERT_TRUE(SSL_CTX_set1_groups_list(ctx.get(), t.rule));
    ASSERT_EQ(t.expected.size(), ctx->supported_group_list.size());
    for (size_t i = 0; i < t.expected.size(); i++) {
      EXPECT_EQ(t.expected[i], ctx->supported_group_list[i]);
    }
  }

  for (const char *rule : kBadCurvesLists) {
    SCOPED_TRACE(rule);
    bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ctx);

    EXPECT_FALSE(SSL_CTX_set1_groups_list(ctx.get(), rule));
    ERR_clear_error();
  }
}



static void ExpectDefaultVersion(uint16_t min_version, uint16_t max_version,
                                 const SSL_METHOD *(*method)(void)) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(method()));
  ASSERT_TRUE(ctx);
  bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);
  EXPECT_EQ(0, SSL_CTX_get_min_proto_version(ctx.get()));
  EXPECT_EQ(0, SSL_CTX_get_max_proto_version(ctx.get()));
  EXPECT_EQ(0, SSL_get_min_proto_version(ssl.get()));
  EXPECT_EQ(0, SSL_get_max_proto_version(ssl.get()));

  EXPECT_TRUE(SSL_CTX_set_min_proto_version(ctx.get(), min_version));
  EXPECT_TRUE(SSL_CTX_set_max_proto_version(ctx.get(), max_version));
  EXPECT_EQ(min_version, SSL_CTX_get_min_proto_version(ctx.get()));
  EXPECT_EQ(max_version, SSL_CTX_get_max_proto_version(ctx.get()));
  EXPECT_TRUE(SSL_set_min_proto_version(ssl.get(), min_version));
  EXPECT_TRUE(SSL_set_max_proto_version(ssl.get(), max_version));
  EXPECT_EQ(min_version, SSL_get_min_proto_version(ssl.get()));
  EXPECT_EQ(max_version, SSL_get_max_proto_version(ssl.get()));
}

TEST(SSLTest, DefaultVersion) {
  ExpectDefaultVersion(TLS1_VERSION, TLS1_3_VERSION, &TLS_method);
  ExpectDefaultVersion(TLS1_VERSION, TLS1_VERSION, &TLSv1_method);
  ExpectDefaultVersion(TLS1_1_VERSION, TLS1_1_VERSION, &TLSv1_1_method);
  ExpectDefaultVersion(TLS1_2_VERSION, TLS1_2_VERSION, &TLSv1_2_method);
  ExpectDefaultVersion(DTLS1_VERSION, DTLS1_2_VERSION, &DTLS_method);
  ExpectDefaultVersion(DTLS1_VERSION, DTLS1_VERSION, &DTLSv1_method);
  ExpectDefaultVersion(DTLS1_2_VERSION, DTLS1_2_VERSION, &DTLSv1_2_method);
}

TEST(SSLTest, CipherProperties) {
  static const struct {
    int id;
    const char *standard_name;
    int cipher_nid;
    int digest_nid;
    int kx_nid;
    int auth_nid;
    int prf_nid;
  } kTests[] = {
      {
          SSL3_CK_RSA_DES_192_CBC3_SHA,
          "TLS_RSA_WITH_3DES_EDE_CBC_SHA",
          NID_des_ede3_cbc,
          NID_sha1,
          NID_kx_rsa,
          NID_auth_rsa,
          NID_md5_sha1,
      },
      {
          TLS1_CK_RSA_WITH_AES_128_SHA,
          "TLS_RSA_WITH_AES_128_CBC_SHA",
          NID_aes_128_cbc,
          NID_sha1,
          NID_kx_rsa,
          NID_auth_rsa,
          NID_md5_sha1,
      },
      {
          TLS1_CK_RSA_WITH_AES_128_SHA256,
          "TLS_RSA_WITH_AES_128_CBC_SHA256",
          NID_aes_128_cbc,
          NID_sha256,
          NID_kx_rsa,
          NID_auth_rsa,
          NID_sha256,
      },
      {
          TLS1_CK_PSK_WITH_AES_256_CBC_SHA,
          "TLS_PSK_WITH_AES_256_CBC_SHA",
          NID_aes_256_cbc,
          NID_sha1,
          NID_kx_psk,
          NID_auth_psk,
          NID_md5_sha1,
      },
      {
          TLS1_CK_ECDHE_RSA_WITH_AES_128_CBC_SHA,
          "TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA",
          NID_aes_128_cbc,
          NID_sha1,
          NID_kx_ecdhe,
          NID_auth_rsa,
          NID_md5_sha1,
      },
      {
          TLS1_CK_ECDHE_RSA_WITH_AES_128_SHA256,
          "TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256",
          NID_aes_128_cbc,
          NID_sha256,
          NID_kx_ecdhe,
          NID_auth_rsa,
          NID_sha256,
      },
      {
          TLS1_CK_ECDHE_RSA_WITH_AES_256_CBC_SHA,
          "TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA",
          NID_aes_256_cbc,
          NID_sha1,
          NID_kx_ecdhe,
          NID_auth_rsa,
          NID_md5_sha1,
      },
      {
          TLS1_CK_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
          "TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256",
          NID_aes_128_gcm,
          NID_undef,
          NID_kx_ecdhe,
          NID_auth_rsa,
          NID_sha256,
      },
      {
          TLS1_CK_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
          "TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256",
          NID_aes_128_gcm,
          NID_undef,
          NID_kx_ecdhe,
          NID_auth_ecdsa,
          NID_sha256,
      },
      {
          TLS1_CK_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
          "TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384",
          NID_aes_256_gcm,
          NID_undef,
          NID_kx_ecdhe,
          NID_auth_ecdsa,
          NID_sha384,
      },
      {
          TLS1_CK_ECDHE_PSK_WITH_AES_128_CBC_SHA,
          "TLS_ECDHE_PSK_WITH_AES_128_CBC_SHA",
          NID_aes_128_cbc,
          NID_sha1,
          NID_kx_ecdhe,
          NID_auth_psk,
          NID_md5_sha1,
      },
      {
          TLS1_CK_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256,
          "TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256",
          NID_chacha20_poly1305,
          NID_undef,
          NID_kx_ecdhe,
          NID_auth_rsa,
          NID_sha256,
      },
      {
          TLS1_3_CK_AES_256_GCM_SHA384,
          "TLS_AES_256_GCM_SHA384",
          NID_aes_256_gcm,
          NID_undef,
          NID_kx_any,
          NID_auth_any,
          NID_sha384,
      },
      {
          TLS1_3_CK_AES_128_GCM_SHA256,
          "TLS_AES_128_GCM_SHA256",
          NID_aes_128_gcm,
          NID_undef,
          NID_kx_any,
          NID_auth_any,
          NID_sha256,
      },
      {
          TLS1_3_CK_CHACHA20_POLY1305_SHA256,
          "TLS_CHACHA20_POLY1305_SHA256",
          NID_chacha20_poly1305,
          NID_undef,
          NID_kx_any,
          NID_auth_any,
          NID_sha256,
      },
  };

  for (const auto &t : kTests) {
    SCOPED_TRACE(t.standard_name);

    const SSL_CIPHER *cipher = SSL_get_cipher_by_value(t.id & 0xffff);
    ASSERT_TRUE(cipher);
    EXPECT_STREQ(t.standard_name, SSL_CIPHER_standard_name(cipher));

    EXPECT_EQ(t.cipher_nid, SSL_CIPHER_get_cipher_nid(cipher));
    EXPECT_EQ(t.digest_nid, SSL_CIPHER_get_digest_nid(cipher));
    EXPECT_EQ(t.kx_nid, SSL_CIPHER_get_kx_nid(cipher));
    EXPECT_EQ(t.auth_nid, SSL_CIPHER_get_auth_nid(cipher));
    const EVP_MD *md = SSL_CIPHER_get_handshake_digest(cipher);
    ASSERT_TRUE(md);
    EXPECT_EQ(t.prf_nid, EVP_MD_nid(md));
    EXPECT_EQ(t.prf_nid, SSL_CIPHER_get_prf_nid(cipher));
  }
}





static bssl::UniquePtr<SSL_CTX> CreateContextWithCertificate(
    const SSL_METHOD *method, bssl::UniquePtr<X509> cert,
    bssl::UniquePtr<EVP_PKEY> key) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(method));
  if (!ctx || !cert || !key ||
      !SSL_CTX_use_certificate(ctx.get(), cert.get()) ||
      !SSL_CTX_use_PrivateKey(ctx.get(), key.get())) {
    return nullptr;
  }
  return ctx;
}

// Correct ID and name
#define TLS13_AES_128_GCM_SHA256_BYTES  ((const unsigned char *)"\x13\x01")
#define TLS13_CHACHA20_POLY1305_SHA256_BYTES ((const unsigned char *)"\x13\x03")
// Invalid ID
#define TLS13_AES_256_GCM_SHA384_BYTES  ((const unsigned char *)"\x13\x13")
TEST(SSLTest, FindingCipher) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx =
          CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);
  // Configure only TLS 1.3.
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_3_VERSION));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));

  SCOPED_TRACE("TLS_AES_128_GCM_SHA256");
  const SSL_CIPHER *cipher1 = SSL_CIPHER_find(server.get(), TLS13_AES_128_GCM_SHA256_BYTES);
  ASSERT_TRUE(cipher1);
  EXPECT_STREQ("TLS_AES_128_GCM_SHA256", SSL_CIPHER_standard_name(cipher1));

  SCOPED_TRACE("TLS_CHACHA20_POLY1305_SHA256");
  const SSL_CIPHER *cipher2 = SSL_CIPHER_find(server.get(), TLS13_CHACHA20_POLY1305_SHA256_BYTES);
  ASSERT_TRUE(cipher2);
  EXPECT_STREQ("TLS_CHACHA20_POLY1305_SHA256", SSL_CIPHER_standard_name(cipher2));

  SCOPED_TRACE("TLS_AES_256_GCM_SHA384");
  const SSL_CIPHER *cipher3 = SSL_CIPHER_find(client.get(), TLS13_AES_256_GCM_SHA384_BYTES);
  ASSERT_FALSE(cipher3);
}

TEST(SSLTest, CheckSSLCipherInheritance) {
  // This configures SSL_CTX objects with default TLS 1.2 and 1.3 ciphersuites
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx =
          CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), TLS1_2_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(server_ctx.get(), TLS1_2_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_3_VERSION));

  ASSERT_TRUE(SSL_CTX_set_ciphersuites(client_ctx.get(), "TLS_AES_128_GCM_SHA256"));
  ASSERT_TRUE(SSL_CTX_set_ciphersuites(server_ctx.get(), "TLS_AES_128_GCM_SHA256"));
  ASSERT_TRUE(SSL_CTX_set_cipher_list(client_ctx.get(), "TLS_RSA_WITH_AES_128_CBC_SHA"));
  ASSERT_TRUE(SSL_CTX_set_cipher_list(server_ctx.get(), "TLS_RSA_WITH_AES_128_CBC_SHA"));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(CreateClientAndServer(&client, &server, client_ctx.get(), server_ctx.get()));

  // Modify CTX ciphersuites
  ASSERT_TRUE(SSL_CTX_set_ciphersuites(client_ctx.get(), "TLS_AES_256_GCM_SHA384"));
  ASSERT_TRUE(SSL_CTX_set_ciphersuites(server_ctx.get(), "TLS_AES_256_GCM_SHA384"));
  ASSERT_TRUE(SSL_CTX_set_cipher_list(client_ctx.get(), "TLS_RSA_WITH_AES_256_CBC_SHA"));
  ASSERT_TRUE(SSL_CTX_set_cipher_list(server_ctx.get(), "TLS_RSA_WITH_AES_256_CBC_SHA"));

  // Ensure SSL object inherits initial CTX cipher suites
  STACK_OF(SSL_CIPHER) *client_ciphers = SSL_get_ciphers(client.get());
  STACK_OF(SSL_CIPHER) *server_ciphers = SSL_get_ciphers(server.get());
  ASSERT_TRUE(client_ciphers);
  ASSERT_TRUE(server_ciphers);
  ASSERT_EQ(sk_SSL_CIPHER_num(client_ciphers), 2u);
  ASSERT_EQ(sk_SSL_CIPHER_num(server_ciphers), 2u);
  const SSL_CIPHER *tls13_cipher = SSL_get_cipher_by_value(TLS1_3_CK_AES_128_GCM_SHA256 & 0xFFFF);
  const SSL_CIPHER *tls12_cipher = SSL_get_cipher_by_value(TLS1_CK_RSA_WITH_AES_128_SHA & 0xFFFF);
  ASSERT_TRUE(tls13_cipher);
  ASSERT_TRUE(tls12_cipher);

  ASSERT_TRUE(sk_SSL_CIPHER_find_awslc(client_ciphers, NULL, tls12_cipher));
  ASSERT_TRUE(sk_SSL_CIPHER_find_awslc(client_ciphers, NULL, tls13_cipher));
  ASSERT_TRUE(sk_SSL_CIPHER_find_awslc(server_ciphers, NULL, tls12_cipher));
  ASSERT_TRUE(sk_SSL_CIPHER_find_awslc(server_ciphers, NULL, tls13_cipher));

  SSL_set_shed_handshake_config(client.get(), 1);
  SSL_set_shed_handshake_config(server.get(), 1);

  ASSERT_TRUE(CompleteHandshakes(client.get(), server.get()));

  // Ensure we fall back to ctx once config is shed
  client_ciphers = SSL_get_ciphers(client.get());
  server_ciphers = SSL_get_ciphers(server.get());

  tls13_cipher = SSL_get_cipher_by_value(TLS1_3_CK_AES_256_GCM_SHA384 & 0xFFFF);
  tls12_cipher = SSL_get_cipher_by_value(TLS1_CK_RSA_WITH_AES_256_SHA & 0xFFFF);

  ASSERT_TRUE(sk_SSL_CIPHER_find_awslc(client_ciphers, NULL, tls13_cipher));
  ASSERT_TRUE(sk_SSL_CIPHER_find_awslc(server_ciphers, NULL, tls12_cipher));
}

TEST(SSLTest, SSLGetCiphersReturnsTLS13Default) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx =
          CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);
  // Configure only TLS 1.3.
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(server_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_3_VERSION));

  bssl::UniquePtr<SSL> client, server;
  // Have to ensure config is not shed per current implementation of SSL_get_ciphers.
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(), server_ctx.get(),
    ClientConfig(), false));

  // Ensure default TLS 1.3 Ciphersuites are present
  const SSL_CIPHER *cipher1 = SSL_get_cipher_by_value(TLS1_3_CK_AES_128_GCM_SHA256 & 0xFFFF);
  ASSERT_TRUE(cipher1);
  const SSL_CIPHER *cipher2 = SSL_get_cipher_by_value(TLS1_3_CK_AES_256_GCM_SHA384 & 0xFFFF);
  ASSERT_TRUE(cipher2);
  const SSL_CIPHER *cipher3 = SSL_get_cipher_by_value(TLS1_3_CK_CHACHA20_POLY1305_SHA256 & 0xFFFF);
  ASSERT_TRUE(cipher3);

  STACK_OF(SSL_CIPHER) *client_ciphers = SSL_get_ciphers(client.get());
  STACK_OF(SSL_CIPHER) *server_ciphers = SSL_get_ciphers(server.get());

  ASSERT_TRUE(sk_SSL_CIPHER_find_awslc(client_ciphers, NULL, cipher1));
  ASSERT_TRUE(sk_SSL_CIPHER_find_awslc(client_ciphers, NULL, cipher2));
  ASSERT_TRUE(sk_SSL_CIPHER_find_awslc(client_ciphers, NULL, cipher3));

  ASSERT_TRUE(sk_SSL_CIPHER_find_awslc(server_ciphers, NULL, cipher1));
  ASSERT_TRUE(sk_SSL_CIPHER_find_awslc(server_ciphers, NULL, cipher2));
  ASSERT_TRUE(sk_SSL_CIPHER_find_awslc(server_ciphers, NULL, cipher3));
}

TEST(SSLTest, TLS13ConfigCiphers) {
  // This configures SSL_CTX objects with default TLS 1.2 and 1.3 ciphersuites
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx =
          CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), TLS1_2_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(server_ctx.get(), TLS1_2_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_3_VERSION));

  // Restrict TLS 1.3 ciphersuite
  ASSERT_TRUE(SSL_CTX_set_ciphersuites(client_ctx.get(), "TLS_AES_128_GCM_SHA256:TLS_AES_256_GCM_SHA384"));
  ASSERT_TRUE(SSL_CTX_set_ciphersuites(server_ctx.get(), "TLS_AES_128_GCM_SHA256:TLS_AES_256_GCM_SHA384"));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(CreateClientAndServer(&client, &server, client_ctx.get(), server_ctx.get()));

  // Modify ciphersuites on the SSL object, this modifies ssl->config
  ASSERT_TRUE(SSL_set_ciphersuites(client.get(), "TLS_AES_256_GCM_SHA384"));
  ASSERT_TRUE(SSL_set_ciphersuites(server.get(), "TLS_AES_128_GCM_SHA256"));

  // Handshake should fail as config objects have no shared cipher.
  ASSERT_FALSE(CompleteHandshakes(client.get(), server.get()));
  ASSERT_EQ(ERR_GET_REASON(ERR_get_error()), SSL_R_NO_SHARED_CIPHER);

  bssl::UniquePtr<SSL> client2, server2;
  ASSERT_TRUE(CreateClientAndServer(&client2, &server2, client_ctx.get(), server_ctx.get()));

  // Modify ciphersuites on the SSL object, this modifies ssl->config
  ASSERT_TRUE(SSL_set_ciphersuites(client2.get(), "TLS_CHACHA20_POLY1305_SHA256"));
  ASSERT_TRUE(SSL_set_ciphersuites(server2.get(), "TLS_CHACHA20_POLY1305_SHA256"));

  ASSERT_TRUE(CompleteHandshakes(client2.get(), server2.get()));
  ASSERT_EQ(SSL_CIPHER_get_id(SSL_get_current_cipher(client2.get())), (uint32_t)TLS1_3_CK_CHACHA20_POLY1305_SHA256);
  ASSERT_EQ(SSL_CIPHER_get_id(SSL_get_current_cipher(server2.get())), (uint32_t)TLS1_3_CK_CHACHA20_POLY1305_SHA256);
}

TEST(SSLTest, TLS13ConfigCtxInteraction) {
  // This configures SSL_CTX objects with default TLS 1.2 and 1.3 ciphersuites
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx =
          CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), TLS1_2_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(server_ctx.get(), TLS1_2_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_3_VERSION));

  // Restrict TLS 1.3 ciphersuite on the SSL_CTX objects
  ASSERT_TRUE(SSL_CTX_set_ciphersuites(client_ctx.get(), "TLS_AES_128_GCM_SHA256"));
  ASSERT_TRUE(SSL_CTX_set_ciphersuites(server_ctx.get(), "TLS_AES_128_GCM_SHA256"));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(CreateClientAndServer(&client, &server, client_ctx.get(), server_ctx.get()));

  // Modify TLS 1.3 ciphersuites for client's SSL object, but not server
  ASSERT_TRUE(SSL_set_ciphersuites(client.get(), "TLS_AES_256_GCM_SHA384"));

  // Handshake should fail as client SSL config and server CTX objects have no
  // shared TLS 1.3 cipher.
  ASSERT_FALSE(CompleteHandshakes(client.get(), server.get()));
  ASSERT_EQ(ERR_GET_REASON(ERR_get_error()), SSL_R_NO_SHARED_CIPHER);

  ERR_clear_error();

  bssl::UniquePtr<SSL> client2, server2;
  ASSERT_TRUE(CreateClientAndServer(&client2, &server2, client_ctx.get(), server_ctx.get()));

  // Modify TLS 1.3 ciphersuites for server2 SSL object, but not client
  ASSERT_TRUE(SSL_set_ciphersuites(server2.get(), "TLS_AES_256_GCM_SHA384"));

  // Handshake should fail as server SSL config and client CTX objects have no
  // shared TLS 1.3 cipher.
  ASSERT_FALSE(CompleteHandshakes(client2.get(), server2.get()));
  ASSERT_EQ(ERR_GET_REASON(ERR_get_error()), SSL_R_NO_SHARED_CIPHER);
}

TEST(SSLTest, TLS12ConfigCiphers) {
  // This configures SSL_CTX objects with default TLS 1.2 and 1.3 ciphersuites
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx =
          CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), TLS1_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_2_VERSION));
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(server_ctx.get(), TLS1_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_2_VERSION));

  // Restrict TLS 1.2 ciphersuite
  ASSERT_TRUE(SSL_CTX_set_cipher_list(client_ctx.get(), "TLS_RSA_WITH_AES_256_CBC_SHA:TLS_RSA_WITH_AES_256_GCM_SHA384"));
  ASSERT_TRUE(SSL_CTX_set_cipher_list(server_ctx.get(), "TLS_RSA_WITH_AES_256_CBC_SHA:TLS_RSA_WITH_AES_256_GCM_SHA384"));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(CreateClientAndServer(&client, &server, client_ctx.get(), server_ctx.get()));

  // Modify ciphersuites on the SSL object and introduce mismatch, this modifies ssl->config
  ASSERT_TRUE(SSL_set_cipher_list(client.get(), "TLS_RSA_WITH_AES_256_CBC_SHA"));
  ASSERT_TRUE(SSL_set_cipher_list(server.get(), "TLS_RSA_WITH_AES_256_GCM_SHA384"));

  // Handshake should fail as config objects have no shared cipher.
  ASSERT_FALSE(CompleteHandshakes(client.get(), server.get()));
  ASSERT_EQ(ERR_GET_REASON(ERR_get_error()), SSL_R_NO_SHARED_CIPHER);

  ERR_clear_error();

  bssl::UniquePtr<SSL> client2, server2;
  ASSERT_TRUE(CreateClientAndServer(&client2, &server2, client_ctx.get(), server_ctx.get()));

  // Modify ciphersuites on the SSL object with a new third cipher, this modifies ssl->config
  ASSERT_TRUE(SSL_set_cipher_list(client2.get(), "TLS_RSA_WITH_AES_128_CBC_SHA"));
  ASSERT_TRUE(SSL_set_cipher_list(server2.get(), "TLS_RSA_WITH_AES_128_CBC_SHA"));

  ASSERT_TRUE(CompleteHandshakes(client2.get(), server2.get()));
  ASSERT_EQ(SSL_CIPHER_get_id(SSL_get_current_cipher(client2.get())), (uint32_t)TLS1_CK_RSA_WITH_AES_128_SHA);
  ASSERT_EQ(SSL_CIPHER_get_id(SSL_get_current_cipher(server2.get())), (uint32_t)TLS1_CK_RSA_WITH_AES_128_SHA);
}

TEST(SSLTest, TLS12ConfigCtxInteraction) {
  // This configures SSL_CTX objects with default TLS 1.2 and 1.3 ciphersuites
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx =
          CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), TLS1_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_2_VERSION));
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(server_ctx.get(), TLS1_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_2_VERSION));

  // Restrict TLS 1.2 ciphersuites on the SSL_CTX objects
  ASSERT_TRUE(SSL_CTX_set_cipher_list(client_ctx.get(), "TLS_RSA_WITH_AES_256_CBC_SHA"));
  ASSERT_TRUE(SSL_CTX_set_cipher_list(server_ctx.get(), "TLS_RSA_WITH_AES_256_CBC_SHA"));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(CreateClientAndServer(&client, &server, client_ctx.get(), server_ctx.get()));

  // Modify TLS 1.2 ciphersuite for client's SSL object, but not server
  ASSERT_TRUE(SSL_set_cipher_list(client.get(), "TLS_RSA_WITH_AES_256_GCM_SHA384"));

  // Handshake should fail as client SSL config and server CTX objects have no
  // shared TLS 1.2 cipher.
  ASSERT_FALSE(CompleteHandshakes(client.get(), server.get()));
  ASSERT_EQ(ERR_GET_REASON(ERR_get_error()), SSL_R_NO_SHARED_CIPHER);

  ERR_clear_error();

  bssl::UniquePtr<SSL> client2, server2;
  ASSERT_TRUE(CreateClientAndServer(&client2, &server2, client_ctx.get(), server_ctx.get()));

  // Modify TLS 1.2 ciphersuites for server2 SSL object, but not client
  ASSERT_TRUE(SSL_set_cipher_list(server2.get(), "TLS_RSA_WITH_AES_256_GCM_SHA384"));

  // Handshake should fail as server SSL config and client CTX objects have no
  // shared TLS 1.2 cipher.
  ASSERT_FALSE(CompleteHandshakes(client2.get(), server2.get()));
  ASSERT_EQ(ERR_GET_REASON(ERR_get_error()), SSL_R_NO_SHARED_CIPHER);
}

TEST(SSLTest, SSLGetCiphersReturnsTLS13Custom) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx =
          CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  // Configure custom TLS 1.3 Ciphersuites
  SSL_CTX_set_ciphersuites(server_ctx.get(), "TLS_AES_128_GCM_SHA256");
  SSL_CTX_set_ciphersuites(client_ctx.get(), "TLS_AES_128_GCM_SHA256:TLS_AES_256_GCM_SHA384");

  // Configure only TLS 1.3.
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(server_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_3_VERSION));

  bssl::UniquePtr<SSL> client, server;
  // Have to ensure config is not shed per current implementation of SSL_get_ciphers.
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(), server_ctx.get(),
    ClientConfig(), false));

  ASSERT_TRUE(CompleteHandshakes(client.get(), server.get()));
  // Ensure default TLS 1.3 Ciphersuites are present
  const SSL_CIPHER *cipher1 = SSL_get_cipher_by_value(TLS1_3_CK_AES_128_GCM_SHA256 & 0xFFFF);
  ASSERT_TRUE(cipher1);
  const SSL_CIPHER *cipher2 = SSL_get_cipher_by_value(TLS1_3_CK_AES_256_GCM_SHA384 & 0xFFFF);
  ASSERT_TRUE(cipher2);
  const SSL_CIPHER *cipher3 = SSL_get_cipher_by_value(TLS1_3_CK_CHACHA20_POLY1305_SHA256 & 0xFFFF);
  ASSERT_TRUE(cipher3);

  STACK_OF(SSL_CIPHER) *client_ciphers = SSL_get_ciphers(client.get());
  STACK_OF(SSL_CIPHER) *server_ciphers = SSL_get_ciphers(server.get());

  ASSERT_TRUE(sk_SSL_CIPHER_find_awslc(client_ciphers, NULL, cipher1));
  ASSERT_TRUE(sk_SSL_CIPHER_find_awslc(client_ciphers, NULL, cipher2));
  ASSERT_FALSE(sk_SSL_CIPHER_find_awslc(client_ciphers, NULL, cipher3));

  ASSERT_TRUE(sk_SSL_CIPHER_find_awslc(server_ciphers, NULL, cipher1));
  ASSERT_FALSE(sk_SSL_CIPHER_find_awslc(server_ciphers, NULL, cipher2));
  ASSERT_FALSE(sk_SSL_CIPHER_find_awslc(server_ciphers, NULL, cipher3));
}

TEST(SSLTest, GetClientCiphersAfterHandshakeFailure1_3) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx = CreateContextWithTestCertificate(TLS_method());

  // configure client to add fake ciphersuite
  SSL_CTX_set_grease_enabled(client_ctx.get(), 1);

  // There will be no cipher match, handshake will not succeed.
  ASSERT_TRUE(SSL_CTX_set_ciphersuites(client_ctx.get(),
                                       "TLS_AES_256_GCM_SHA384:TLS_CHACHA20_POLY1305_SHA256"));
  ASSERT_TRUE(SSL_CTX_set_ciphersuites(server_ctx.get(),
                                               "TLS_AES_128_GCM_SHA256"));

  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_3_VERSION));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(CreateClientAndServer(&client, &server,
                                    client_ctx.get(), server_ctx.get()));

  const unsigned char *tmp = nullptr;
  // Handshake not completed, getting ciphers should fail
  ASSERT_FALSE(SSL_client_hello_get0_ciphers(client.get(), &tmp));
  ASSERT_FALSE(SSL_client_hello_get0_ciphers(server.get(), &tmp));
  ASSERT_FALSE(tmp);

  // This should fail, but should be able to inspect client ciphers still
  ASSERT_FALSE(CompleteHandshakes(client.get(), server.get()));

  ASSERT_EQ(SSL_client_hello_get0_ciphers(client.get(), nullptr), (size_t) 0);

  const unsigned char expected_cipher_bytes[] = {0x13, 0x02, 0x13, 0x03};
  const unsigned char *p = nullptr;

  // Expected size is 2 bytes more than |expected_cipher_bytes| to account for
  // grease value
  ASSERT_EQ(SSL_client_hello_get0_ciphers(server.get(), &p),
            sizeof(expected_cipher_bytes) + 2);

  // Grab the first 2 bytes and check grease value
  uint16_t grease_val = CRYPTO_load_u16_be(p);
  ASSERT_FALSE(SSL_get_cipher_by_value(grease_val));

  // Sanity check for first cipher ID after grease value
  uint16_t cipher_val = CRYPTO_load_u16_be(p+2);
  ASSERT_TRUE(SSL_get_cipher_by_value((cipher_val)));

  // Check order and validity of the rest of the client cipher suites,
  // excluding the grease value (2nd byte onwards)
  ASSERT_EQ(Bytes(expected_cipher_bytes, sizeof(expected_cipher_bytes)),
            Bytes(p+2, sizeof(expected_cipher_bytes)));

  // Parsed ciphersuite list should only have 2 valid ciphersuites as configured
  // (grease value should not be included). Even though the handshake fails,
  // client cipher data should be available through the server SSL object.
  ASSERT_TRUE(sk_SSL_CIPHER_num(server.get()->client_cipher_suites.get()) == 2);
}

TEST(SSLTest, GetClientCiphers1_3) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx = CreateContextWithTestCertificate(TLS_method());

  // configure client to add fake ciphersuite
  SSL_CTX_set_grease_enabled(client_ctx.get(), 1);

  ASSERT_TRUE(SSL_CTX_set_ciphersuites(client_ctx.get(),
                                       "TLS_AES_128_GCM_SHA256:TLS_AES_256_GCM_SHA384:TLS_CHACHA20_POLY1305_SHA256"));

  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_3_VERSION));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(CreateClientAndServer(&client, &server,
                                    client_ctx.get(), server_ctx.get()));

  const unsigned char *tmp = nullptr;
  // Handshake not completed, getting ciphers should fail
  ASSERT_FALSE(SSL_client_hello_get0_ciphers(client.get(), &tmp));
  ASSERT_FALSE(SSL_client_hello_get0_ciphers(server.get(), &tmp));
  ASSERT_FALSE(tmp);

  ASSERT_TRUE(CompleteHandshakes(client.get(), server.get()));

  ASSERT_EQ(SSL_client_hello_get0_ciphers(client.get(), nullptr), (size_t) 0);

  const unsigned char expected_cipher_bytes[] = {0x13, 0x01, 0x13, 0x02, 0x13, 0x03};
  const unsigned char *p = nullptr;

  // Expected size is 2 bytes more than |expected_cipher_bytes| to account for
  // grease value
  ASSERT_EQ(SSL_client_hello_get0_ciphers(server.get(), &p),
            sizeof(expected_cipher_bytes) + 2);

  // Grab the first 2 bytes and check grease value
  uint16_t grease_val = CRYPTO_load_u16_be(p);
  ASSERT_FALSE(SSL_get_cipher_by_value(grease_val));

  // Sanity check for first cipher ID after grease value
  uint16_t cipher_val = CRYPTO_load_u16_be(p+2);
  ASSERT_TRUE(SSL_get_cipher_by_value((cipher_val)));

  // Check order and validity of the rest of the client cipher suites,
  // excluding the grease value (2nd byte onwards)
  ASSERT_EQ(Bytes(expected_cipher_bytes, sizeof(expected_cipher_bytes)),
            Bytes(p+2, sizeof(expected_cipher_bytes)));

  // Parsed ciphersuite list should only have 3 valid ciphersuites as configured
  // (grease value should not be included)
  ASSERT_TRUE(sk_SSL_CIPHER_num(server.get()->client_cipher_suites.get()) == 3);
}

TEST(SSLTest, GetClientCiphers1_2) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx =
          CreateContextWithTestCertificate(TLS_method());

  // configure client to add fake ciphersuite
  SSL_CTX_set_grease_enabled(client_ctx.get(), 1);

  ASSERT_TRUE(SSL_CTX_set_cipher_list(client_ctx.get(),
                                      "TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384:TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA"));
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), TLS1_2_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_2_VERSION));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(CreateClientAndServer(&client, &server,
                                    client_ctx.get(), server_ctx.get()));

  const unsigned char *tmp = nullptr;
  // Handshake not completed, getting ciphers should fail
  ASSERT_FALSE(SSL_client_hello_get0_ciphers(client.get(), &tmp));
  ASSERT_FALSE(SSL_client_hello_get0_ciphers(server.get(), &tmp));
  ASSERT_FALSE(tmp);

  ASSERT_TRUE(CompleteHandshakes(client.get(), server.get()));

  ASSERT_EQ(SSL_client_hello_get0_ciphers(client.get(), nullptr), (size_t) 0);

  const unsigned char expected_cipher_bytes[] = {0xC0, 0x2C, 0xC0, 0x13};
  const unsigned char *p = nullptr;

  // Expected size is 2 bytes more than |expected_cipher_bytes| to account for
  // grease value
  ASSERT_EQ(SSL_client_hello_get0_ciphers(server.get(), &p),
            sizeof(expected_cipher_bytes) + 2);

  // Grab the first 2 bytes and check grease value
  uint16_t grease_val = CRYPTO_load_u16_be(p);
  ASSERT_FALSE(SSL_get_cipher_by_value(grease_val));

  // Sanity check for first cipher ID after grease value
  uint16_t cipher_val = CRYPTO_load_u16_be(p+2);
  ASSERT_TRUE(SSL_get_cipher_by_value((cipher_val)));

  // Check order and validity of the rest of the client cipher suites,
  // excluding the grease value (2nd byte onwards)
  ASSERT_EQ(Bytes(expected_cipher_bytes, sizeof(expected_cipher_bytes)),
            Bytes(p+2, sizeof(expected_cipher_bytes)));

  // Parsed ciphersuite list should only have 2 valid ciphersuites as configured
  // (grease value should not be included)
  ASSERT_TRUE(sk_SSL_CIPHER_num(server.get()->client_cipher_suites.get()) == 2);
}


// Test that |SSL_get_client_CA_list| echoes back the configured parameter even
// before configuring as a server.
TEST(SSLTest, ClientCAList) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);

  bssl::UniquePtr<X509_NAME> name(X509_NAME_new());
  ASSERT_TRUE(name);

  bssl::UniquePtr<X509_NAME> name_dup(X509_NAME_dup(name.get()));
  ASSERT_TRUE(name_dup);

  bssl::UniquePtr<STACK_OF(X509_NAME)> stack(sk_X509_NAME_new_null());
  ASSERT_TRUE(stack);
  ASSERT_TRUE(PushToStack(stack.get(), std::move(name_dup)));

  // |SSL_set_client_CA_list| takes ownership.
  SSL_set_client_CA_list(ssl.get(), stack.release());

  STACK_OF(X509_NAME) *result = SSL_get_client_CA_list(ssl.get());
  ASSERT_TRUE(result);
  ASSERT_EQ(1u, sk_X509_NAME_num(result));
  EXPECT_EQ(0, X509_NAME_cmp(sk_X509_NAME_value(result, 0), name.get()));
}

TEST(SSLTest, AddClientCA) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);

  bssl::UniquePtr<X509> cert1 = GetTestCertificate();
  bssl::UniquePtr<X509> cert2 = GetChainTestCertificate();
  ASSERT_TRUE(cert1 && cert2);
  X509_NAME *name1 = X509_get_subject_name(cert1.get());
  X509_NAME *name2 = X509_get_subject_name(cert2.get());

  EXPECT_EQ(0u, sk_X509_NAME_num(SSL_get_client_CA_list(ssl.get())));

  ASSERT_TRUE(SSL_add_client_CA(ssl.get(), cert1.get()));
  ASSERT_TRUE(SSL_add_client_CA(ssl.get(), cert2.get()));

  STACK_OF(X509_NAME) *list = SSL_get_client_CA_list(ssl.get());
  ASSERT_EQ(2u, sk_X509_NAME_num(list));
  EXPECT_EQ(0, X509_NAME_cmp(sk_X509_NAME_value(list, 0), name1));
  EXPECT_EQ(0, X509_NAME_cmp(sk_X509_NAME_value(list, 1), name2));

  ASSERT_TRUE(SSL_add_client_CA(ssl.get(), cert1.get()));

  list = SSL_get_client_CA_list(ssl.get());
  ASSERT_EQ(3u, sk_X509_NAME_num(list));
  EXPECT_EQ(0, X509_NAME_cmp(sk_X509_NAME_value(list, 0), name1));
  EXPECT_EQ(0, X509_NAME_cmp(sk_X509_NAME_value(list, 1), name2));
  EXPECT_EQ(0, X509_NAME_cmp(sk_X509_NAME_value(list, 2), name1));
}


TEST(SSLTest, TLS13ExporterAvailability) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);
  // Configure only TLS 1.3.
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_3_VERSION));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(CreateClientAndServer(&client, &server, client_ctx.get(),
                                    server_ctx.get()));

  std::vector<uint8_t> buffer(32);
  const char *label = "EXPORTER-test-label";

  // The exporters are not available before the handshake starts.
  EXPECT_FALSE(SSL_export_keying_material(client.get(), buffer.data(),
                                          buffer.size(), label, strlen(label),
                                          nullptr, 0, 0));
  EXPECT_FALSE(SSL_export_keying_material(server.get(), buffer.data(),
                                          buffer.size(), label, strlen(label),
                                          nullptr, 0, 0));

  // Send the client's first flight of handshake messages.
  int client_ret = SSL_do_handshake(client.get());
  EXPECT_EQ(SSL_get_error(client.get(), client_ret), SSL_ERROR_WANT_READ);

  // The handshake isn't far enough for the exporters to work.
  EXPECT_FALSE(SSL_export_keying_material(client.get(), buffer.data(),
                                          buffer.size(), label, strlen(label),
                                          nullptr, 0, 0));
  EXPECT_FALSE(SSL_export_keying_material(server.get(), buffer.data(),
                                          buffer.size(), label, strlen(label),
                                          nullptr, 0, 0));

  // Send all the server's handshake messages.
  int server_ret = SSL_do_handshake(server.get());
  EXPECT_EQ(SSL_get_error(server.get(), server_ret), SSL_ERROR_WANT_READ);

  // At this point in the handshake, the server should have the exporter key
  // derived since it's sent its Finished message. The client hasn't yet
  // processed the server's handshake messages, so the exporter shouldn't be
  // available to the client.
  EXPECT_FALSE(SSL_export_keying_material(client.get(), buffer.data(),
                                          buffer.size(), label, strlen(label),
                                          nullptr, 0, 0));
  EXPECT_TRUE(SSL_export_keying_material(server.get(), buffer.data(),
                                         buffer.size(), label, strlen(label),
                                         nullptr, 0, 0));

  // Finish the handshake on the client.
  EXPECT_EQ(SSL_do_handshake(client.get()), 1);

  // The exporter should be available on both endpoints.
  EXPECT_TRUE(SSL_export_keying_material(client.get(), buffer.data(),
                                         buffer.size(), label, strlen(label),
                                         nullptr, 0, 0));
  EXPECT_TRUE(SSL_export_keying_material(server.get(), buffer.data(),
                                         buffer.size(), label, strlen(label),
                                         nullptr, 0, 0));

  // Finish the handshake on the server.
  EXPECT_EQ(SSL_do_handshake(server.get()), 1);

  // The exporter should still be available on both endpoints.
  EXPECT_TRUE(SSL_export_keying_material(client.get(), buffer.data(),
                                         buffer.size(), label, strlen(label),
                                         nullptr, 0, 0));
  EXPECT_TRUE(SSL_export_keying_material(server.get(), buffer.data(),
                                         buffer.size(), label, strlen(label),
                                         nullptr, 0, 0));
}

static void AppendSession(SSL_SESSION *session, void *arg) {
  std::vector<SSL_SESSION *> *out =
      reinterpret_cast<std::vector<SSL_SESSION *> *>(arg);
  out->push_back(session);
}

// CacheEquals returns true if |ctx|'s session cache consists of |expected|, in
// order.
static bool CacheEquals(SSL_CTX *ctx,
                        const std::vector<SSL_SESSION *> &expected) {
  // Check the linked list.
  SSL_SESSION *ptr = ctx->session_cache_head;
  for (SSL_SESSION *session : expected) {
    if (ptr != session) {
      return false;
    }
    // Redundant w/ above, but avoids static analysis failure
    if (ptr == nullptr) {
      return false;
    }
    // TODO(davidben): This is an absurd way to denote the end of the list.
    if (ptr->next ==
        reinterpret_cast<SSL_SESSION *>(&ctx->session_cache_tail)) {
      ptr = nullptr;
    } else {
      ptr = ptr->next;
    }
  }
  if (ptr != nullptr) {
    return false;
  }

  // Check the hash table.
  std::vector<SSL_SESSION *> actual, expected_copy;
  lh_SSL_SESSION_doall_arg(ctx->sessions, AppendSession, &actual);
  expected_copy = expected;

  std::sort(actual.begin(), actual.end());
  std::sort(expected_copy.begin(), expected_copy.end());

  return actual == expected_copy;
}

static bssl::UniquePtr<SSL_SESSION> CreateTestSession(uint32_t number) {
  bssl::UniquePtr<SSL_CTX> ssl_ctx(SSL_CTX_new(TLS_method()));
  if (!ssl_ctx) {
    return nullptr;
  }
  bssl::UniquePtr<SSL_SESSION> ret(SSL_SESSION_new(ssl_ctx.get()));
  if (!ret) {
    return nullptr;
  }

  uint8_t id[SSL3_SSL_SESSION_ID_LENGTH] = {0};
  OPENSSL_memcpy(id, &number, sizeof(number));
  if (!SSL_SESSION_set1_id(ret.get(), id, sizeof(id))) {
    return nullptr;
  }
  return ret;
}

// Test that the internal session cache behaves as expected.
TEST(SSLTest, InternalSessionCache) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);

  // Prepare 10 test sessions.
  std::vector<bssl::UniquePtr<SSL_SESSION>> sessions;
  for (int i = 0; i < 10; i++) {
    bssl::UniquePtr<SSL_SESSION> session = CreateTestSession(i);
    ASSERT_TRUE(session);
    sessions.push_back(std::move(session));
  }

  SSL_CTX_sess_set_cache_size(ctx.get(), 5);

  // Insert all the test sessions.
  for (const auto &session : sessions) {
    ASSERT_TRUE(SSL_CTX_add_session(ctx.get(), session.get()));
  }

  // Only the last five should be in the list.
  ASSERT_TRUE(CacheEquals(
      ctx.get(), {sessions[9].get(), sessions[8].get(), sessions[7].get(),
                  sessions[6].get(), sessions[5].get()}));

  // Inserting an element already in the cache should fail and leave the cache
  // unchanged.
  ASSERT_FALSE(SSL_CTX_add_session(ctx.get(), sessions[7].get()));
  ASSERT_TRUE(CacheEquals(
      ctx.get(), {sessions[9].get(), sessions[8].get(), sessions[7].get(),
                  sessions[6].get(), sessions[5].get()}));

  // Although collisions should be impossible (256-bit session IDs), the cache
  // must handle them gracefully.
  bssl::UniquePtr<SSL_SESSION> collision(CreateTestSession(7));
  ASSERT_TRUE(collision);
  ASSERT_TRUE(SSL_CTX_add_session(ctx.get(), collision.get()));
  ASSERT_TRUE(CacheEquals(
      ctx.get(), {collision.get(), sessions[9].get(), sessions[8].get(),
                  sessions[6].get(), sessions[5].get()}));

  // Removing sessions behaves correctly.
  ASSERT_TRUE(SSL_CTX_remove_session(ctx.get(), sessions[6].get()));
  ASSERT_TRUE(CacheEquals(ctx.get(), {collision.get(), sessions[9].get(),
                                      sessions[8].get(), sessions[5].get()}));

  // Removing sessions requires an exact match.
  ASSERT_FALSE(SSL_CTX_remove_session(ctx.get(), sessions[0].get()));
  ASSERT_FALSE(SSL_CTX_remove_session(ctx.get(), sessions[7].get()));

  // The cache remains unchanged.
  ASSERT_TRUE(CacheEquals(ctx.get(), {collision.get(), sessions[9].get(),
                                      sessions[8].get(), sessions[5].get()}));
}



static const uint8_t kTestName[] = {
    0x30, 0x45, 0x31, 0x0b, 0x30, 0x09, 0x06, 0x03, 0x55, 0x04, 0x06, 0x13,
    0x02, 0x41, 0x55, 0x31, 0x13, 0x30, 0x11, 0x06, 0x03, 0x55, 0x04, 0x08,
    0x0c, 0x0a, 0x53, 0x6f, 0x6d, 0x65, 0x2d, 0x53, 0x74, 0x61, 0x74, 0x65,
    0x31, 0x21, 0x30, 0x1f, 0x06, 0x03, 0x55, 0x04, 0x0a, 0x0c, 0x18, 0x49,
    0x6e, 0x74, 0x65, 0x72, 0x6e, 0x65, 0x74, 0x20, 0x57, 0x69, 0x64, 0x67,
    0x69, 0x74, 0x73, 0x20, 0x50, 0x74, 0x79, 0x20, 0x4c, 0x74, 0x64,
};

// Test that, after seeing TLS 1.2 in response to early data, |SSL_write|
// continues to report |SSL_R_WRONG_VERSION_ON_EARLY_DATA|. See
// https://crbug.com/1078515.
TEST(SSLTest, WriteAfterWrongVersionOnEarlyData) {
  // Set up some 0-RTT-enabled contexts.
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);
  SSL_CTX_set_early_data_enabled(client_ctx.get(), 1);
  SSL_CTX_set_early_data_enabled(server_ctx.get(), 1);
  SSL_CTX_set_session_cache_mode(client_ctx.get(), SSL_SESS_CACHE_BOTH);
  SSL_CTX_set_session_cache_mode(server_ctx.get(), SSL_SESS_CACHE_BOTH);

  // Get an early-data-capable session.
  bssl::UniquePtr<SSL_SESSION> session =
      CreateClientSession(client_ctx.get(), server_ctx.get());
  ASSERT_TRUE(session);
  EXPECT_TRUE(SSL_SESSION_early_data_capable(session.get()));

  // Offer the session to the server, but now the server speaks TLS 1.2.
  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(CreateClientAndServer(&client, &server, client_ctx.get(),
                                    server_ctx.get()));
  SSL_set_session(client.get(), session.get());
  EXPECT_TRUE(SSL_set_max_proto_version(server.get(), TLS1_2_VERSION));

  // The client handshake initially succeeds in the early data state.
  EXPECT_EQ(1, SSL_do_handshake(client.get()));
  EXPECT_TRUE(SSL_in_early_data(client.get()));

  // The server processes the ClientHello and negotiates TLS 1.2.
  EXPECT_EQ(-1, SSL_do_handshake(server.get()));
  EXPECT_EQ(SSL_ERROR_WANT_READ, SSL_get_error(server.get(), -1));
  EXPECT_EQ(TLS1_2_VERSION, SSL_version(server.get()));

  // Capture the client's output.
  bssl::UniquePtr<BIO> mem(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(mem);
  SSL_set0_wbio(client.get(), bssl::UpRef(mem).release());

  // The client processes the ServerHello and fails.
  EXPECT_EQ(-1, SSL_do_handshake(client.get()));
  EXPECT_EQ(SSL_ERROR_SSL, SSL_get_error(client.get(), -1));
  EXPECT_TRUE(ErrorEquals(ERR_get_error(), ERR_LIB_SSL,
                          SSL_R_WRONG_VERSION_ON_EARLY_DATA));

  // The client should have written an alert to the transport.
  const uint8_t *unused;
  size_t len;
  ASSERT_TRUE(BIO_mem_contents(mem.get(), &unused, &len));
  EXPECT_NE(0u, len);
  EXPECT_TRUE(BIO_reset(mem.get()));

  // Writing should fail, with the same error as the handshake.
  EXPECT_EQ(-1, SSL_write(client.get(), "a", 1));
  EXPECT_EQ(SSL_ERROR_SSL, SSL_get_error(client.get(), -1));
  EXPECT_TRUE(ErrorEquals(ERR_get_error(), ERR_LIB_SSL,
                          SSL_R_WRONG_VERSION_ON_EARLY_DATA));

  // Nothing should be written to the transport.
  ASSERT_TRUE(BIO_mem_contents(mem.get(), &unused, &len));
  EXPECT_EQ(0u, len);
}

TEST(SSLTest, SessionDuplication) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));

  SSL_SESSION *session0 = SSL_get_session(client.get());
  bssl::UniquePtr<SSL_SESSION> session1 =
      bssl::SSL_SESSION_dup(session0, SSL_SESSION_DUP_ALL);
  ASSERT_TRUE(session1);

  session1->not_resumable = false;

  uint8_t *s0_bytes, *s1_bytes;
  size_t s0_len, s1_len;

  ASSERT_TRUE(SSL_SESSION_to_bytes(session0, &s0_bytes, &s0_len));
  bssl::UniquePtr<uint8_t> free_s0(s0_bytes);

  ASSERT_TRUE(SSL_SESSION_to_bytes(session1.get(), &s1_bytes, &s1_len));
  bssl::UniquePtr<uint8_t> free_s1(s1_bytes);

  EXPECT_EQ(Bytes(s0_bytes, s0_len), Bytes(s1_bytes, s1_len));
}

static void ExpectFDs(const SSL *ssl, int rfd, int wfd) {
  EXPECT_EQ(rfd, SSL_get_fd(ssl));
  EXPECT_EQ(rfd, SSL_get_rfd(ssl));
  EXPECT_EQ(wfd, SSL_get_wfd(ssl));

  // The wrapper BIOs are always equal when fds are equal, even if set
  // individually.
  if (rfd == wfd) {
    EXPECT_EQ(SSL_get_rbio(ssl), SSL_get_wbio(ssl));
  }
}

TEST(SSLTest, SetFD) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);

  // Test setting different read and write FDs.
  bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);
  EXPECT_TRUE(SSL_set_rfd(ssl.get(), 1));
  EXPECT_TRUE(SSL_set_wfd(ssl.get(), 2));
  ExpectFDs(ssl.get(), 1, 2);

  // Test setting the same FD.
  ssl.reset(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);
  EXPECT_TRUE(SSL_set_fd(ssl.get(), 1));
  ExpectFDs(ssl.get(), 1, 1);

  // Test setting the same FD one side at a time.
  ssl.reset(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);
  EXPECT_TRUE(SSL_set_rfd(ssl.get(), 1));
  EXPECT_TRUE(SSL_set_wfd(ssl.get(), 1));
  ExpectFDs(ssl.get(), 1, 1);

  // Test setting the same FD in the other order.
  ssl.reset(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);
  EXPECT_TRUE(SSL_set_wfd(ssl.get(), 1));
  EXPECT_TRUE(SSL_set_rfd(ssl.get(), 1));
  ExpectFDs(ssl.get(), 1, 1);

  // Test changing the read FD partway through.
  ssl.reset(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);
  EXPECT_TRUE(SSL_set_fd(ssl.get(), 1));
  EXPECT_TRUE(SSL_set_rfd(ssl.get(), 2));
  ExpectFDs(ssl.get(), 2, 1);

  // Test changing the write FD partway through.
  ssl.reset(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);
  EXPECT_TRUE(SSL_set_fd(ssl.get(), 1));
  EXPECT_TRUE(SSL_set_wfd(ssl.get(), 2));
  ExpectFDs(ssl.get(), 1, 2);

  // Test a no-op change to the read FD partway through.
  ssl.reset(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);
  EXPECT_TRUE(SSL_set_fd(ssl.get(), 1));
  EXPECT_TRUE(SSL_set_rfd(ssl.get(), 1));
  ExpectFDs(ssl.get(), 1, 1);

  // Test a no-op change to the write FD partway through.
  ssl.reset(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);
  EXPECT_TRUE(SSL_set_fd(ssl.get(), 1));
  EXPECT_TRUE(SSL_set_wfd(ssl.get(), 1));
  ExpectFDs(ssl.get(), 1, 1);

  // ASan builds will implicitly test that the internal |BIO| reference-counting
  // is correct.
}

TEST(SSLTest, SetBIO) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);

  bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
  bssl::UniquePtr<BIO> bio1(BIO_new(BIO_s_mem())), bio2(BIO_new(BIO_s_mem())),
      bio3(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(ssl);
  ASSERT_TRUE(bio1);
  ASSERT_TRUE(bio2);
  ASSERT_TRUE(bio3);

  // SSL_set_bio takes one reference when the parameters are the same.
  BIO_up_ref(bio1.get());
  SSL_set_bio(ssl.get(), bio1.get(), bio1.get());

  // Repeating the call does nothing.
  SSL_set_bio(ssl.get(), bio1.get(), bio1.get());

  // It takes one reference each when the parameters are different.
  BIO_up_ref(bio2.get());
  BIO_up_ref(bio3.get());
  SSL_set_bio(ssl.get(), bio2.get(), bio3.get());

  // Repeating the call does nothing.
  SSL_set_bio(ssl.get(), bio2.get(), bio3.get());

  // It takes one reference when changing only wbio.
  BIO_up_ref(bio1.get());
  SSL_set_bio(ssl.get(), bio2.get(), bio1.get());

  // It takes one reference when changing only rbio and the two are different.
  BIO_up_ref(bio3.get());
  SSL_set_bio(ssl.get(), bio3.get(), bio1.get());

  // If setting wbio to rbio, it takes no additional references.
  SSL_set_bio(ssl.get(), bio3.get(), bio3.get());

  // From there, wbio may be switched to something else.
  BIO_up_ref(bio1.get());
  SSL_set_bio(ssl.get(), bio3.get(), bio1.get());

  // If setting rbio to wbio, it takes no additional references.
  SSL_set_bio(ssl.get(), bio1.get(), bio1.get());

  // From there, rbio may be switched to something else, but, for historical
  // reasons, it takes a reference to both parameters.
  BIO_up_ref(bio1.get());
  BIO_up_ref(bio2.get());
  SSL_set_bio(ssl.get(), bio2.get(), bio1.get());

  // ASAN builds will implicitly test that the internal |BIO| reference-counting
  // is correct.
}



// Tests that our ClientHellos do not change unexpectedly. These are purely
// change detection tests. If they fail as part of an intentional ClientHello
// change, update the test vector.
TEST(SSLTest, ClientHello) {
  struct {
    uint16_t max_version;
    std::vector<uint8_t> expected;
  } kTests[] = {
    {TLS1_VERSION,
     {0x16, 0x03, 0x01, 0x00, 0x58, 0x01, 0x00, 0x00, 0x54, 0x03, 0x01, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0c, 0xc0, 0x09,
      0xc0, 0x13, 0xc0, 0x0a, 0xc0, 0x14, 0x00, 0x2f, 0x00, 0x35, 0x01, 0x00,
      0x00, 0x1f, 0x00, 0x17, 0x00, 0x00, 0xff, 0x01, 0x00, 0x01, 0x00, 0x00,
      0x0a, 0x00, 0x08, 0x00, 0x06, 0x00, 0x1d, 0x00, 0x17, 0x00, 0x18, 0x00,
      0x0b, 0x00, 0x02, 0x01, 0x00, 0x00, 0x23, 0x00, 0x00}},
    {TLS1_1_VERSION,
     {0x16, 0x03, 0x01, 0x00, 0x58, 0x01, 0x00, 0x00, 0x54, 0x03, 0x02, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0c, 0xc0, 0x09,
      0xc0, 0x13, 0xc0, 0x0a, 0xc0, 0x14, 0x00, 0x2f, 0x00, 0x35, 0x01, 0x00,
      0x00, 0x1f, 0x00, 0x17, 0x00, 0x00, 0xff, 0x01, 0x00, 0x01, 0x00, 0x00,
      0x0a, 0x00, 0x08, 0x00, 0x06, 0x00, 0x1d, 0x00, 0x17, 0x00, 0x18, 0x00,
      0x0b, 0x00, 0x02, 0x01, 0x00, 0x00, 0x23, 0x00, 0x00}},
    {TLS1_2_VERSION,
     {0x16, 0x03, 0x01, 0x00, 0x86, 0x01, 0x00, 0x00, 0x82, 0x03, 0x03, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x22, 0xcc, 0xa9,
      0xcc, 0xa8, 0xc0, 0x2b, 0xc0, 0x2f, 0xc0, 0x2c, 0xc0, 0x30, 0xc0, 0x09,
      0xc0, 0x13, 0xc0, 0x27, 0xc0, 0x0a, 0xc0, 0x14, 0xc0, 0x28, 0x00, 0x9c,
      0x00, 0x9d, 0x00, 0x2f, 0x00, 0x3c, 0x00, 0x35, 0x01, 0x00, 0x00, 0x37,
      0x00, 0x17, 0x00, 0x00, 0xff, 0x01, 0x00, 0x01, 0x00, 0x00, 0x0a, 0x00,
      0x08, 0x00, 0x06, 0x00, 0x1d, 0x00, 0x17, 0x00, 0x18, 0x00, 0x0b, 0x00,
      0x02, 0x01, 0x00, 0x00, 0x23, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x14, 0x00,
      0x12, 0x04, 0x03, 0x08, 0x04, 0x04, 0x01, 0x05, 0x03, 0x08, 0x05, 0x05,
      0x01, 0x08, 0x06, 0x06, 0x01, 0x02, 0x01}},
    {TLS1_3_VERSION,
     {0x16, 0x03, 0x01, 0x00, 0xe9, 0x01, 0x00, 0x00, 0xe5, 0x03, 0x03, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x28, 0x13, 0x01, 0x13, 0x02, 0x13, 0x03,
      0xcc, 0xa9, 0xcc, 0xa8, 0xc0, 0x2b, 0xc0, 0x2f, 0xc0, 0x2c, 0xc0, 0x30,
      0xc0, 0x09, 0xc0, 0x13, 0xc0, 0x27, 0xc0, 0x0a, 0xc0, 0x14, 0xc0, 0x28,
      0x00, 0x9c, 0x00, 0x9d, 0x00, 0x2f, 0x00, 0x3c, 0x00, 0x35, 0x01, 0x00,
      0x00, 0x74, 0x00, 0x17, 0x00, 0x00, 0xff, 0x01, 0x00, 0x01, 0x00, 0x00,
      0x0a, 0x00, 0x08, 0x00, 0x06, 0x00, 0x1d, 0x00, 0x17, 0x00, 0x18, 0x00,
      0x0b, 0x00, 0x02, 0x01, 0x00, 0x00, 0x23, 0x00, 0x00, 0x00, 0x0d, 0x00,
      0x14, 0x00, 0x12, 0x04, 0x03, 0x08, 0x04, 0x04, 0x01, 0x05, 0x03, 0x08,
      0x05, 0x05, 0x01, 0x08, 0x06, 0x06, 0x01, 0x02, 0x01, 0x00, 0x33, 0x00,
      0x26, 0x00, 0x24, 0x00, 0x1d, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x2d, 0x00, 0x02, 0x01, 0x01, 0x00, 0x2b, 0x00,
      0x09, 0x08, 0x03, 0x04, 0x03, 0x03, 0x03, 0x02, 0x03, 0x01}}
  };

  for (const auto &t : kTests) {
    SCOPED_TRACE(t.max_version);

    bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ctx);
    // Our default cipher list varies by CPU capabilities, so manually place the
    // ChaCha20 ciphers in front.
    const char *cipher_list = "CHACHA20:ALL";
    ASSERT_TRUE(SSL_CTX_set_max_proto_version(ctx.get(), t.max_version));
    ASSERT_TRUE(SSL_CTX_set_strict_cipher_list(ctx.get(), cipher_list));

    // Explicitly set TLS 1.3 ciphersuites so CPU capabilities don't affect order
    ASSERT_TRUE(SSL_CTX_set_ciphersuites(ctx.get(), TLS13_DEFAULT_CIPHER_LIST_AES_HW));

    bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
    ASSERT_TRUE(ssl);
    std::vector<uint8_t> client_hello;
    ASSERT_TRUE(GetClientHello(ssl.get(), &client_hello));

    // Zero the client_random.
    constexpr size_t kRandomOffset = 1 + 2 + 2 +  // record header
                                     1 + 3 +      // handshake message header
                                     2;           // client_version

    int pre = client_hello.size();
    if (t.max_version == TLS1_3_VERSION) {
      ASSERT_GE(client_hello.size(), kRandomOffset + SSL3_RANDOM_SIZE + 1 + SSL3_SESSION_ID_SIZE);
      OPENSSL_memset(client_hello.data() + kRandomOffset, 0, SSL3_RANDOM_SIZE + 1  + SSL3_SESSION_ID_SIZE);
      // Jump to key share extension and zero out the key
      OPENSSL_memset(client_hello.data() + 187, 0, 32);
    } else {
      ASSERT_GE(client_hello.size(), kRandomOffset + SSL3_RANDOM_SIZE);
      OPENSSL_memset(client_hello.data() + kRandomOffset, 0, SSL3_RANDOM_SIZE);
    }
    int post = client_hello.size();
    ASSERT_EQ(pre, post);

    if (client_hello != t.expected) {
      ADD_FAILURE() << "ClientHellos did not match.";
      // Print the value manually so it is easier to update the test vector.
      for (size_t i = 0; i < client_hello.size(); i += 12) {
        printf("     %c", i == 0 ? '{' : ' ');
        for (size_t j = i; j < client_hello.size() && j < i + 12; j++) {
          if (j > i) {
            printf(" ");
          }
          printf("0x%02x", client_hello[j]);
          if (j < client_hello.size() - 1) {
            printf(",");
          }
        }
        if (i + 12 >= client_hello.size()) {
          printf("}},");
        }
        printf("\n");
      }
    }
  }
}




// Test that the early callback can swap the maximum version.
TEST(SSLTest, EarlyCallbackVersionSwitch) {
  bssl::UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(server_ctx);
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_3_VERSION));

  SSL_CTX_set_select_certificate_cb(
      server_ctx.get(),
      [](const SSL_CLIENT_HELLO *client_hello) -> ssl_select_cert_result_t {
        if (!SSL_set_max_proto_version(client_hello->ssl, TLS1_2_VERSION)) {
          return ssl_select_cert_error;
        }

        return ssl_select_cert_success;
      });

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));
  EXPECT_EQ(TLS1_2_VERSION, SSL_version(client.get()));
}

TEST(SSLTest, SetVersion) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);

  // Set valid TLS versions.
  for (const auto &vers : kAllVersions) {
    SCOPED_TRACE(vers.name);
    if (vers.ssl_method == VersionParam::is_tls) {
      EXPECT_TRUE(SSL_CTX_set_max_proto_version(ctx.get(), vers.version));
      EXPECT_EQ(SSL_CTX_get_max_proto_version(ctx.get()), vers.version);
      EXPECT_TRUE(SSL_CTX_set_min_proto_version(ctx.get(), vers.version));
      EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), vers.version);
      EXPECT_TRUE(SSL_set_max_proto_version(ssl.get(), vers.version));
      EXPECT_EQ(SSL_get_max_proto_version(ssl.get()), vers.version);
      EXPECT_TRUE(SSL_set_min_proto_version(ssl.get(), vers.version));
      EXPECT_EQ(SSL_get_min_proto_version(ssl.get()), vers.version);
    }
  }

  // Invalid TLS versions are rejected.
  EXPECT_FALSE(SSL_CTX_set_max_proto_version(ctx.get(), DTLS1_VERSION));
  EXPECT_FALSE(SSL_CTX_set_max_proto_version(ctx.get(), 0x0200));
  EXPECT_FALSE(SSL_CTX_set_max_proto_version(ctx.get(), 0x1234));
  EXPECT_FALSE(SSL_CTX_set_min_proto_version(ctx.get(), DTLS1_VERSION));
  EXPECT_FALSE(SSL_CTX_set_min_proto_version(ctx.get(), 0x0200));
  EXPECT_FALSE(SSL_CTX_set_min_proto_version(ctx.get(), 0x1234));
  EXPECT_FALSE(SSL_set_max_proto_version(ssl.get(), 0x0200));
  EXPECT_FALSE(SSL_set_max_proto_version(ssl.get(), 0x1234));
  EXPECT_FALSE(SSL_set_min_proto_version(ssl.get(), DTLS1_VERSION));
  EXPECT_FALSE(SSL_set_min_proto_version(ssl.get(), 0x0200));
  EXPECT_FALSE(SSL_set_min_proto_version(ssl.get(), 0x1234));

  // Zero represents the default version.
  EXPECT_TRUE(SSL_CTX_set_max_proto_version(ctx.get(), 0));
  EXPECT_EQ(0, SSL_CTX_get_max_proto_version(ctx.get()));
  EXPECT_TRUE(SSL_CTX_set_min_proto_version(ctx.get(), 0));
  EXPECT_EQ(0, SSL_CTX_get_min_proto_version(ctx.get()));
  EXPECT_TRUE(SSL_set_max_proto_version(ssl.get(), 0));
  EXPECT_EQ(0, SSL_get_max_proto_version(ssl.get()));
  EXPECT_TRUE(SSL_set_min_proto_version(ssl.get(), 0));
  EXPECT_EQ(0, SSL_get_min_proto_version(ssl.get()));

  // SSL 3.0 is not available.
  EXPECT_FALSE(SSL_CTX_set_min_proto_version(ctx.get(), SSL3_VERSION));
  EXPECT_FALSE(SSL_set_min_proto_version(ssl.get(), SSL3_VERSION));

  ctx.reset(SSL_CTX_new(DTLS_method()));
  ASSERT_TRUE(ctx);
  ssl.reset(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);

  // Set valid DTLS versions.
  for (const auto &vers : kAllVersions) {
    SCOPED_TRACE(vers.name);
    if (vers.ssl_method == VersionParam::is_dtls) {
      EXPECT_TRUE(SSL_CTX_set_max_proto_version(ctx.get(), vers.version));
      EXPECT_EQ(SSL_CTX_get_max_proto_version(ctx.get()), vers.version);
      EXPECT_TRUE(SSL_CTX_set_min_proto_version(ctx.get(), vers.version));
      EXPECT_EQ(SSL_CTX_get_min_proto_version(ctx.get()), vers.version);
    }
  }

  // Invalid DTLS versions are rejected.
  EXPECT_FALSE(SSL_CTX_set_max_proto_version(ctx.get(), TLS1_VERSION));
  EXPECT_FALSE(SSL_CTX_set_max_proto_version(ctx.get(), 0xfefe /* DTLS 1.1 */));
  EXPECT_FALSE(SSL_CTX_set_max_proto_version(ctx.get(), 0xfffe /* DTLS 0.1 */));
  EXPECT_FALSE(SSL_CTX_set_max_proto_version(ctx.get(), 0x1234));
  EXPECT_FALSE(SSL_CTX_set_min_proto_version(ctx.get(), TLS1_VERSION));
  EXPECT_FALSE(SSL_CTX_set_min_proto_version(ctx.get(), 0xfefe /* DTLS 1.1 */));
  EXPECT_FALSE(SSL_CTX_set_min_proto_version(ctx.get(), 0xfffe /* DTLS 0.1 */));
  EXPECT_FALSE(SSL_CTX_set_min_proto_version(ctx.get(), 0x1234));

  // Zero represents the default version.
  EXPECT_TRUE(SSL_CTX_set_max_proto_version(ctx.get(), 0));
  EXPECT_EQ(0, SSL_CTX_get_max_proto_version(ctx.get()));
  EXPECT_TRUE(SSL_CTX_set_min_proto_version(ctx.get(), 0));
  EXPECT_EQ(0, SSL_CTX_get_min_proto_version(ctx.get()));
}





TEST(SSLTest, BuildCertChain) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));

  // No certificate set, so this should fail.
  EXPECT_FALSE(SSL_CTX_build_cert_chain(ctx.get(), 0));
  EXPECT_TRUE(ExpectSingleError(ERR_LIB_SSL, SSL_R_NO_CERTIFICATE_SET));

  ASSERT_TRUE(SSL_CTX_use_certificate(ctx.get(), GetLeafPublic().get()));
  ASSERT_TRUE(SSL_CTX_use_PrivateKey(ctx.get(), GetLeafKey().get()));

  // Verification will fail because there is no valid root cert available.
  EXPECT_FALSE(SSL_CTX_build_cert_chain(ctx.get(), 0));
  ERR_clear_error();

  // Should return 2 when |SSL_BUILD_CHAIN_FLAG_IGNORE_ERROR| is set.
  EXPECT_EQ(
      SSL_CTX_build_cert_chain(ctx.get(), SSL_BUILD_CHAIN_FLAG_IGNORE_ERROR),
      2);
  EXPECT_TRUE(ExpectSingleError(ERR_LIB_SSL, SSL_R_CERTIFICATE_VERIFY_FAILED));
  ERR_clear_error();

  // Should return 2, but with no error on the stack when
  // |SSL_BUILD_CHAIN_FLAG_IGNORE_ERROR| and |SSL_BUILD_CHAIN_FLAG_CLEAR_ERROR|
  // are set.
  EXPECT_EQ(
      SSL_CTX_build_cert_chain(ctx.get(), SSL_BUILD_CHAIN_FLAG_IGNORE_ERROR |
                                              SSL_BUILD_CHAIN_FLAG_CLEAR_ERROR),
      2);
  EXPECT_FALSE(ERR_get_error());

  // Pass in the trust store. |SSL_CTX_build_cert_chain| should succeed now.
  ASSERT_TRUE(X509_STORE_add_cert(SSL_CTX_get_cert_store(ctx.get()),
                                  GetLeafRoot().get()));
  X509_VERIFY_PARAM_set_flags(SSL_CTX_get0_param(ctx.get()),
                              X509_V_FLAG_NO_CHECK_TIME);
  EXPECT_EQ(SSL_CTX_build_cert_chain(ctx.get(), 0), 1);
  STACK_OF(X509) *chain;
  ASSERT_TRUE(SSL_CTX_get0_chain_certs(ctx.get(), &chain));
  EXPECT_TRUE(ChainsEqual(chain, {GetLeafRoot().get()}));

  // Root cert is self-signed, so |SSL_BUILD_CHAIN_FLAG_UNTRUSTED| will
  // still pass.
  ASSERT_TRUE(SSL_CTX_clear_chain_certs(ctx.get()));
  EXPECT_TRUE(
      SSL_CTX_build_cert_chain(ctx.get(), SSL_BUILD_CHAIN_FLAG_UNTRUSTED));
  ASSERT_TRUE(SSL_CTX_get0_chain_certs(ctx.get(), &chain));
  EXPECT_TRUE(ChainsEqual(chain, {GetLeafRoot().get()}));

  // |SSL_BUILD_CHAIN_FLAG_CHECK| uses the already built cert chain as the trust
  // store and verifies against it. If we clear the cert chain, there should be
  // no trust store to compare against if |SSL_BUILD_CHAIN_FLAG_CHECK| is still
  // set.
  EXPECT_EQ(SSL_CTX_build_cert_chain(ctx.get(), SSL_BUILD_CHAIN_FLAG_CHECK), 1);
  ASSERT_TRUE(SSL_CTX_clear_chain_certs(ctx.get()));
  EXPECT_FALSE(SSL_CTX_build_cert_chain(ctx.get(), SSL_BUILD_CHAIN_FLAG_CHECK));
  EXPECT_TRUE(ExpectSingleError(ERR_LIB_SSL, SSL_R_CERTIFICATE_VERIFY_FAILED));

  // |SSL_BUILD_CHAIN_FLAG_CHECK| and |SSL_BUILD_CHAIN_FLAG_UNTRUSTED| are
  // mutually exclusive, with |SSL_BUILD_CHAIN_FLAG_CHECK| taking priority.
  // The result with both set should be the same as only
  // |SSL_BUILD_CHAIN_FLAG_CHECK| being set.
  ASSERT_TRUE(SSL_CTX_clear_chain_certs(ctx.get()));
  EXPECT_FALSE(SSL_CTX_build_cert_chain(
      ctx.get(), SSL_BUILD_CHAIN_FLAG_CHECK | SSL_BUILD_CHAIN_FLAG_UNTRUSTED));
  EXPECT_FALSE(SSL_CTX_build_cert_chain(ctx.get(), SSL_BUILD_CHAIN_FLAG_CHECK));
  // First call with |SSL_BUILD_CHAIN_FLAG_CHECK| existing will fail, second
  // call with |SSL_BUILD_CHAIN_FLAG_UNTRUSTED| will succeed.
  EXPECT_FALSE(SSL_CTX_build_cert_chain(
      ctx.get(), SSL_BUILD_CHAIN_FLAG_CHECK | SSL_BUILD_CHAIN_FLAG_UNTRUSTED));
  EXPECT_EQ(SSL_CTX_build_cert_chain(ctx.get(), SSL_BUILD_CHAIN_FLAG_UNTRUSTED),
            1);
  // |SSL_BUILD_CHAIN_FLAG_CHECK| will succeed since we have a built chain now.
  EXPECT_EQ(SSL_CTX_build_cert_chain(ctx.get(), SSL_BUILD_CHAIN_FLAG_CHECK), 1);

  // Test that successful verification with |SSL_BUILD_CHAIN_FLAG_IGNORE_ERROR|
  // does not return 2.
  ASSERT_TRUE(SSL_CTX_clear_chain_certs(ctx.get()));
  EXPECT_EQ(
      SSL_CTX_build_cert_chain(ctx.get(), SSL_BUILD_CHAIN_FLAG_IGNORE_ERROR),
      1);

  // Test that successful verification with |SSL_BUILD_CHAIN_FLAG_NO_ROOT|
  // does include the root cert.
  ASSERT_TRUE(SSL_CTX_clear_chain_certs(ctx.get()));
  EXPECT_EQ(SSL_CTX_build_cert_chain(ctx.get(), SSL_BUILD_CHAIN_FLAG_NO_ROOT),
            1);
  ASSERT_TRUE(SSL_CTX_get0_chain_certs(ctx.get(), &chain));
  EXPECT_TRUE(ChainsEqual(chain, {}));
}

TEST(SSLTest, AddChainCertHack) {
  // Ensure that we don't accidently break the hack that we have in place to
  // keep curl and serf happy when they use an |X509| even after transfering
  // ownership.

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  X509 *cert = GetTestCertificate().release();
  ASSERT_TRUE(cert);
  SSL_CTX_add0_chain_cert(ctx.get(), cert);

  // This should not trigger a use-after-free.
  X509_cmp(cert, cert);
}

TEST(SSLTest, GetCertificate) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  bssl::UniquePtr<X509> cert = GetTestCertificate();
  ASSERT_TRUE(cert);
  ASSERT_TRUE(SSL_CTX_use_certificate(ctx.get(), cert.get()));
  bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);

  X509 *cert2 = SSL_CTX_get0_certificate(ctx.get());
  ASSERT_TRUE(cert2);

  X509 *cert3 = SSL_get_certificate(ssl.get());
  ASSERT_TRUE(cert3);

  // The old and new certificates must be identical.
  EXPECT_EQ(0, X509_cmp(cert.get(), cert2));
  EXPECT_EQ(0, X509_cmp(cert.get(), cert3));

  uint8_t *der = nullptr;
  long der_len = i2d_X509(cert.get(), &der);
  ASSERT_LT(0, der_len);
  bssl::UniquePtr<uint8_t> free_der(der);

  uint8_t *der2 = nullptr;
  long der2_len = i2d_X509(cert2, &der2);
  ASSERT_LT(0, der2_len);
  bssl::UniquePtr<uint8_t> free_der2(der2);

  uint8_t *der3 = nullptr;
  long der3_len = i2d_X509(cert3, &der3);
  ASSERT_LT(0, der3_len);
  bssl::UniquePtr<uint8_t> free_der3(der3);

  // They must also encode identically.
  EXPECT_EQ(Bytes(der, der_len), Bytes(der2, der2_len));
  EXPECT_EQ(Bytes(der, der_len), Bytes(der3, der3_len));
}

TEST(SSLTest, GetCertificateExData) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  bssl::UniquePtr<X509> cert = GetTestCertificate();
  ASSERT_TRUE(cert);

  int ex_data_index =
      X509_get_ex_new_index(0, nullptr, nullptr, nullptr, nullptr);
  const char ex_data[] = "AWS-LC external data";
  ASSERT_TRUE(X509_set_ex_data(cert.get(), ex_data_index, (void *)ex_data));
  ASSERT_TRUE(X509_get_ex_data(cert.get(), ex_data_index));

  ASSERT_TRUE(SSL_CTX_use_certificate(ctx.get(), cert.get()));
  bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);

  X509 *cert2 = SSL_CTX_get0_certificate(ctx.get());
  ASSERT_TRUE(cert2);
  const char *ex_data2 = (const char *)X509_get_ex_data(cert2, ex_data_index);
  EXPECT_TRUE(ex_data2);

  X509 *cert3 = SSL_get_certificate(ssl.get());
  ASSERT_TRUE(cert3);
  const char *ex_data3 = (const char *)X509_get_ex_data(cert3, ex_data_index);
  EXPECT_TRUE(ex_data3);

  // The external data extracted must be identical.
  EXPECT_EQ(ex_data2, ex_data);
  EXPECT_EQ(ex_data3, ex_data);
}

TEST(SSLTest, GetCertificateASN1) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  bssl::UniquePtr<X509> cert = GetTestCertificate();
  ASSERT_TRUE(cert);

  // Convert cert to ASN1 to pass in.
  uint8_t *der = nullptr;
  size_t der_len = i2d_X509(cert.get(), &der);
  bssl::UniquePtr<uint8_t> free_der(der);

  ASSERT_TRUE(SSL_CTX_use_certificate_ASN1(ctx.get(), der_len, der));
  bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);

  X509 *cert2 = SSL_CTX_get0_certificate(ctx.get());
  ASSERT_TRUE(cert2);

  X509 *cert3 = SSL_get_certificate(ssl.get());
  ASSERT_TRUE(cert3);

  // The old and new certificates must be identical.
  EXPECT_EQ(0, X509_cmp(cert.get(), cert2));
  EXPECT_EQ(0, X509_cmp(cert.get(), cert3));

  uint8_t *der2 = nullptr;
  long der2_len = i2d_X509(cert2, &der2);
  ASSERT_LT(0, der2_len);
  bssl::UniquePtr<uint8_t> free_der2(der2);

  uint8_t *der3 = nullptr;
  long der3_len = i2d_X509(cert3, &der3);
  ASSERT_LT(0, der3_len);
  bssl::UniquePtr<uint8_t> free_der3(der3);

  // They must also encode identically.
  EXPECT_EQ(Bytes(der, der_len), Bytes(der2, der2_len));
  EXPECT_EQ(Bytes(der, der_len), Bytes(der3, der3_len));
}

TEST(SSLTest, SetChainAndKeyMismatch) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_with_buffers_method()));
  ASSERT_TRUE(ctx);

  bssl::UniquePtr<EVP_PKEY> key = GetTestKey();
  ASSERT_TRUE(key);
  bssl::UniquePtr<CRYPTO_BUFFER> leaf = GetChainTestCertificateBuffer();
  ASSERT_TRUE(leaf);
  std::vector<CRYPTO_BUFFER *> chain = {
      leaf.get(),
  };

  // Should fail because |GetTestKey| doesn't match the chain-test certificate.
  ASSERT_FALSE(SSL_CTX_set_chain_and_key(ctx.get(), &chain[0], chain.size(),
                                         key.get(), nullptr));
  ERR_clear_error();

  // Ensure |SSL_CTX_use_cert_and_key| also fails
  bssl::UniquePtr<X509> x509_leaf = X509FromBuffer(GetChainTestCertificateBuffer());
  ASSERT_FALSE(SSL_CTX_use_cert_and_key(ctx.get(), x509_leaf.get(),
                                        key.get(), NULL, 1));
  ERR_clear_error();
}

TEST(SSLTest, SetChainAndKey) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_with_buffers_method()));
  ASSERT_TRUE(client_ctx);
  bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_with_buffers_method()));
  ASSERT_TRUE(server_ctx);

  ASSERT_EQ(nullptr, SSL_CTX_get0_chain(server_ctx.get()));

  bssl::UniquePtr<EVP_PKEY> key = GetChainTestKey();
  ASSERT_TRUE(key);
  bssl::UniquePtr<CRYPTO_BUFFER> leaf = GetChainTestCertificateBuffer();
  ASSERT_TRUE(leaf);
  bssl::UniquePtr<CRYPTO_BUFFER> intermediate =
      GetChainTestIntermediateBuffer();
  ASSERT_TRUE(intermediate);
  std::vector<CRYPTO_BUFFER *> chain = {
      leaf.get(),
      intermediate.get(),
  };
  ASSERT_TRUE(SSL_CTX_set_chain_and_key(server_ctx.get(), &chain[0],
                                        chain.size(), key.get(), nullptr));

  ASSERT_EQ(chain.size(),
            sk_CRYPTO_BUFFER_num(SSL_CTX_get0_chain(server_ctx.get())));

  SSL_CTX_set_custom_verify(
      client_ctx.get(), SSL_VERIFY_PEER,
      [](SSL *ssl, uint8_t *out_alert) -> ssl_verify_result_t {
        return ssl_verify_ok;
      });

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));
}

TEST(SSLTest, SetLeafChainAndKey) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(client_ctx);
  bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(server_ctx);

  ASSERT_EQ(nullptr, SSL_CTX_get0_chain(server_ctx.get()));

  bssl::UniquePtr<EVP_PKEY> key = GetChainTestKey();
  ASSERT_TRUE(key);
  bssl::UniquePtr<X509> leaf = GetChainTestCertificate();
  ASSERT_TRUE(leaf);
  bssl::UniquePtr<X509> intermediate = GetChainTestIntermediate();
  bssl::UniquePtr<STACK_OF(X509)> chain(sk_X509_new_null());
  ASSERT_TRUE(chain);
  ASSERT_TRUE(PushToStack(chain.get(), std::move(intermediate)));

  ASSERT_TRUE(SSL_CTX_use_cert_and_key(server_ctx.get(), leaf.get(),
                                        key.get(), chain.get(), 1));

  SSL_CTX_set_custom_verify(
      client_ctx.get(), SSL_VERIFY_PEER,
      [](SSL *ssl, uint8_t *out_alert) -> ssl_verify_result_t {
        return ssl_verify_ok;
      });

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));

  // Try setting on previously populated fields without an override
  ASSERT_FALSE(SSL_CTX_use_cert_and_key(server_ctx.get(), leaf.get(),
                                        key.get(), chain.get(), 0));
  ERR_clear_error();
}

TEST(SSLTest, BuffersFailWithoutCustomVerify) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_with_buffers_method()));
  ASSERT_TRUE(client_ctx);
  bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_with_buffers_method()));
  ASSERT_TRUE(server_ctx);

  bssl::UniquePtr<EVP_PKEY> key = GetChainTestKey();
  ASSERT_TRUE(key);
  bssl::UniquePtr<CRYPTO_BUFFER> leaf = GetChainTestCertificateBuffer();
  ASSERT_TRUE(leaf);
  std::vector<CRYPTO_BUFFER *> chain = {leaf.get()};
  ASSERT_TRUE(SSL_CTX_set_chain_and_key(server_ctx.get(), &chain[0],
                                        chain.size(), key.get(), nullptr));

  // Without SSL_CTX_set_custom_verify(), i.e. with everything in the default
  // configuration, certificate verification should fail.
  bssl::UniquePtr<SSL> client, server;
  ASSERT_FALSE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                      server_ctx.get()));

  // Whereas with a verifier, the connection should succeed.
  SSL_CTX_set_custom_verify(
      client_ctx.get(), SSL_VERIFY_PEER,
      [](SSL *ssl, uint8_t *out_alert) -> ssl_verify_result_t {
        return ssl_verify_ok;
      });
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));
}

TEST(SSLTest, CustomVerify) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_with_buffers_method()));
  ASSERT_TRUE(client_ctx);
  bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_with_buffers_method()));
  ASSERT_TRUE(server_ctx);

  bssl::UniquePtr<EVP_PKEY> key = GetChainTestKey();
  ASSERT_TRUE(key);
  bssl::UniquePtr<CRYPTO_BUFFER> leaf = GetChainTestCertificateBuffer();
  ASSERT_TRUE(leaf);
  std::vector<CRYPTO_BUFFER *> chain = {leaf.get()};
  ASSERT_TRUE(SSL_CTX_set_chain_and_key(server_ctx.get(), &chain[0],
                                        chain.size(), key.get(), nullptr));

  SSL_CTX_set_custom_verify(
      client_ctx.get(), SSL_VERIFY_PEER,
      [](SSL *ssl, uint8_t *out_alert) -> ssl_verify_result_t {
        return ssl_verify_ok;
      });

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));

  // With SSL_VERIFY_PEER, ssl_verify_invalid should result in a dropped
  // connection.
  SSL_CTX_set_custom_verify(
      client_ctx.get(), SSL_VERIFY_PEER,
      [](SSL *ssl, uint8_t *out_alert) -> ssl_verify_result_t {
        return ssl_verify_invalid;
      });

  ASSERT_FALSE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                      server_ctx.get()));

  // But with SSL_VERIFY_NONE, ssl_verify_invalid should not cause a dropped
  // connection.
  SSL_CTX_set_custom_verify(
      client_ctx.get(), SSL_VERIFY_NONE,
      [](SSL *ssl, uint8_t *out_alert) -> ssl_verify_result_t {
        return ssl_verify_invalid;
      });

  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));
}

TEST(SSLTest, ClientCABuffers) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_with_buffers_method()));
  ASSERT_TRUE(client_ctx);
  bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_with_buffers_method()));
  ASSERT_TRUE(server_ctx);

  bssl::UniquePtr<EVP_PKEY> key = GetChainTestKey();
  ASSERT_TRUE(key);
  bssl::UniquePtr<CRYPTO_BUFFER> leaf = GetChainTestCertificateBuffer();
  ASSERT_TRUE(leaf);
  bssl::UniquePtr<CRYPTO_BUFFER> intermediate =
      GetChainTestIntermediateBuffer();
  ASSERT_TRUE(intermediate);
  std::vector<CRYPTO_BUFFER *> chain = {
      leaf.get(),
      intermediate.get(),
  };
  ASSERT_TRUE(SSL_CTX_set_chain_and_key(server_ctx.get(), &chain[0],
                                        chain.size(), key.get(), nullptr));

  bssl::UniquePtr<CRYPTO_BUFFER> ca_name(
      CRYPTO_BUFFER_new(kTestName, sizeof(kTestName), nullptr));
  ASSERT_TRUE(ca_name);
  bssl::UniquePtr<STACK_OF(CRYPTO_BUFFER)> ca_names(
      sk_CRYPTO_BUFFER_new_null());
  ASSERT_TRUE(ca_names);
  ASSERT_TRUE(PushToStack(ca_names.get(), std::move(ca_name)));
  SSL_CTX_set0_client_CAs(server_ctx.get(), ca_names.release());

  // Configure client and server to accept all certificates.
  SSL_CTX_set_custom_verify(
      client_ctx.get(), SSL_VERIFY_PEER,
      [](SSL *ssl, uint8_t *out_alert) -> ssl_verify_result_t {
        return ssl_verify_ok;
      });
  SSL_CTX_set_custom_verify(
      server_ctx.get(), SSL_VERIFY_PEER,
      [](SSL *ssl, uint8_t *out_alert) -> ssl_verify_result_t {
        return ssl_verify_ok;
      });

  bool cert_cb_called = false;
  SSL_CTX_set_cert_cb(
      client_ctx.get(),
      [](SSL *ssl, void *arg) -> int {
        const STACK_OF(CRYPTO_BUFFER) *peer_names =
            SSL_get0_server_requested_CAs(ssl);
        EXPECT_EQ(1u, sk_CRYPTO_BUFFER_num(peer_names));
        CRYPTO_BUFFER *peer_name = sk_CRYPTO_BUFFER_value(peer_names, 0);
        EXPECT_EQ(Bytes(kTestName), Bytes(CRYPTO_BUFFER_data(peer_name),
                                          CRYPTO_BUFFER_len(peer_name)));
        *reinterpret_cast<bool *>(arg) = true;
        return 1;
      },
      &cert_cb_called);

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));
  EXPECT_TRUE(cert_cb_called);
}

// Configuring the empty cipher list, though an error, should still modify the
// configuration.
TEST(SSLTest, EmptyCipherList) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);

  // Initially, the cipher list is not empty.
  EXPECT_NE(0u, sk_SSL_CIPHER_num(SSL_CTX_get_ciphers(ctx.get())));

  // Configuring the empty cipher list with |SSL_CTX_set_cipher_list|
  // succeeds.
  EXPECT_TRUE(SSL_CTX_set_cipher_list(ctx.get(), ""));
  // The cipher list should only be populated with default TLS 1.3 ciphersuites
  EXPECT_EQ(3u, sk_SSL_CIPHER_num(SSL_CTX_get_ciphers(ctx.get())));

  // Configuring the empty cipher list with |SSL_CTX_set_ciphersuites| works
  EXPECT_TRUE(SSL_CTX_set_ciphersuites(ctx.get(), ""));
  EXPECT_EQ(0u, sk_SSL_CIPHER_num(ctx->tls13_cipher_list->ciphers.get()));
  EXPECT_EQ(0u, sk_SSL_CIPHER_num(SSL_CTX_get_ciphers(ctx.get())));

  // Configuring the empty cipher list with |SSL_CTX_set_strict_cipher_list|
  // fails.
  EXPECT_FALSE(SSL_CTX_set_strict_cipher_list(ctx.get(), ""));
  ERR_clear_error();

  // But the cipher list is still updated to empty.
  EXPECT_EQ(0u, sk_SSL_CIPHER_num(SSL_CTX_get_ciphers(ctx.get())));
}

struct TLSVersionTestParams {
  uint16_t version;
};

const TLSVersionTestParams kTLSVersionTests[] = {
    {TLS1_VERSION},
    {TLS1_1_VERSION},
    {TLS1_2_VERSION},
    {TLS1_3_VERSION},
};

struct CertificateKeyTestParams {
  bssl::UniquePtr<X509> (*certificate)();
  bssl::UniquePtr<EVP_PKEY> (*key)();
  int slot_index;
  const char suite[50];
  uint16_t corresponding_sigalg;
};

const CertificateKeyTestParams kCertificateKeyTests[] = {
    {GetTestCertificate, GetTestKey, SSL_PKEY_RSA,
     "TLS_RSA_WITH_AES_256_CBC_SHA:", SSL_SIGN_RSA_PSS_RSAE_SHA256},
    {GetECDSATestCertificate, GetECDSATestKey, SSL_PKEY_ECC,
     "TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA:",
     SSL_SIGN_ECDSA_SECP256R1_SHA256},
    {GetED25519TestCertificate, GetED25519TestKey, SSL_PKEY_ED25519,
     "TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256:", SSL_SIGN_ED25519},
};

class MultipleCertificateSlotTest
    : public testing::TestWithParam<
          std::tuple<TLSVersionTestParams, CertificateKeyTestParams>> {
 public:
  MultipleCertificateSlotTest() {
    this->version = version_param().version;
    this->slot_index = certificate_key_param().slot_index;
  }

  uint16_t version = 0;
  int slot_index = -1;

  static TLSVersionTestParams version_param() {
    return std::get<0>(GetParam());
  }
  static CertificateKeyTestParams certificate_key_param() {
    return std::get<1>(GetParam());
  }

  const void StandardCertificateSlotIndexTests(SSL_CTX *client_ctx,
                                               SSL_CTX *server_ctx,
                                               std::vector<uint16_t> sigalgs,
                                               int last_cert_type_set,
                                               int should_connect) {
    EXPECT_TRUE(SSL_CTX_set_signing_algorithm_prefs(client_ctx, sigalgs.data(),
                                                    sigalgs.size()));
    EXPECT_TRUE(SSL_CTX_set_verify_algorithm_prefs(client_ctx, sigalgs.data(),
                                                   sigalgs.size()));

    ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx, version));
    ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx, version));
    ASSERT_TRUE(SSL_CTX_set_min_proto_version(server_ctx, version));
    ASSERT_TRUE(SSL_CTX_set_max_proto_version(server_ctx, version));

    ClientConfig config;
    bssl::UniquePtr<SSL> client, server;

    EXPECT_EQ(ConnectClientAndServer(&client, &server, client_ctx, server_ctx,
                                     config, false),
              should_connect);
    if (!should_connect) {
      return;
    }

    ASSERT_TRUE(CompleteHandshakes(client.get(), server.get()));

    // Check the internal slot index to verify that the correct slot was set.
    // This should be the slot of the last certificate that was set in
    // |server_ctx|.
    EXPECT_EQ(server_ctx->cert->cert_private_key_idx, last_cert_type_set);
    EXPECT_EQ(server->ctx->cert->cert_private_key_idx, last_cert_type_set);

    // Check the internal slot index to verify that the correct slot was used
    // during the handshake.
    EXPECT_EQ(server->config->cert->cert_private_key_idx, slot_index);
  }
};

INSTANTIATE_TEST_SUITE_P(
    MultipleCertificateSlotAllTest, MultipleCertificateSlotTest,
    testing::Combine(testing::ValuesIn(kTLSVersionTests),
                     testing::ValuesIn(kCertificateKeyTests)));

// Sets up the |SSL_CTX| with |SSL_CTX_use_certificate| & |SSL_use_PrivateKey|.
TEST_P(MultipleCertificateSlotTest, CertificateSlotIndex) {
  if (version < TLS1_2_VERSION && slot_index == SSL_PKEY_ED25519) {
    // ED25519 is not supported in versions prior to TLS1.2.
    GTEST_SKIP();
  }
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx(CreateContextWithCertificate(
      TLS_method(), certificate_key_param().certificate(),
      certificate_key_param().key()));

  StandardCertificateSlotIndexTests(
      client_ctx.get(), server_ctx.get(),
      {SSL_SIGN_ED25519, SSL_SIGN_ECDSA_SECP256R1_SHA256,
       SSL_SIGN_RSA_PSS_RSAE_SHA256},
      slot_index, true);
}

// Sets up the |SSL_CTX| with |SSL_CTX_set_chain_and_key|.
TEST_P(MultipleCertificateSlotTest, SetChainAndKeyIndex) {
  if (version < TLS1_2_VERSION && slot_index == SSL_PKEY_ED25519) {
    // ED25519 is not supported in versions prior to TLS1.2.
    GTEST_SKIP();
  }
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_method()));

  uint8_t *buf = nullptr;
  int cert_len = i2d_X509(certificate_key_param().certificate().get(), &buf);
  bssl::UniquePtr<uint8_t> free_buf(buf);

  bssl::UniquePtr<CRYPTO_BUFFER> leaf(
      CRYPTO_BUFFER_new(buf, cert_len, nullptr));
  ASSERT_TRUE(leaf);
  std::vector<CRYPTO_BUFFER *> chain = {leaf.get()};

  ASSERT_TRUE(
      SSL_CTX_set_chain_and_key(server_ctx.get(), &chain[0], chain.size(),
                                certificate_key_param().key().get(), nullptr));

  StandardCertificateSlotIndexTests(
      client_ctx.get(), server_ctx.get(),
      {SSL_SIGN_ED25519, SSL_SIGN_ECDSA_SECP256R1_SHA256,
       SSL_SIGN_RSA_PSS_RSAE_SHA256},
      slot_index, true);
}

TEST_P(MultipleCertificateSlotTest, AutomaticSelectionSigAlgs) {
  if (version < TLS1_2_VERSION && slot_index == SSL_PKEY_ED25519) {
    // ED25519 is not supported in versions prior to TLS1.2.
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_method()));

  ASSERT_TRUE(
      SSL_CTX_use_certificate(server_ctx.get(), GetTestCertificate().get()));
  ASSERT_TRUE(SSL_CTX_use_PrivateKey(server_ctx.get(), GetTestKey().get()));
  ASSERT_TRUE(SSL_CTX_use_certificate(server_ctx.get(),
                                      GetECDSATestCertificate().get()));
  ASSERT_TRUE(
      SSL_CTX_use_PrivateKey(server_ctx.get(), GetECDSATestKey().get()));
  ASSERT_TRUE(SSL_CTX_use_certificate(server_ctx.get(),
                                      GetED25519TestCertificate().get()));
  ASSERT_TRUE(
      SSL_CTX_use_PrivateKey(server_ctx.get(), GetED25519TestKey().get()));


  // Versions prior to TLS1.3 need a valid authentication cipher suite to pair
  // with the certificate.
  if (version < TLS1_3_VERSION) {
    ASSERT_TRUE(SSL_CTX_set_cipher_list(client_ctx.get(),
                                        certificate_key_param().suite));
  }

  StandardCertificateSlotIndexTests(
      client_ctx.get(), server_ctx.get(),
      {certificate_key_param().corresponding_sigalg}, SSL_PKEY_ED25519, true);
}

TEST_P(MultipleCertificateSlotTest, AutomaticSelectionCipherAuth) {
  if ((version < TLS1_2_VERSION && slot_index == SSL_PKEY_ED25519) ||
      version >= TLS1_3_VERSION) {
    // ED25519 is not supported in versions prior to TLS1.2.
    // TLS 1.3 not have cipher-based authentication configuration.
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_method()));

  ASSERT_TRUE(
      SSL_CTX_use_certificate(server_ctx.get(), GetTestCertificate().get()));
  ASSERT_TRUE(SSL_CTX_use_PrivateKey(server_ctx.get(), GetTestKey().get()));
  ASSERT_TRUE(SSL_CTX_use_certificate(server_ctx.get(),
                                      GetECDSATestCertificate().get()));
  ASSERT_TRUE(
      SSL_CTX_use_PrivateKey(server_ctx.get(), GetECDSATestKey().get()));
  ASSERT_TRUE(SSL_CTX_use_certificate(server_ctx.get(),
                                      GetED25519TestCertificate().get()));
  ASSERT_TRUE(
      SSL_CTX_use_PrivateKey(server_ctx.get(), GetED25519TestKey().get()));


  // Versions prior to TLS1.3 need a valid authentication cipher suite to pair
  // with the certificate.
  if (version < TLS1_3_VERSION) {
    ASSERT_TRUE(SSL_CTX_set_cipher_list(client_ctx.get(),
                                        certificate_key_param().suite));
  }

  // We allow all possible sigalgs in this test, but either the ECDSA or ED25519
  // certificate could be chosen when using an |SSL_aECDSA| ciphersuite.
  std::vector<uint16_t> sigalgs = {SSL_SIGN_RSA_PSS_RSAE_SHA256};
  if (slot_index == SSL_PKEY_ED25519) {
    sigalgs.push_back(SSL_SIGN_ED25519);
  } else {
    sigalgs.push_back(SSL_SIGN_ECDSA_SECP256R1_SHA256);
  }

  StandardCertificateSlotIndexTests(client_ctx.get(), server_ctx.get(), sigalgs,
                                    SSL_PKEY_ED25519, true);
}

TEST_P(MultipleCertificateSlotTest, MissingCertificate) {
  if (version < TLS1_2_VERSION && slot_index == SSL_PKEY_ED25519) {
    // ED25519 is not supported in versions prior to TLS1.2.
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_method()));

  ASSERT_TRUE(SSL_CTX_use_PrivateKey(server_ctx.get(), GetTestKey().get()));
  ASSERT_TRUE(
      SSL_CTX_use_PrivateKey(server_ctx.get(), GetECDSATestKey().get()));
  ASSERT_TRUE(
      SSL_CTX_use_PrivateKey(server_ctx.get(), GetED25519TestKey().get()));

  // Versions prior to TLS1.3 need a valid authentication cipher suite to pair
  // with the certificate.
  if (version < TLS1_3_VERSION) {
    ASSERT_TRUE(SSL_CTX_set_cipher_list(client_ctx.get(),
                                        certificate_key_param().suite));
  }

  StandardCertificateSlotIndexTests(
      client_ctx.get(), server_ctx.get(),
      {certificate_key_param().corresponding_sigalg}, -1, false);
}

TEST_P(MultipleCertificateSlotTest, MissingPrivateKey) {
  if (version < TLS1_2_VERSION && slot_index == SSL_PKEY_ED25519) {
    // ED25519 is not supported in versions prior to TLS1.2.
    GTEST_SKIP();
  }

  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_method()));

  ASSERT_TRUE(
      SSL_CTX_use_certificate(server_ctx.get(), GetTestCertificate().get()));
  ASSERT_TRUE(SSL_CTX_use_certificate(server_ctx.get(),
                                      GetECDSATestCertificate().get()));
  ASSERT_TRUE(SSL_CTX_use_certificate(server_ctx.get(),
                                      GetED25519TestCertificate().get()));

  // Versions prior to TLS1.3 need a valid authentication cipher suite to pair
  // with the certificate.
  if (version < TLS1_3_VERSION) {
    ASSERT_TRUE(SSL_CTX_set_cipher_list(client_ctx.get(),
                                        certificate_key_param().suite));
  }

  StandardCertificateSlotIndexTests(
      client_ctx.get(), server_ctx.get(),
      {certificate_key_param().corresponding_sigalg}, -1, false);
}


struct MultiTransferReadWriteTestParams {
  const char suite[50];
  bool tls13;
  bssl::UniquePtr<X509> (*certificate)();
  bssl::UniquePtr<EVP_PKEY> (*key)();
};

static const MultiTransferReadWriteTestParams kMultiTransferReadWriteTests[] = {
    {"TLS_AES_128_GCM_SHA256:", true, GetECDSATestCertificate, GetECDSATestKey},
    {"TLS_AES_256_GCM_SHA384:", true, GetECDSATestCertificate, GetECDSATestKey},
    {"TLS_CHACHA20_POLY1305_SHA256:", true, GetECDSATestCertificate,
     GetECDSATestKey},
    {"TLS_RSA_WITH_NULL_SHA:", false, GetTestCertificate, GetTestKey},
    {"TLS_RSA_WITH_3DES_EDE_CBC_SHA:", false, GetTestCertificate, GetTestKey},
    {"TLS_RSA_WITH_AES_128_CBC_SHA:", false, GetTestCertificate, GetTestKey},
    {"TLS_RSA_WITH_AES_256_CBC_SHA:", false, GetTestCertificate, GetTestKey},
    {"TLS_RSA_WITH_AES_128_CBC_SHA256:", false, GetTestCertificate, GetTestKey},
    {"TLS_RSA_WITH_AES_128_GCM_SHA256:", false, GetTestCertificate, GetTestKey},
    {"TLS_RSA_WITH_AES_256_GCM_SHA384:", false, GetTestCertificate, GetTestKey},
    {"TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA:", false, GetECDSATestCertificate,
     GetECDSATestKey},
    {"TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA:", false, GetECDSATestCertificate,
     GetECDSATestKey},
    {"TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA:", false, GetTestCertificate,
     GetTestKey},
    {"TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA:", false, GetTestCertificate,
     GetTestKey},
    {"TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256:", false, GetTestCertificate,
     GetTestKey},
    {"TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256:", false, GetECDSATestCertificate,
     GetECDSATestKey},
    {"TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384:", false, GetECDSATestCertificate,
     GetECDSATestKey},
    {"TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256:", false, GetTestCertificate,
     GetTestKey},
    {"TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384:", false, GetTestCertificate,
     GetTestKey},
    {"TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256:", false, GetTestCertificate,
     GetTestKey},
    {"TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256:", false,
     GetECDSATestCertificate, GetECDSATestKey}};

class MultiTransferReadWriteTest
    : public testing::TestWithParam<MultiTransferReadWriteTestParams> {};

INSTANTIATE_TEST_SUITE_P(SuiteTests, MultiTransferReadWriteTest,
                         testing::ValuesIn(kMultiTransferReadWriteTests));

TEST_P(MultiTransferReadWriteTest, SuiteTransfers) {
  auto params = GetParam();

  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx(CreateContextWithCertificate(
      TLS_method(), params.certificate(), params.key()));

  uint16_t version = TLS1_2_VERSION;
  int (*set_cipher_suites)(SSL_CTX *, const char *) = SSL_CTX_set_cipher_list;
  if (params.tls13) {
    version = TLS1_3_VERSION;
    set_cipher_suites = SSL_CTX_set_ciphersuites;
  }

  ASSERT_TRUE(set_cipher_suites(client_ctx.get(), params.suite));
  ASSERT_TRUE(set_cipher_suites(server_ctx.get(), params.suite));

  ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), version));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), version));
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(server_ctx.get(), version));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(server_ctx.get(), version));

  ClientConfig config;
  bssl::UniquePtr<SSL> client, server;

  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get(), config, true));

  ASSERT_TRUE(CompleteHandshakes(client.get(), server.get()));

  bssl::UniquePtr<SSL> transfer_server;
  TransferSSL(&server, server_ctx.get(), &transfer_server);
  server = std::move(transfer_server);

  char buf[3];
  size_t buf_cap = sizeof(buf);

  for (size_t t = 0; t < 5; t++) {
    for (size_t i = 0; i < 20; i++) {
      std::string send_str = std::to_string(i);

      // Assert server open
      ASSERT_TRUE(SSL_write(client.get(), send_str.c_str(), send_str.length()));
      int read = SSL_read(server.get(), buf, buf_cap);
      ASSERT_TRUE(read);
      ASSERT_TRUE((size_t)read == send_str.length());
      std::string read_str(buf, read);
      ASSERT_EQ(send_str, read_str);

      // Assert server seal
      ASSERT_TRUE(SSL_write(server.get(), send_str.c_str(), send_str.length()));
      read = SSL_read(client.get(), buf, buf_cap);
      ASSERT_TRUE(read);
      ASSERT_TRUE((size_t)read == send_str.length());
      read_str = std::string(buf, read);
      ASSERT_EQ(send_str, read_str);
    }
    TransferSSL(&server, server_ctx.get(), &transfer_server);
    server = std::move(transfer_server);
  }
}

// ssl_test_ticket_aead_failure_mode enumerates the possible ways in which the
// test |SSL_TICKET_AEAD_METHOD| can fail.
enum ssl_test_ticket_aead_failure_mode {
  ssl_test_ticket_aead_ok = 0,
  ssl_test_ticket_aead_seal_fail,
  ssl_test_ticket_aead_open_soft_fail,
  ssl_test_ticket_aead_open_hard_fail,
};

struct ssl_test_ticket_aead_state {
  unsigned retry_count = 0;
  ssl_test_ticket_aead_failure_mode failure_mode = ssl_test_ticket_aead_ok;
};

static int ssl_test_ticket_aead_ex_index_dup(CRYPTO_EX_DATA *to,
                                             const CRYPTO_EX_DATA *from,
                                             void **from_d, int index,
                                             long argl, void *argp) {
  abort();
}

static void ssl_test_ticket_aead_ex_index_free(void *parent, void *ptr,
                                               CRYPTO_EX_DATA *ad, int index,
                                               long argl, void *argp) {
  delete reinterpret_cast<ssl_test_ticket_aead_state*>(ptr);
}

static CRYPTO_once_t g_ssl_test_ticket_aead_ex_index_once = CRYPTO_ONCE_INIT;
static int g_ssl_test_ticket_aead_ex_index;

static int ssl_test_ticket_aead_get_ex_index() {
  CRYPTO_once(&g_ssl_test_ticket_aead_ex_index_once, [] {
    g_ssl_test_ticket_aead_ex_index = SSL_get_ex_new_index(
        0, nullptr, nullptr, ssl_test_ticket_aead_ex_index_dup,
        ssl_test_ticket_aead_ex_index_free);
  });
  return g_ssl_test_ticket_aead_ex_index;
}

static size_t ssl_test_ticket_aead_max_overhead(SSL *ssl) { return 1; }

static int ssl_test_ticket_aead_seal(SSL *ssl, uint8_t *out, size_t *out_len,
                                     size_t max_out_len, const uint8_t *in,
                                     size_t in_len) {
  auto state = reinterpret_cast<ssl_test_ticket_aead_state *>(
      SSL_get_ex_data(ssl, ssl_test_ticket_aead_get_ex_index()));

  if (state->failure_mode == ssl_test_ticket_aead_seal_fail ||
      max_out_len < in_len + 1) {
    return 0;
  }

  OPENSSL_memmove(out, in, in_len);
  out[in_len] = 0xff;
  *out_len = in_len + 1;

  return 1;
}

static ssl_ticket_aead_result_t ssl_test_ticket_aead_open(
    SSL *ssl, uint8_t *out, size_t *out_len, size_t max_out_len,
    const uint8_t *in, size_t in_len) {
  auto state = reinterpret_cast<ssl_test_ticket_aead_state *>(
      SSL_get_ex_data(ssl, ssl_test_ticket_aead_get_ex_index()));

  if (state->retry_count > 0) {
    state->retry_count--;
    return ssl_ticket_aead_retry;
  }

  switch (state->failure_mode) {
    case ssl_test_ticket_aead_ok:
      break;
    case ssl_test_ticket_aead_seal_fail:
      // If |seal| failed then there shouldn't be any ticket to try and
      // decrypt.
      abort();
      break;
    case ssl_test_ticket_aead_open_soft_fail:
      return ssl_ticket_aead_ignore_ticket;
    case ssl_test_ticket_aead_open_hard_fail:
      return ssl_ticket_aead_error;
  }

  if (in_len == 0 || in[in_len - 1] != 0xff) {
    return ssl_ticket_aead_ignore_ticket;
  }

  if (max_out_len < in_len - 1) {
    return ssl_ticket_aead_error;
  }

  OPENSSL_memmove(out, in, in_len - 1);
  *out_len = in_len - 1;
  return ssl_ticket_aead_success;
}

static const SSL_TICKET_AEAD_METHOD kSSLTestTicketMethod = {
    ssl_test_ticket_aead_max_overhead,
    ssl_test_ticket_aead_seal,
    ssl_test_ticket_aead_open,
};

static void ConnectClientAndServerWithTicketMethod(
    bssl::UniquePtr<SSL> *out_client, bssl::UniquePtr<SSL> *out_server,
    SSL_CTX *client_ctx, SSL_CTX *server_ctx, unsigned retry_count,
    ssl_test_ticket_aead_failure_mode failure_mode, SSL_SESSION *session) {
  bssl::UniquePtr<SSL> client(SSL_new(client_ctx)), server(SSL_new(server_ctx));
  ASSERT_TRUE(client);
  ASSERT_TRUE(server);
  SSL_set_connect_state(client.get());
  SSL_set_accept_state(server.get());

  auto state = new ssl_test_ticket_aead_state;
  state->retry_count = retry_count;
  state->failure_mode = failure_mode;

  ASSERT_GE(ssl_test_ticket_aead_get_ex_index(), 0);
  ASSERT_TRUE(SSL_set_ex_data(server.get(), ssl_test_ticket_aead_get_ex_index(),
                              state));

  SSL_set_session(client.get(), session);

  BIO *bio1, *bio2;
  ASSERT_TRUE(BIO_new_bio_pair(&bio1, 0, &bio2, 0));

  // SSL_set_bio takes ownership.
  SSL_set_bio(client.get(), bio1, bio1);
  SSL_set_bio(server.get(), bio2, bio2);

  if (CompleteHandshakes(client.get(), server.get())) {
    *out_client = std::move(client);
    *out_server = std::move(server);
  } else {
    out_client->reset();
    out_server->reset();
  }
}

using TicketAEADMethodParam =
    testing::tuple<uint16_t, unsigned, ssl_test_ticket_aead_failure_mode, bool>;

class TicketAEADMethodTest
    : public ::testing::TestWithParam<TicketAEADMethodParam> {};

TEST_P(TicketAEADMethodTest, Resume) {
  bssl::UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(server_ctx);
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(client_ctx);

  const uint16_t version = testing::get<0>(GetParam());
  const unsigned retry_count = testing::get<1>(GetParam());
  const ssl_test_ticket_aead_failure_mode failure_mode =
      testing::get<2>(GetParam());
  const bool transfer_ssl = testing::get<3>(GetParam());

  ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), version));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), version));
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(server_ctx.get(), version));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(server_ctx.get(), version));

  SSL_CTX_set_session_cache_mode(client_ctx.get(), SSL_SESS_CACHE_BOTH);
  SSL_CTX_set_session_cache_mode(server_ctx.get(), SSL_SESS_CACHE_BOTH);
  SSL_CTX_set_current_time_cb(client_ctx.get(), FrozenTimeCallback);
  SSL_CTX_set_current_time_cb(server_ctx.get(), FrozenTimeCallback);
  SSL_CTX_sess_set_new_cb(client_ctx.get(), SaveLastSession);

  SSL_CTX_set_ticket_aead_method(server_ctx.get(), &kSSLTestTicketMethod);

  bssl::UniquePtr<SSL> client, server;
  ASSERT_NO_FATAL_FAILURE(ConnectClientAndServerWithTicketMethod(
      &client, &server, client_ctx.get(), server_ctx.get(), retry_count,
      failure_mode, nullptr));
  // Only transfer when the code is to test SSL transfer and the connection is
  // finished successuflly.
  if (transfer_ssl && server) {
    // |server| is reset to hold the transferred SSL.
    TransferSSL(&server, server_ctx.get(), nullptr);
  }
  switch (failure_mode) {
    case ssl_test_ticket_aead_ok:
    case ssl_test_ticket_aead_open_hard_fail:
    case ssl_test_ticket_aead_open_soft_fail:
      ASSERT_TRUE(client);
      break;
    case ssl_test_ticket_aead_seal_fail:
      EXPECT_FALSE(client);
      return;
  }
  EXPECT_FALSE(SSL_session_reused(client.get()));
  EXPECT_FALSE(SSL_session_reused(server.get()));

  ASSERT_TRUE(FlushNewSessionTickets(client.get(), server.get()));
  bssl::UniquePtr<SSL_SESSION> session = std::move(g_last_session);
  ASSERT_NO_FATAL_FAILURE(ConnectClientAndServerWithTicketMethod(
      &client, &server, client_ctx.get(), server_ctx.get(), retry_count,
      failure_mode, session.get()));
  // Do SSL transfer again.
  // Only transfer when the code is to test SSL transfer and the connection is
  // finished successuflly.
  if (transfer_ssl && server) {
    // |server| is reset to hold the transferred SSL.
    TransferSSL(&server, server_ctx.get(), nullptr);
  }
  switch (failure_mode) {
    case ssl_test_ticket_aead_ok:
      ASSERT_TRUE(client);
      EXPECT_TRUE(SSL_session_reused(client.get()));
      EXPECT_TRUE(SSL_session_reused(server.get()));
      break;
    case ssl_test_ticket_aead_seal_fail:
      abort();
      break;
    case ssl_test_ticket_aead_open_hard_fail:
      EXPECT_FALSE(client);
      break;
    case ssl_test_ticket_aead_open_soft_fail:
      ASSERT_TRUE(client);
      EXPECT_FALSE(SSL_session_reused(client.get()));
      EXPECT_FALSE(SSL_session_reused(server.get()));
  }
}

std::string TicketAEADMethodParamToString(
    const testing::TestParamInfo<TicketAEADMethodParam> &params) {
  std::string ret = GetVersionName(std::get<0>(params.param));
  // GTest only allows alphanumeric characters and '_' in the parameter
  // string. Additionally filter out the 'v' to get "TLS13" over "TLSv13".
  for (auto it = ret.begin(); it != ret.end();) {
    if (*it == '.' || *it == 'v') {
      it = ret.erase(it);
    } else {
      ++it;
    }
  }
  char retry_count[256];
  snprintf(retry_count, sizeof(retry_count), "%u", std::get<1>(params.param));
  ret += "_";
  ret += retry_count;
  ret += "Retries_";
  switch (std::get<2>(params.param)) {
    case ssl_test_ticket_aead_ok:
      ret += "OK";
      break;
    case ssl_test_ticket_aead_seal_fail:
      ret += "SealFail";
      break;
    case ssl_test_ticket_aead_open_soft_fail:
      ret += "OpenSoftFail";
      break;
    case ssl_test_ticket_aead_open_hard_fail:
      ret += "OpenHardFail";
      break;
  }
  if (std::get<3>(params.param)) {
    ret += "_SSLTransfer";
  }
  return ret;
}

INSTANTIATE_TEST_SUITE_P(
    TicketAEADMethodTests, TicketAEADMethodTest,
    testing::Combine(testing::Values(TLS1_2_VERSION, TLS1_3_VERSION),
                     testing::Values(0, 1, 2),
                     testing::Values(ssl_test_ticket_aead_ok,
                                     ssl_test_ticket_aead_seal_fail,
                                     ssl_test_ticket_aead_open_soft_fail,
                                     ssl_test_ticket_aead_open_hard_fail),
                     testing::Values(TRANSFER_SSL, !TRANSFER_SSL)),
    TicketAEADMethodParamToString);

TEST(SSLTest, SelectNextProto) {
  uint8_t *result;
  uint8_t result_len;

  // If there is an overlap, it should be returned.
  EXPECT_EQ(OPENSSL_NPN_NEGOTIATED,
            SSL_select_next_proto(&result, &result_len,
                                  (const uint8_t *)"\1a\2bb\3ccc", 9,
                                  (const uint8_t *)"\1x\1y\1a\1z", 8));
  EXPECT_EQ(Bytes("a"), Bytes(result, result_len));

  EXPECT_EQ(OPENSSL_NPN_NEGOTIATED,
            SSL_select_next_proto(&result, &result_len,
                                  (const uint8_t *)"\1a\2bb\3ccc", 9,
                                  (const uint8_t *)"\1x\1y\2bb\1z", 9));
  EXPECT_EQ(Bytes("bb"), Bytes(result, result_len));

  EXPECT_EQ(OPENSSL_NPN_NEGOTIATED,
            SSL_select_next_proto(&result, &result_len,
                                  (const uint8_t *)"\1a\2bb\3ccc", 9,
                                  (const uint8_t *)"\1x\1y\3ccc\1z", 10));
  EXPECT_EQ(Bytes("ccc"), Bytes(result, result_len));

  // Peer preference order takes precedence over local.
  EXPECT_EQ(OPENSSL_NPN_NEGOTIATED,
            SSL_select_next_proto(&result, &result_len,
                                  (const uint8_t *)"\1a\2bb\3ccc", 9,
                                  (const uint8_t *)"\3ccc\2bb\1a", 9));
  EXPECT_EQ(Bytes("a"), Bytes(result, result_len));

  // If there is no overlap, opportunistically select the first local protocol.
  // ALPN callers should ignore this, but NPN callers may use this per
  // draft-agl-tls-nextprotoneg-03, section 6.
  EXPECT_EQ(OPENSSL_NPN_NO_OVERLAP,
            SSL_select_next_proto(&result, &result_len,
                                  (const uint8_t *)"\1a\2bb\3ccc", 9,
                                  (const uint8_t *)"\1x\2yy\3zzz", 9));
  EXPECT_EQ(Bytes("x"), Bytes(result, result_len));

  // The peer preference order may be empty in NPN. This should be treated as no
  // overlap and continue to select an opportunistic protocol.
  EXPECT_EQ(OPENSSL_NPN_NO_OVERLAP,
            SSL_select_next_proto(&result, &result_len, nullptr, 0,
                                  (const uint8_t *)"\1x\2yy\3zzz", 9));
  EXPECT_EQ(Bytes("x"), Bytes(result, result_len));

  // Although calling this function with no local protocols is a caller error,
  // it should cleanly return an empty protocol.
  EXPECT_EQ(
      OPENSSL_NPN_NO_OVERLAP,
      SSL_select_next_proto(&result, &result_len,
                            (const uint8_t *)"\1a\2bb\3ccc", 9, nullptr, 0));
  EXPECT_EQ(Bytes(""), Bytes(result, result_len));

  // Syntax errors are similarly caller errors.
  EXPECT_EQ(
      OPENSSL_NPN_NO_OVERLAP,
      SSL_select_next_proto(&result, &result_len, (const uint8_t *)"\4aaa", 4,
                            (const uint8_t *)"\1a\2bb\3ccc", 9));
  EXPECT_EQ(Bytes(""), Bytes(result, result_len));
  EXPECT_EQ(OPENSSL_NPN_NO_OVERLAP,
            SSL_select_next_proto(&result, &result_len,
                                  (const uint8_t *)"\1a\2bb\3ccc", 9,
                                  (const uint8_t *)"\4aaa", 4));
  EXPECT_EQ(Bytes(""), Bytes(result, result_len));

  // Protocols in protocol lists may not be empty.
  EXPECT_EQ(OPENSSL_NPN_NO_OVERLAP,
            SSL_select_next_proto(&result, &result_len,
                                  (const uint8_t *)"\0\2bb\3ccc", 8,
                                  (const uint8_t *)"\1a\2bb\3ccc", 9));
  EXPECT_EQ(OPENSSL_NPN_NO_OVERLAP,
            SSL_select_next_proto(&result, &result_len,
                                  (const uint8_t *)"\1a\2bb\3ccc", 9,
                                  (const uint8_t *)"\0\2bb\3ccc", 8));
  EXPECT_EQ(Bytes(""), Bytes(result, result_len));
}

// The client should gracefully handle no suitable ciphers being enabled.
TEST(SSLTest, NoCiphersAvailable) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);

  // Configure |client_ctx| with a cipher list that does not intersect with its
  // version configuration.
  ASSERT_TRUE(SSL_CTX_set_strict_cipher_list(
      ctx.get(), "TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256"));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(ctx.get(), TLS1_1_VERSION));

  bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);
  SSL_set_connect_state(ssl.get());

  UniquePtr<BIO> rbio(BIO_new(BIO_s_mem())), wbio(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(rbio);
  ASSERT_TRUE(wbio);
  SSL_set0_rbio(ssl.get(), rbio.release());
  SSL_set0_wbio(ssl.get(), wbio.release());

  int ret = SSL_do_handshake(ssl.get());
  EXPECT_EQ(-1, ret);
  EXPECT_EQ(SSL_ERROR_SSL, SSL_get_error(ssl.get(), ret));
  EXPECT_TRUE(
      ErrorEquals(ERR_get_error(), ERR_LIB_SSL, SSL_R_NO_CIPHERS_AVAILABLE));
}

// Test that post-handshake tickets consumed by |SSL_shutdown| are ignored.
TEST(SSLTest, ShutdownIgnoresTickets) {
  bssl::UniquePtr<SSL_CTX> ctx(CreateContextWithTestCertificate(TLS_method()));
  ASSERT_TRUE(ctx);
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(ctx.get(), TLS1_3_VERSION));

  SSL_CTX_set_session_cache_mode(ctx.get(), SSL_SESS_CACHE_BOTH);

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, ctx.get(), ctx.get()));

  SSL_CTX_sess_set_new_cb(ctx.get(), [](SSL *ssl, SSL_SESSION *session) -> int {
    ADD_FAILURE() << "New session callback called during SSL_shutdown";
    return 0;
  });

  // Send close_notify.
  EXPECT_EQ(0, SSL_shutdown(server.get()));
  EXPECT_EQ(0, SSL_shutdown(client.get()));

  // Receive close_notify.
  EXPECT_EQ(1, SSL_shutdown(server.get()));
  EXPECT_EQ(1, SSL_shutdown(client.get()));
}

TEST(SSLTest, SignatureAlgorithmProperties) {
  EXPECT_EQ(EVP_PKEY_NONE, SSL_get_signature_algorithm_key_type(0x1234));
  EXPECT_EQ(nullptr, SSL_get_signature_algorithm_digest(0x1234));
  EXPECT_FALSE(SSL_is_signature_algorithm_rsa_pss(0x1234));

  EXPECT_EQ(EVP_PKEY_RSA,
            SSL_get_signature_algorithm_key_type(SSL_SIGN_RSA_PKCS1_MD5_SHA1));
  EXPECT_EQ(EVP_md5_sha1(),
            SSL_get_signature_algorithm_digest(SSL_SIGN_RSA_PKCS1_MD5_SHA1));
  EXPECT_FALSE(SSL_is_signature_algorithm_rsa_pss(SSL_SIGN_RSA_PKCS1_MD5_SHA1));

  EXPECT_EQ(EVP_PKEY_EC, SSL_get_signature_algorithm_key_type(
                             SSL_SIGN_ECDSA_SECP256R1_SHA256));
  EXPECT_EQ(EVP_sha256(), SSL_get_signature_algorithm_digest(
                              SSL_SIGN_ECDSA_SECP256R1_SHA256));
  EXPECT_FALSE(
      SSL_is_signature_algorithm_rsa_pss(SSL_SIGN_ECDSA_SECP256R1_SHA256));

  EXPECT_EQ(EVP_PKEY_RSA,
            SSL_get_signature_algorithm_key_type(SSL_SIGN_RSA_PSS_RSAE_SHA384));
  EXPECT_EQ(EVP_sha384(),
            SSL_get_signature_algorithm_digest(SSL_SIGN_RSA_PSS_RSAE_SHA384));
  EXPECT_TRUE(SSL_is_signature_algorithm_rsa_pss(SSL_SIGN_RSA_PSS_RSAE_SHA384));
}



TEST(SSLTest, HandoffDeclined) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx(
      CreateContextWithTestCertificate(TLS_method()));
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  SSL_CTX_set_handoff_mode(server_ctx.get(), true);
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_2_VERSION));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(CreateClientAndServer(&client, &server, client_ctx.get(),
                                    server_ctx.get()));

  int client_ret = SSL_do_handshake(client.get());
  int client_err = SSL_get_error(client.get(), client_ret);
  ASSERT_EQ(client_err, SSL_ERROR_WANT_READ);

  int server_ret = SSL_do_handshake(server.get());
  int server_err = SSL_get_error(server.get(), server_ret);
  ASSERT_EQ(server_err, SSL_ERROR_HANDOFF);

  ScopedCBB cbb;
  SSL_CLIENT_HELLO hello;
  ASSERT_TRUE(CBB_init(cbb.get(), 256));
  ASSERT_TRUE(SSL_serialize_handoff(server.get(), cbb.get(), &hello));

  ASSERT_TRUE(SSL_decline_handoff(server.get()));

  ASSERT_TRUE(CompleteHandshakes(client.get(), server.get()));

  uint8_t byte = 42;
  EXPECT_EQ(SSL_write(client.get(), &byte, 1), 1);
  EXPECT_EQ(SSL_read(server.get(), &byte, 1), 1);
  EXPECT_EQ(42, byte);

  byte = 43;
  EXPECT_EQ(SSL_write(server.get(), &byte, 1), 1);
  EXPECT_EQ(SSL_read(client.get(), &byte, 1), 1);
  EXPECT_EQ(43, byte);
}

static std::string SigAlgsToString(Span<const uint16_t> sigalgs) {
  std::string ret = "{";

  for (uint16_t v : sigalgs) {
    if (ret.size() > 1) {
      ret += ", ";
    }

    char buf[8];
    snprintf(buf, sizeof(buf) - 1, "0x%02x", v);
    buf[sizeof(buf) - 1] = 0;
    ret += std::string(buf);
  }

  ret += "}";
  return ret;
}

void ExpectSigAlgsEqual(Span<const uint16_t> expected,
                        Span<const uint16_t> actual) {
  bool matches = false;
  if (expected.size() == actual.size()) {
    matches = true;

    for (size_t i = 0; i < expected.size(); i++) {
      if (expected[i] != actual[i]) {
        matches = false;
        break;
      }
    }
  }

  if (!matches) {
    ADD_FAILURE() << "expected: " << SigAlgsToString(expected)
                  << " got: " << SigAlgsToString(actual);
  }
}

TEST(SSLTest, SigAlgs) {
  static const struct {
    std::vector<int> input;
    bool ok;
    std::vector<uint16_t> expected;
  } kTests[] = {
      {{}, true, {}},
      {{1}, false, {}},
      {{1, 2, 3}, false, {}},
      {{NID_sha256, EVP_PKEY_ED25519}, false, {}},
      {{NID_sha256, EVP_PKEY_RSA, NID_sha256, EVP_PKEY_RSA}, false, {}},

      {{NID_sha256, EVP_PKEY_RSA}, true, {SSL_SIGN_RSA_PKCS1_SHA256}},
      {{NID_sha512, EVP_PKEY_RSA}, true, {SSL_SIGN_RSA_PKCS1_SHA512}},
      {{NID_sha256, EVP_PKEY_RSA_PSS}, true, {SSL_SIGN_RSA_PSS_RSAE_SHA256}},
      {{NID_undef, EVP_PKEY_ED25519}, true, {SSL_SIGN_ED25519}},
      {{NID_undef, EVP_PKEY_ED25519, NID_sha384, EVP_PKEY_EC},
       true,
       {SSL_SIGN_ED25519, SSL_SIGN_ECDSA_SECP384R1_SHA384}},
  };

  UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);

  unsigned n = 1;
  for (const auto &test : kTests) {
    SCOPED_TRACE(n++);

    const bool ok =
        SSL_CTX_set1_sigalgs(ctx.get(), test.input.data(), test.input.size());
    EXPECT_EQ(ok, test.ok);

    if (!ok) {
      ERR_clear_error();
    }

    if (!test.ok) {
      continue;
    }

    ExpectSigAlgsEqual(test.expected, ctx->cert->sigalgs);
  }
}

TEST(SSLTest, SigAlgsList) {
  static const struct {
    const char *input;
    bool ok;
    std::vector<uint16_t> expected;
  } kTests[] = {
      {"", false, {}},
      {":", false, {}},
      {"+", false, {}},
      {"RSA", false, {}},
      {"RSA+", false, {}},
      {"RSA+SHA256:", false, {}},
      {":RSA+SHA256:", false, {}},
      {":RSA+SHA256+:", false, {}},
      {"!", false, {}},
      {"\x01", false, {}},
      {"RSA+SHA256:RSA+SHA384:RSA+SHA256", false, {}},
      {"RSA-PSS+SHA256:rsa_pss_rsae_sha256", false, {}},

      {"RSA+SHA256", true, {SSL_SIGN_RSA_PKCS1_SHA256}},
      {"RSA+SHA256:ed25519",
       true,
       {SSL_SIGN_RSA_PKCS1_SHA256, SSL_SIGN_ED25519}},
      {"ECDSA+SHA256:RSA+SHA512",
       true,
       {SSL_SIGN_ECDSA_SECP256R1_SHA256, SSL_SIGN_RSA_PKCS1_SHA512}},
      {"ecdsa_secp256r1_sha256:rsa_pss_rsae_sha256",
       true,
       {SSL_SIGN_ECDSA_SECP256R1_SHA256, SSL_SIGN_RSA_PSS_RSAE_SHA256}},
      {"RSA-PSS+SHA256", true, {SSL_SIGN_RSA_PSS_RSAE_SHA256}},
      {"PSS+SHA256", true, {SSL_SIGN_RSA_PSS_RSAE_SHA256}},
  };

  UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);

  unsigned n = 1;
  for (const auto &test : kTests) {
    SCOPED_TRACE(n++);

    const bool ok = SSL_CTX_set1_sigalgs_list(ctx.get(), test.input);
    EXPECT_EQ(ok, test.ok);

    if (!ok) {
      if (test.ok) {
        ERR_print_errors_fp(stderr);
      }
      ERR_clear_error();
    }

    if (!test.ok) {
      continue;
    }

    ExpectSigAlgsEqual(test.expected, ctx->cert->sigalgs);
  }
}

TEST(SSLTest, DISABLED_ApplyHandoffRemovesUnsupportedCiphers) {
  bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(server_ctx);
  bssl::UniquePtr<SSL> server(SSL_new(server_ctx.get()));
  ASSERT_TRUE(server);

  // handoff is a handoff message that has been artificially modified to pretend
  // that only cipher 0x0A is supported.  When it is applied to |server|, all
  // ciphers but that one should be removed.
  //
  // To make a new one of these, try sticking this in the |Handoff| test above:
  //
  // hexdump(stderr, "", handoff.data(), handoff.size());
  // sed -e 's/\(..\)/0x\1, /g'
  //
  // and modify serialize_features() to emit only cipher 0x0A.

  uint8_t handoff[] = {
      0x30, 0x81, 0x9a, 0x02, 0x01, 0x00, 0x04, 0x00, 0x04, 0x81, 0x82, 0x01,
      0x00, 0x00, 0x7e, 0x03, 0x03, 0x30, 0x8e, 0x8f, 0x79, 0xd2, 0x87, 0x39,
      0xc2, 0x23, 0x23, 0x13, 0xca, 0x3c, 0x80, 0x44, 0xfd, 0x80, 0x83, 0x62,
      0x3c, 0xcc, 0xf8, 0x76, 0xd3, 0x62, 0xbb, 0x54, 0xe3, 0xc4, 0x39, 0x24,
      0xa5, 0x00, 0x00, 0x1e, 0xc0, 0x2b, 0xc0, 0x2f, 0xc0, 0x2c, 0xc0, 0x30,
      0xcc, 0xa9, 0xcc, 0xa8, 0xc0, 0x09, 0xc0, 0x13, 0xc0, 0x0a, 0xc0, 0x14,
      0x00, 0x9c, 0x00, 0x9d, 0x00, 0x2f, 0x00, 0x35, 0x00, 0x0a, 0x01, 0x00,
      0x00, 0x37, 0x00, 0x17, 0x00, 0x00, 0xff, 0x01, 0x00, 0x01, 0x00, 0x00,
      0x0a, 0x00, 0x08, 0x00, 0x06, 0x00, 0x1d, 0x00, 0x17, 0x00, 0x18, 0x00,
      0x0b, 0x00, 0x02, 0x01, 0x00, 0x00, 0x23, 0x00, 0x00, 0x00, 0x0d, 0x00,
      0x14, 0x00, 0x12, 0x04, 0x03, 0x08, 0x04, 0x04, 0x01, 0x05, 0x03, 0x08,
      0x05, 0x05, 0x01, 0x08, 0x06, 0x06, 0x01, 0x02, 0x01, 0x04, 0x02, 0x00,
      0x0a, 0x04, 0x0a, 0x00, 0x15, 0x00, 0x17, 0x00, 0x18, 0x00, 0x19, 0x00,
      0x1d,
  };

  EXPECT_EQ(22u, sk_SSL_CIPHER_num(SSL_get_ciphers(server.get())));
  ASSERT_TRUE(
      SSL_apply_handoff(server.get(), {handoff, OPENSSL_ARRAY_SIZE(handoff)}));
  EXPECT_EQ(1u, sk_SSL_CIPHER_num(SSL_get_ciphers(server.get())));
}

TEST(SSLTest, ApplyHandoffRemovesUnsupportedCurves) {
  bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(server_ctx);
  bssl::UniquePtr<SSL> server(SSL_new(server_ctx.get()));
  ASSERT_TRUE(server);

  // handoff is a handoff message that has been artificially modified to pretend
  // that only one ECDH group is supported.  When it is applied to |server|, all
  // groups but that one should be removed.
  //
  // See |ApplyHandoffRemovesUnsupportedCiphers| for how to make a new one of
  // these.
  uint8_t handoff[] = {
      0x30, 0x81, 0xc0, 0x02, 0x01, 0x00, 0x04, 0x00, 0x04, 0x81, 0x82, 0x01,
      0x00, 0x00, 0x7e, 0x03, 0x03, 0x98, 0x30, 0xce, 0xd9, 0xb0, 0xdf, 0x5f,
      0x82, 0x05, 0x4a, 0x43, 0x67, 0x7e, 0xdb, 0x6a, 0x4f, 0x21, 0x18, 0x4e,
      0x0d, 0x94, 0x63, 0x18, 0x8b, 0x54, 0x89, 0xdb, 0x8b, 0x1d, 0x84, 0xbc,
      0x09, 0x00, 0x00, 0x1e, 0xc0, 0x2b, 0xc0, 0x2f, 0xc0, 0x2c, 0xc0, 0x30,
      0xcc, 0xa9, 0xcc, 0xa8, 0xc0, 0x09, 0xc0, 0x13, 0xc0, 0x0a, 0xc0, 0x14,
      0x00, 0x9c, 0x00, 0x9d, 0x00, 0x2f, 0x00, 0x35, 0x00, 0x0a, 0x01, 0x00,
      0x00, 0x37, 0x00, 0x17, 0x00, 0x00, 0xff, 0x01, 0x00, 0x01, 0x00, 0x00,
      0x0a, 0x00, 0x08, 0x00, 0x06, 0x00, 0x1d, 0x00, 0x17, 0x00, 0x18, 0x00,
      0x0b, 0x00, 0x02, 0x01, 0x00, 0x00, 0x23, 0x00, 0x00, 0x00, 0x0d, 0x00,
      0x14, 0x00, 0x12, 0x04, 0x03, 0x08, 0x04, 0x04, 0x01, 0x05, 0x03, 0x08,
      0x05, 0x05, 0x01, 0x08, 0x06, 0x06, 0x01, 0x02, 0x01, 0x04, 0x30, 0x00,
      0x02, 0x00, 0x0a, 0x00, 0x2f, 0x00, 0x35, 0x00, 0x8c, 0x00, 0x8d, 0x00,
      0x9c, 0x00, 0x9d, 0x13, 0x01, 0x13, 0x02, 0x13, 0x03, 0xc0, 0x09, 0xc0,
      0x0a, 0xc0, 0x13, 0xc0, 0x14, 0xc0, 0x2b, 0xc0, 0x2c, 0xc0, 0x2f, 0xc0,
      0x30, 0xc0, 0x35, 0xc0, 0x36, 0xcc, 0xa8, 0xcc, 0xa9, 0xcc, 0xac, 0x04,
      0x02, 0x00, 0x17,
  };

  // The zero length means that the default list of groups is used.
  EXPECT_EQ(0u, server->config->supported_group_list.size());
  ASSERT_TRUE(
      SSL_apply_handoff(server.get(), {handoff, OPENSSL_ARRAY_SIZE(handoff)}));
  EXPECT_EQ(1u, server->config->supported_group_list.size());
}


TEST(SSLTest, ZeroSizedWriteFlushesHandshakeMessages) {
  // If there are pending handshake messages, an |SSL_write| of zero bytes
  // should flush them.
  bssl::UniquePtr<SSL_CTX> server_ctx(
      CreateContextWithTestCertificate(TLS_method()));
  ASSERT_TRUE(server_ctx);
  EXPECT_TRUE(SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_3_VERSION));
  EXPECT_TRUE(SSL_CTX_set_min_proto_version(server_ctx.get(), TLS1_3_VERSION));

  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(client_ctx);
  EXPECT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_3_VERSION));
  EXPECT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), TLS1_3_VERSION));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));

  BIO *client_wbio = SSL_get_wbio(client.get());
  EXPECT_EQ(0u, BIO_wpending(client_wbio));
  EXPECT_TRUE(SSL_key_update(client.get(), SSL_KEY_UPDATE_NOT_REQUESTED));
  EXPECT_EQ(0u, BIO_wpending(client_wbio));
  EXPECT_EQ(0, SSL_write(client.get(), nullptr, 0));
  EXPECT_NE(0u, BIO_wpending(client_wbio));
}

TEST(SSLTest, SSLGetKeyUpdate) {
  bssl::UniquePtr<SSL_CTX> server_ctx(
      CreateContextWithTestCertificate(TLS_method()));
  ASSERT_TRUE(server_ctx);
  EXPECT_TRUE(SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_3_VERSION));
  EXPECT_TRUE(SSL_CTX_set_min_proto_version(server_ctx.get(), TLS1_3_VERSION));

  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(client_ctx);
  EXPECT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_3_VERSION));
  EXPECT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), TLS1_3_VERSION));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));

  // Initial state should be |SSL_KEY_UPDATE_NONE|.
  EXPECT_EQ(SSL_get_key_update_type(client.get()), SSL_KEY_UPDATE_NONE);

  // Test setting |SSL_key_update| with |SSL_KEY_UPDATE_REQUESTED|.
  EXPECT_TRUE(SSL_key_update(client.get(), SSL_KEY_UPDATE_REQUESTED));
  // |SSL_get_key_update_type| is used to determine whether a key update
  // operation has been scheduled but not yet performed.
  EXPECT_EQ(SSL_get_key_update_type(client.get()), SSL_KEY_UPDATE_REQUESTED);
  EXPECT_EQ(0, SSL_write(client.get(), nullptr, 0));
  // Key update operation should have been performed by now.
  EXPECT_EQ(SSL_get_key_update_type(client.get()), SSL_KEY_UPDATE_NONE);

  // Test setting |SSL_key_update| with |SSL_KEY_UPDATE_NOT_REQUESTED|.
  EXPECT_TRUE(SSL_key_update(client.get(), SSL_KEY_UPDATE_NOT_REQUESTED));
  EXPECT_EQ(SSL_get_key_update_type(client.get()),
            SSL_KEY_UPDATE_NOT_REQUESTED);
  EXPECT_EQ(0, SSL_write(client.get(), nullptr, 0));
  // Key update operation should have been performed by now.
  EXPECT_EQ(SSL_get_key_update_type(client.get()), SSL_KEY_UPDATE_NONE);
}
// SSL_CTX_get0_certificate needs to lock internally. Test this works.
TEST(SSLTest, GetCertificateThreads) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  bssl::UniquePtr<X509> cert = GetTestCertificate();
  ASSERT_TRUE(cert);
  ASSERT_TRUE(SSL_CTX_use_certificate(ctx.get(), cert.get()));

  // Existing code expects |SSL_CTX_get0_certificate| to be callable from two
  // threads concurrently. It originally was an immutable operation. Now we
  // implement it with a thread-safe cache, so it is worth testing.
  X509 *cert2_thread;
  std::thread thread(
      [&] { cert2_thread = SSL_CTX_get0_certificate(ctx.get()); });
  X509 *cert2 = SSL_CTX_get0_certificate(ctx.get());
  thread.join();

  ASSERT_TRUE(cert2);
  ASSERT_TRUE(cert2_thread);
  EXPECT_EQ(cert2, cert2_thread);
  EXPECT_EQ(0, X509_cmp(cert.get(), cert2));
}

#ifdef OPENSSL_THREADS

static void SetValueOnFree(void *parent, void *ptr, CRYPTO_EX_DATA *ad,
                          int index, long argl, void *argp) {
  if (ptr != nullptr) {
    *static_cast<long *>(ptr) = argl;
  }
}

// Test that one thread can register ex_data while another thread is destroying
// an object that uses it.
TEST(SSLTest, ExDataThreads) {
  static bool already_run = false;
  if (already_run) {
    GTEST_SKIP() << "This test consumes process-global resources and can only "
                    "be run once in a process. It is not compatible with "
                    "--gtest_repeat.";
  }
  already_run = true;

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);

  // Register an initial index, so the threads can exercise having any ex_data.
  int first_index =
      SSL_get_ex_new_index(-1, nullptr, nullptr, nullptr, SetValueOnFree);
  ASSERT_GE(first_index, 0);

  // Callers may register indices concurrently with using other indices. This
  // may happen if one part of an application is initializing while another part
  // is already running.
  static constexpr int kNumIndices = 3;
  static constexpr int kNumSSLs = 10;
  int index[kNumIndices];
  long values[kNumSSLs];
  std::fill(std::begin(values), std::end(values), -2);
  std::vector<std::thread> threads;
  for (size_t i = 0; i < kNumIndices; i++) {
    threads.emplace_back([&, i] {
      index[i] = SSL_get_ex_new_index(static_cast<long>(i), nullptr, nullptr,
                                      nullptr, SetValueOnFree);
      ASSERT_GE(index[i], 0);
    });
  }
  for (size_t i = 0; i < kNumSSLs; i++) {
    threads.emplace_back([&, i] {
      bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
      ASSERT_TRUE(ssl);
      ASSERT_TRUE(SSL_set_ex_data(ssl.get(), first_index, &values[i]));
    });
  }
  for (auto &thread : threads) {
    thread.join();
  }

  // Each of the SSL threads should have set their flag via ex_data.
  for (size_t i = 0; i < kNumSSLs; i++) {
    EXPECT_EQ(values[i], -1);
  }

  // Each of the newly-registered indices should be distinct and work correctly.
  static_assert(kNumIndices <= kNumSSLs, "values buffer too small");
  std::fill(std::begin(values), std::end(values), -2);
  bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);
  for (size_t i = 0; i < kNumIndices; i++) {
    for (size_t j = 0; j < i; j++) {
      EXPECT_NE(index[i], index[j]);
    }
    ASSERT_TRUE(SSL_set_ex_data(ssl.get(), index[i], &values[i]));
  }
  ssl = nullptr;
  for (size_t i = 0; i < kNumIndices; i++) {
    EXPECT_EQ(values[i], static_cast<long>(i));
  }
}
#endif  // OPENSSL_THREADS

extern "C" {
int BORINGSSL_enum_c_type_test(void);
}

TEST(SSLTest, EnumTypes) {
  EXPECT_EQ(sizeof(int), sizeof(ssl_private_key_result_t));
  EXPECT_EQ(1, BORINGSSL_enum_c_type_test());
}

static void WriteHelloRequest(SSL *server) {
  // This function assumes TLS 1.2 with ChaCha20-Poly1305.
  ASSERT_EQ(SSL_version(server), TLS1_2_VERSION);
  ASSERT_EQ(SSL_CIPHER_get_cipher_nid(SSL_get_current_cipher(server)),
            NID_chacha20_poly1305);

  // Encrypt a HelloRequest.
  uint8_t in[] = {SSL3_MT_HELLO_REQUEST, 0, 0, 0};
#if defined(BORINGSSL_UNSAFE_FUZZER_MODE)
  // Fuzzer-mode records are unencrypted.
  uint8_t record[5 + sizeof(in)];
  record[0] = SSL3_RT_HANDSHAKE;
  record[1] = 3;
  record[2] = 3;  // TLS 1.2
  record[3] = 0;
  record[4] = sizeof(record) - 5;
  memcpy(record + 5, in, sizeof(in));
#else
  // Extract key material from |server|.
  static const size_t kKeyLen = 32;
  static const size_t kNonceLen = 12;
  ASSERT_EQ(2u * (kKeyLen + kNonceLen), SSL_get_key_block_len(server));
  uint8_t key_block[2u * (kKeyLen + kNonceLen)];
  ASSERT_TRUE(SSL_generate_key_block(server, key_block, sizeof(key_block)));
  Span<uint8_t> key = MakeSpan(key_block + kKeyLen, kKeyLen);
  Span<uint8_t> nonce =
      MakeSpan(key_block + kKeyLen + kKeyLen + kNonceLen, kNonceLen);

  uint8_t ad[13];
  uint64_t seq = SSL_get_write_sequence(server);
  for (size_t i = 0; i < 8; i++) {
    // The nonce is XORed with the sequence number.
    nonce[11 - i] ^= uint8_t(seq);
    ad[7 - i] = uint8_t(seq);
    seq >>= 8;
  }

  ad[8] = SSL3_RT_HANDSHAKE;
  ad[9] = 3;
  ad[10] = 3;  // TLS 1.2
  ad[11] = 0;
  ad[12] = sizeof(in);

  uint8_t record[5 + sizeof(in) + 16];
  record[0] = SSL3_RT_HANDSHAKE;
  record[1] = 3;
  record[2] = 3;  // TLS 1.2
  record[3] = 0;
  record[4] = sizeof(record) - 5;

  ScopedEVP_AEAD_CTX aead;
  ASSERT_TRUE(EVP_AEAD_CTX_init(aead.get(), EVP_aead_chacha20_poly1305(),
                                key.data(), key.size(),
                                EVP_AEAD_DEFAULT_TAG_LENGTH, nullptr));
  size_t len;
  ASSERT_TRUE(EVP_AEAD_CTX_seal(aead.get(), record + 5, &len,
                                sizeof(record) - 5, nonce.data(), nonce.size(),
                                in, sizeof(in), ad, sizeof(ad)));
  ASSERT_EQ(sizeof(record) - 5, len);
#endif  // BORINGSSL_UNSAFE_FUZZER_MODE

  ASSERT_EQ(int(sizeof(record)),
            BIO_write(SSL_get_wbio(server), record, sizeof(record)));
}

TEST_P(SSLTest, WriteWhileExplicitRenegotiate) {
  bssl::UniquePtr<SSL_CTX> ctx(CreateContextWithTestCertificate(TLS_method()));
  ASSERT_TRUE(ctx);

  ASSERT_TRUE(SSL_CTX_set_min_proto_version(ctx.get(), TLS1_2_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(ctx.get(), TLS1_2_VERSION));
  ASSERT_TRUE(SSL_CTX_set_strict_cipher_list(
      ctx.get(), "TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256"));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(CreateClientAndServer(&client, &server, ctx.get(), ctx.get()));
  SSL_set_renegotiate_mode(client.get(), ssl_renegotiate_explicit);
  ASSERT_TRUE(CompleteHandshakes(client.get(), server.get()));

  if (GetParam().transfer_ssl) {
    // |server| is reset to hold the transferred SSL.
    TransferSSL(&server, ctx.get(), nullptr);
  }

  static const uint8_t kInput[] = {'h', 'e', 'l', 'l', 'o'};

  // Write "hello" until the buffer is full, so |client| has a pending write.
  size_t num_writes = 0;
  for (;;) {
    int ret = SSL_write(client.get(), kInput, sizeof(kInput));
    if (ret != int(sizeof(kInput))) {
      ASSERT_EQ(-1, ret);
      ASSERT_EQ(SSL_ERROR_WANT_WRITE, SSL_get_error(client.get(), ret));
      break;
    }
    num_writes++;
  }

  ASSERT_NO_FATAL_FAILURE(WriteHelloRequest(server.get()));

  // |SSL_read| should pick up the HelloRequest.
  uint8_t byte;
  ASSERT_EQ(-1, SSL_read(client.get(), &byte, 1));
  ASSERT_EQ(SSL_ERROR_WANT_RENEGOTIATE, SSL_get_error(client.get(), -1));

  // Drain the data from the |client|.
  uint8_t buf[sizeof(kInput)];
  for (size_t i = 0; i < num_writes; i++) {
    ASSERT_EQ(int(sizeof(buf)), SSL_read(server.get(), buf, sizeof(buf)));
    EXPECT_EQ(Bytes(buf), Bytes(kInput));
  }

  // |client| should be able to finish the pending write and continue to write,
  // despite the paused HelloRequest.
  ASSERT_EQ(int(sizeof(kInput)),
            SSL_write(client.get(), kInput, sizeof(kInput)));
  ASSERT_EQ(int(sizeof(buf)), SSL_read(server.get(), buf, sizeof(buf)));
  EXPECT_EQ(Bytes(buf), Bytes(kInput));

  ASSERT_EQ(int(sizeof(kInput)),
            SSL_write(client.get(), kInput, sizeof(kInput)));
  ASSERT_EQ(int(sizeof(buf)), SSL_read(server.get(), buf, sizeof(buf)));
  EXPECT_EQ(Bytes(buf), Bytes(kInput));

  // |SSL_read| is stuck until we acknowledge the HelloRequest.
  ASSERT_EQ(-1, SSL_read(client.get(), &byte, 1));
  ASSERT_EQ(SSL_ERROR_WANT_RENEGOTIATE, SSL_get_error(client.get(), -1));

  ASSERT_TRUE(SSL_renegotiate(client.get()));
  ASSERT_EQ(-1, SSL_read(client.get(), &byte, 1));
  ASSERT_EQ(SSL_ERROR_WANT_READ, SSL_get_error(client.get(), -1));

  // We never renegotiate as a server.
  ASSERT_EQ(-1, SSL_read(server.get(), buf, sizeof(buf)));
  ASSERT_EQ(SSL_ERROR_SSL, SSL_get_error(server.get(), -1));
  EXPECT_TRUE(
      ErrorEquals(ERR_get_error(), ERR_LIB_SSL, SSL_R_NO_RENEGOTIATION));

  EXPECT_EQ(SSL_CTX_sess_connect_renegotiate(ctx.get()), 1);
  EXPECT_EQ(SSL_CTX_sess_accept_renegotiate(ctx.get()), 0);
}

TEST(SSLTest, ConnectionPropertiesDuringRenegotiate) {
  // Configure known connection properties, so we can check against them.
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  bssl::UniquePtr<X509> cert = GetTestCertificate();
  ASSERT_TRUE(cert);
  bssl::UniquePtr<EVP_PKEY> key = GetTestKey();
  ASSERT_TRUE(key);
  ASSERT_TRUE(SSL_CTX_use_certificate(ctx.get(), cert.get()));
  ASSERT_TRUE(SSL_CTX_use_PrivateKey(ctx.get(), key.get()));
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(ctx.get(), TLS1_2_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(ctx.get(), TLS1_2_VERSION));
  ASSERT_TRUE(SSL_CTX_set_strict_cipher_list(
      ctx.get(), "TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256"));
  ASSERT_TRUE(SSL_CTX_set1_groups_list(ctx.get(), "X25519"));
  ASSERT_TRUE(SSL_CTX_set1_sigalgs_list(ctx.get(), "rsa_pkcs1_sha256"));

  // Connect a client and server that accept renegotiation.
  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(CreateClientAndServer(&client, &server, ctx.get(), ctx.get()));
  SSL_set_renegotiate_mode(client.get(), ssl_renegotiate_freely);
  ASSERT_TRUE(CompleteHandshakes(client.get(), server.get()));

  auto check_properties = [&] {
    EXPECT_EQ(SSL_version(client.get()), TLS1_2_VERSION);
    const SSL_CIPHER *cipher = SSL_get_current_cipher(client.get());
    ASSERT_TRUE(cipher);
    EXPECT_EQ(SSL_CIPHER_get_id(cipher),
              uint32_t{TLS1_CK_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256});
    EXPECT_EQ(SSL_get_group_id(client.get()), SSL_GROUP_X25519);
    EXPECT_EQ(SSL_get_peer_signature_algorithm(client.get()),
              SSL_SIGN_RSA_PKCS1_SHA256);

    int psig_nid;
    EXPECT_TRUE(SSL_get_peer_signature_type_nid(client.get(), &psig_nid));
    EXPECT_EQ(psig_nid, EVP_PKEY_RSA);
    int digest_nid;
    EXPECT_TRUE(SSL_get_peer_signature_nid(client.get(), &digest_nid));
    EXPECT_EQ(digest_nid, NID_sha256);

    bssl::UniquePtr<X509> peer(SSL_get_peer_certificate(client.get()));
    ASSERT_TRUE(peer);
    EXPECT_EQ(X509_cmp(cert.get(), peer.get()), 0);
  };
  check_properties();

  // Client has not signed any TLS messages yet
  EXPECT_FALSE(SSL_get_peer_signature_type_nid(server.get(), nullptr));
  EXPECT_FALSE(SSL_get_peer_signature_nid(server.get(), nullptr));

  // The server sends a HelloRequest.
  ASSERT_NO_FATAL_FAILURE(WriteHelloRequest(server.get()));

  // Reading from the client will consume the HelloRequest, start a
  // renegotiation, and then block on a ServerHello from the server.
  uint8_t byte;
  ASSERT_EQ(-1, SSL_read(client.get(), &byte, 1));
  ASSERT_EQ(SSL_ERROR_WANT_READ, SSL_get_error(client.get(), -1));

  // Connection properties should continue to report values from the original
  // handshake.
  check_properties();
  EXPECT_EQ(SSL_CTX_sess_connect_renegotiate(ctx.get()), 1);
  EXPECT_EQ(SSL_CTX_sess_accept_renegotiate(ctx.get()), 0);

  // Client does not sign any messages in renegotiation either
  EXPECT_FALSE(SSL_get_peer_signature_type_nid(server.get(), nullptr));
  EXPECT_FALSE(SSL_get_peer_signature_nid(server.get(), nullptr));
}

TEST(SSLTest, SSLGetSignatureData) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  bssl::UniquePtr<X509> cert = GetECDSATestCertificate();
  ASSERT_TRUE(cert);
  bssl::UniquePtr<EVP_PKEY> key = GetECDSATestKey();
  ASSERT_TRUE(key);
  ASSERT_TRUE(SSL_CTX_use_certificate(ctx.get(), cert.get()));
  ASSERT_TRUE(SSL_CTX_use_PrivateKey(ctx.get(), key.get()));

  // Explicitly configure |SSL_VERIFY_PEER| so both the client and server
  // verify each other
  SSL_CTX_set_custom_verify(
          ctx.get(), SSL_VERIFY_PEER,
          [](SSL *ssl, uint8_t *out_alert) { return ssl_verify_ok; });

  ASSERT_TRUE(SSL_CTX_set_min_proto_version(ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set1_sigalgs_list(ctx.get(), "ECDSA+SHA256"));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(CreateClientAndServer(&client, &server, ctx.get(), ctx.get()));

  // Before handshake, neither client nor server has signed any messages
  ASSERT_FALSE(SSL_get_peer_signature_nid(client.get(), nullptr));
  ASSERT_FALSE(SSL_get_peer_signature_nid(server.get(), nullptr));
  ASSERT_FALSE(SSL_get_peer_signature_type_nid(client.get(), nullptr));
  ASSERT_FALSE(SSL_get_peer_signature_type_nid(server.get(), nullptr));

  ASSERT_TRUE(CompleteHandshakes(client.get(), server.get()));

  // Both client and server verified each other, both have signed TLS messages
  // now
  int client_digest, client_sigtype;
  ASSERT_TRUE(SSL_get_peer_signature_nid(server.get(), &client_digest));
  ASSERT_TRUE(SSL_get_peer_signature_type_nid(server.get(), &client_sigtype));
  ASSERT_EQ(client_sigtype, EVP_PKEY_EC);
  ASSERT_EQ(client_digest, NID_sha256);

  int server_digest, server_sigtype;
  ASSERT_TRUE(SSL_get_peer_signature_nid(client.get(), &server_digest));
  ASSERT_TRUE(SSL_get_peer_signature_type_nid(client.get(), &server_sigtype));
  ASSERT_EQ(server_sigtype, EVP_PKEY_EC);
  ASSERT_EQ(server_digest, NID_sha256);
}

TEST(SSLTest, CopyWithoutEarlyData) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx(
      CreateContextWithTestCertificate(TLS_method()));
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  SSL_CTX_set_session_cache_mode(client_ctx.get(), SSL_SESS_CACHE_BOTH);
  SSL_CTX_set_session_cache_mode(server_ctx.get(), SSL_SESS_CACHE_BOTH);
  SSL_CTX_set_early_data_enabled(client_ctx.get(), 1);
  SSL_CTX_set_early_data_enabled(server_ctx.get(), 1);

  bssl::UniquePtr<SSL_SESSION> session =
      CreateClientSession(client_ctx.get(), server_ctx.get());
  ASSERT_TRUE(session);

  // The client should attempt early data with |session|.
  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(CreateClientAndServer(&client, &server, client_ctx.get(),
                                    server_ctx.get()));
  SSL_set_session(client.get(), session.get());
  SSL_set_early_data_enabled(client.get(), 1);
  ASSERT_EQ(1, SSL_do_handshake(client.get()));
  EXPECT_TRUE(SSL_in_early_data(client.get()));

  // |SSL_SESSION_copy_without_early_data| should disable early data but
  // still resume the session.
  bssl::UniquePtr<SSL_SESSION> session2(
      SSL_SESSION_copy_without_early_data(session.get()));
  ASSERT_TRUE(session2);
  EXPECT_NE(session.get(), session2.get());
  ASSERT_TRUE(CreateClientAndServer(&client, &server, client_ctx.get(),
                                    server_ctx.get()));
  SSL_set_session(client.get(), session2.get());
  SSL_set_early_data_enabled(client.get(), 1);
  EXPECT_TRUE(CompleteHandshakes(client.get(), server.get()));
  EXPECT_TRUE(SSL_session_reused(client.get()));
  EXPECT_EQ(ssl_early_data_unsupported_for_session,
            SSL_get_early_data_reason(client.get()));

  // |SSL_SESSION_copy_without_early_data| should be a reference count increase
  // when passed an early-data-incapable session.
  bssl::UniquePtr<SSL_SESSION> session3(
      SSL_SESSION_copy_without_early_data(session2.get()));
  EXPECT_EQ(session2.get(), session3.get());
}

TEST(SSLTest, ProcessTLS13NewSessionTicket) {
  // Configure client and server to negotiate TLS 1.3 only.
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx(
      CreateContextWithTestCertificate(TLS_method()));
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(server_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_3_VERSION));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));
  EXPECT_EQ(TLS1_3_VERSION, SSL_version(client.get()));

  // Process a TLS 1.3 NewSessionTicket.
  static const uint8_t kTicket[] = {
      0x04, 0x00, 0x00, 0xb2, 0x00, 0x02, 0xa3, 0x00, 0x04, 0x03, 0x02, 0x01,
      0x01, 0x00, 0x00, 0xa0, 0x01, 0x06, 0x09, 0x11, 0x16, 0x19, 0x21, 0x26,
      0x29, 0x31, 0x36, 0x39, 0x41, 0x46, 0x49, 0x51, 0x03, 0x06, 0x09, 0x13,
      0x16, 0x19, 0x23, 0x26, 0x29, 0x33, 0x36, 0x39, 0x43, 0x46, 0x49, 0x53,
      0xf7, 0x00, 0x29, 0xec, 0xf2, 0xc4, 0xa4, 0x41, 0xfc, 0x30, 0x17, 0x2e,
      0x9f, 0x7c, 0xa8, 0xaf, 0x75, 0x70, 0xf0, 0x1f, 0xc7, 0x98, 0xf7, 0xcf,
      0x5a, 0x5a, 0x6b, 0x5b, 0xfe, 0xf1, 0xe7, 0x3a, 0xe8, 0xf7, 0x6c, 0xd2,
      0xa8, 0xa6, 0x92, 0x5b, 0x96, 0x8d, 0xde, 0xdb, 0xd3, 0x20, 0x6a, 0xcb,
      0x69, 0x06, 0xf4, 0x91, 0x85, 0x2e, 0xe6, 0x5e, 0x0c, 0x59, 0xf2, 0x9e,
      0x9b, 0x79, 0x91, 0x24, 0x7e, 0x4a, 0x32, 0x3d, 0xbe, 0x4b, 0x80, 0x70,
      0xaf, 0xd0, 0x1d, 0xe2, 0xca, 0x05, 0x35, 0x09, 0x09, 0x05, 0x0f, 0xbb,
      0xc4, 0xae, 0xd7, 0xc4, 0xed, 0xd7, 0xae, 0x35, 0xc8, 0x73, 0x63, 0x78,
      0x64, 0xc9, 0x7a, 0x1f, 0xed, 0x7a, 0x9a, 0x47, 0x44, 0xfd, 0x50, 0xf7,
      0xb7, 0xe0, 0x64, 0xa9, 0x02, 0xc1, 0x5c, 0x23, 0x18, 0x3f, 0xc4, 0xcf,
      0x72, 0x02, 0x59, 0x2d, 0xe1, 0xaa, 0x61, 0x72, 0x00, 0x04, 0x5a, 0x5a,
      0x00, 0x00,
  };
  bssl::UniquePtr<SSL_SESSION> session(SSL_process_tls13_new_session_ticket(
      client.get(), kTicket, sizeof(kTicket)));
  ASSERT_TRUE(session);
  ASSERT_TRUE(SSL_SESSION_has_ticket(session.get()));

  uint8_t *session_buf = nullptr;
  size_t session_length = 0;
  ASSERT_TRUE(
      SSL_SESSION_to_bytes(session.get(), &session_buf, &session_length));
  bssl::UniquePtr<uint8_t> session_buf_free(session_buf);
  ASSERT_TRUE(session_buf);
  ASSERT_GT(session_length, 0u);

  // Servers cannot call |SSL_process_tls13_new_session_ticket|.
  ASSERT_FALSE(SSL_process_tls13_new_session_ticket(server.get(), kTicket,
                                                    sizeof(kTicket)));

  // Clients cannot call |SSL_process_tls13_new_session_ticket| before the
  // handshake completes.
  bssl::UniquePtr<SSL> client2(SSL_new(client_ctx.get()));
  ASSERT_TRUE(client2);
  SSL_set_connect_state(client2.get());
  ASSERT_FALSE(SSL_process_tls13_new_session_ticket(client2.get(), kTicket,
                                                    sizeof(kTicket)));
}

TEST(SSLTest, BIO) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx(
      CreateContextWithTestCertificate(TLS_method()));
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  for (bool take_ownership : {true, false}) {
    // For simplicity, get the handshake out of the way first.
    bssl::UniquePtr<SSL> client, server;
    ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                       server_ctx.get()));

    // Wrap |client| in an SSL BIO.
    bssl::UniquePtr<BIO> client_bio(BIO_new(BIO_f_ssl()));
    ASSERT_TRUE(client_bio);
    ASSERT_EQ(1, BIO_set_ssl(client_bio.get(), client.get(), take_ownership));
    if (take_ownership) {
      client.release();
    }

    // Flushing the BIO should not crash.
    EXPECT_EQ(1, BIO_flush(client_bio.get()));

    // Exchange some data.
    EXPECT_EQ(5, BIO_write(client_bio.get(), "hello", 5));
    uint8_t buf[5];
    ASSERT_EQ(5, SSL_read(server.get(), buf, sizeof(buf)));
    EXPECT_EQ(Bytes("hello"), Bytes(buf));

    EXPECT_EQ(5, SSL_write(server.get(), "world", 5));
    ASSERT_EQ(5, BIO_read(client_bio.get(), buf, sizeof(buf)));
    EXPECT_EQ(Bytes("world"), Bytes(buf));

    // |BIO_should_read| should work.
    EXPECT_EQ(-1, BIO_read(client_bio.get(), buf, sizeof(buf)));
    EXPECT_TRUE(BIO_should_read(client_bio.get()));

    // Writing data should eventually exceed the buffer size and fail, reporting
    // |BIO_should_write|.
    int ret;
    for (int i = 0; i < 1024; i++) {
      const uint8_t kZeros[1024] = {0};
      ret = BIO_write(client_bio.get(), kZeros, sizeof(kZeros));
      if (ret <= 0) {
        break;
      }
    }
    EXPECT_EQ(-1, ret);
    EXPECT_TRUE(BIO_should_write(client_bio.get()));
  }
}

TEST(SSLTest, BIO_2) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx(
      CreateContextWithTestCertificate(TLS_method()));
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  bssl::UniquePtr<BIO> server_bio(BIO_new_ssl(server_ctx.get(), 0));
  bssl::UniquePtr<BIO> client_bio(BIO_new_ssl_connect(client_ctx.get()));
  ASSERT_TRUE(server_bio);
  ASSERT_TRUE(client_bio);

  SSL *server_ssl_ptr, *client_ssl_ptr;
  ASSERT_TRUE(BIO_get_ssl(server_bio.get(), &server_ssl_ptr));
  ASSERT_TRUE(BIO_get_ssl(client_bio.get(), &client_ssl_ptr));
  ASSERT_TRUE(server_ssl_ptr);
  ASSERT_TRUE(client_ssl_ptr);

  // Client SSL BIOs typically establish connections to a host using
  // |BIO_do_connect|, which leverages the underlying connect |BIO| for socket
  // management. While OpenSSL provides |BIO_new_accept| and |BIO_s_accept| for
  // server-side socket setup, we haven't yet implemented this functionality.
  // For these tests, we opt for traditional SSL connection methods instead
  // until we have support for server-side socket management via |BIO|s.
  // Adding full socket management on the server side would exceed the scope of
  // testing |BIO_new_ssl(_connect)|, especially since we have dedicated tests
  // elsewhere that verify |BIO_do_connect|'s correctness.
  BIO *bio1, *bio2;
  ASSERT_TRUE(BIO_new_bio_pair(&bio1, 0, &bio2, 0));
  SSL_set_bio(client_ssl_ptr, bio1, bio1);
  SSL_set_bio(server_ssl_ptr, bio2, bio2);
  ASSERT_TRUE(CompleteHandshakes(client_ssl_ptr, server_ssl_ptr));
}

TEST(SSLTest, ALPNConfig) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  bssl::UniquePtr<X509> cert = GetTestCertificate();
  bssl::UniquePtr<EVP_PKEY> key = GetTestKey();
  ASSERT_TRUE(cert);
  ASSERT_TRUE(key);
  ASSERT_TRUE(SSL_CTX_use_certificate(ctx.get(), cert.get()));
  ASSERT_TRUE(SSL_CTX_use_PrivateKey(ctx.get(), key.get()));

  // Set up some machinery to check the configured ALPN against what is actually
  // sent over the wire. Note that the ALPN callback is only called when the
  // client offers ALPN.
  std::vector<uint8_t> observed_alpn;
  SSL_CTX_set_alpn_select_cb(
      ctx.get(),
      [](SSL *ssl, const uint8_t **out, uint8_t *out_len, const uint8_t *in,
         unsigned in_len, void *arg) -> int {
        std::vector<uint8_t> *observed_alpn_ptr =
            static_cast<std::vector<uint8_t> *>(arg);
        observed_alpn_ptr->assign(in, in + in_len);
        return SSL_TLSEXT_ERR_NOACK;
      },
      &observed_alpn);
  auto check_alpn_proto = [&](Span<const uint8_t> expected) {
    observed_alpn.clear();
    bssl::UniquePtr<SSL> client, server;
    ASSERT_TRUE(ConnectClientAndServer(&client, &server, ctx.get(), ctx.get()));
    EXPECT_EQ(Bytes(expected), Bytes(observed_alpn));
  };

  // Note that |SSL_CTX_set_alpn_protos|'s return value is reversed.
  static const uint8_t kValidList[] = {0x03, 'f', 'o', 'o',
                                       0x03, 'b', 'a', 'r'};
  EXPECT_EQ(0,
            SSL_CTX_set_alpn_protos(ctx.get(), kValidList, sizeof(kValidList)));
  check_alpn_proto(kValidList);

  // Invalid lists are rejected.
  static const uint8_t kInvalidList[] = {0x04, 'f', 'o', 'o'};
  EXPECT_EQ(1, SSL_CTX_set_alpn_protos(ctx.get(), kInvalidList,
                                       sizeof(kInvalidList)));

  // Empty lists are valid and are interpreted as disabling ALPN.
  EXPECT_EQ(0, SSL_CTX_set_alpn_protos(ctx.get(), nullptr, 0));
  check_alpn_proto({});
}



// Test that the key usage checker can correctly handle issuerUID and
// subjectUID. See https://crbug.com/1199744.
TEST(SSLTest, KeyUsageWithUIDs) {
  static const char kGoodKeyUsage[] = R"(
-----BEGIN CERTIFICATE-----
MIIB7DCCAZOgAwIBAgIJANlMBNpJfb/rMAoGCCqGSM49BAMCMEUxCzAJBgNVBAYT
AkFVMRMwEQYDVQQIDApTb21lLVN0YXRlMSEwHwYDVQQKDBhJbnRlcm5ldCBXaWRn
aXRzIFB0eSBMdGQwHhcNMTQwNDIzMjMyMTU3WhcNMTQwNTIzMjMyMTU3WjBFMQsw
CQYDVQQGEwJBVTETMBEGA1UECAwKU29tZS1TdGF0ZTEhMB8GA1UECgwYSW50ZXJu
ZXQgV2lkZ2l0cyBQdHkgTHRkMFkwEwYHKoZIzj0CAQYIKoZIzj0DAQcDQgAE5itp
4r9ln5e+Lx4NlIpM1Zdrt6keDUb73ampHp3culoB59aXqAoY+cPEox5W4nyDSNsW
Ghz1HX7xlC1Lz3IiwYEEABI0VoIEABI0VqNgMF4wHQYDVR0OBBYEFKuE0qyrlfCC
ThZ4B1VXX+QmjYLRMB8GA1UdIwQYMBaAFKuE0qyrlfCCThZ4B1VXX+QmjYLRMA4G
A1UdDwEB/wQEAwIHgDAMBgNVHRMEBTADAQH/MAoGCCqGSM49BAMCA0cAMEQCIEWJ
34EcqW5MHwLIA1hZ2Tj/jV2QjN02KLxis9mFsqDKAiAMlMTkzsM51vVs9Ohqa+Rc
4Z7qDhjIhiF4dM0uEDYRVA==
-----END CERTIFICATE-----
)";
  static const char kBadKeyUsage[] = R"(
-----BEGIN CERTIFICATE-----
MIIB7jCCAZOgAwIBAgIJANlMBNpJfb/rMAoGCCqGSM49BAMCMEUxCzAJBgNVBAYT
AkFVMRMwEQYDVQQIDApTb21lLVN0YXRlMSEwHwYDVQQKDBhJbnRlcm5ldCBXaWRn
aXRzIFB0eSBMdGQwHhcNMTQwNDIzMjMyMTU3WhcNMTQwNTIzMjMyMTU3WjBFMQsw
CQYDVQQGEwJBVTETMBEGA1UECAwKU29tZS1TdGF0ZTEhMB8GA1UECgwYSW50ZXJu
ZXQgV2lkZ2l0cyBQdHkgTHRkMFkwEwYHKoZIzj0CAQYIKoZIzj0DAQcDQgAE5itp
4r9ln5e+Lx4NlIpM1Zdrt6keDUb73ampHp3culoB59aXqAoY+cPEox5W4nyDSNsW
Ghz1HX7xlC1Lz3IiwYEEABI0VoIEABI0VqNgMF4wHQYDVR0OBBYEFKuE0qyrlfCC
ThZ4B1VXX+QmjYLRMB8GA1UdIwQYMBaAFKuE0qyrlfCCThZ4B1VXX+QmjYLRMA4G
A1UdDwEB/wQEAwIDCDAMBgNVHRMEBTADAQH/MAoGCCqGSM49BAMCA0kAMEYCIQC6
taYBUDu2gcZC6EMk79FBHArYI0ucF+kzvETegZCbBAIhANtObFec5gtso/47moPD
RHrQbWsFUakETXL9QMlegh5t
-----END CERTIFICATE-----
)";

  bssl::UniquePtr<X509> good = CertFromPEM(kGoodKeyUsage);
  ASSERT_TRUE(good);
  bssl::UniquePtr<X509> bad = CertFromPEM(kBadKeyUsage);
  ASSERT_TRUE(bad);

  // We check key usage when configuring EC certificates to distinguish ECDSA
  // and ECDH.
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  EXPECT_TRUE(SSL_CTX_use_certificate(ctx.get(), good.get()));
  EXPECT_FALSE(SSL_CTX_use_certificate(ctx.get(), bad.get()));
}

// Test that |SSL_can_release_private_key| reports true as early as expected.
// The internal asserts in the library check we do not report true too early.
TEST(SSLTest, CanReleasePrivateKey) {
  bssl::UniquePtr<SSL_CTX> client_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  SSL_CTX_set_session_cache_mode(client_ctx.get(), SSL_SESS_CACHE_BOTH);

  // Note this assumes the transport buffer is large enough to fit the client
  // and server first flights. We check this with |SSL_ERROR_WANT_READ|. If the
  // transport buffer was too small it would return |SSL_ERROR_WANT_WRITE|.
  auto check_first_server_round_trip = [&](SSL *client, SSL *server) {
    // Write the ClientHello.
    ASSERT_EQ(-1, SSL_do_handshake(client));
    ASSERT_EQ(SSL_ERROR_WANT_READ, SSL_get_error(client, -1));

    // Consume the ClientHello and write the server flight.
    ASSERT_EQ(-1, SSL_do_handshake(server));
    ASSERT_EQ(SSL_ERROR_WANT_READ, SSL_get_error(server, -1));

    EXPECT_TRUE(SSL_can_release_private_key(server));
  };

  {
    SCOPED_TRACE("TLS 1.2 ECDHE");
    bssl::UniquePtr<SSL_CTX> server_ctx(
        CreateContextWithTestCertificate(TLS_method()));
    ASSERT_TRUE(server_ctx);
    ASSERT_TRUE(
        SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_2_VERSION));
    ASSERT_TRUE(SSL_CTX_set_strict_cipher_list(
        server_ctx.get(), "TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256"));
    // Configure the server to request client certificates, so we can also test
    // the client half.
    SSL_CTX_set_custom_verify(
        server_ctx.get(), SSL_VERIFY_PEER,
        [](SSL *ssl, uint8_t *out_alert) { return ssl_verify_ok; });
    bssl::UniquePtr<SSL> client, server;
    ASSERT_TRUE(CreateClientAndServer(&client, &server, client_ctx.get(),
                                      server_ctx.get()));
    check_first_server_round_trip(client.get(), server.get());

    // Consume the server flight and write the client response. The client still
    // has a Finished message to consume but can also release its key early.
    ASSERT_EQ(-1, SSL_do_handshake(client.get()));
    ASSERT_EQ(SSL_ERROR_WANT_READ, SSL_get_error(client.get(), -1));
    EXPECT_TRUE(SSL_can_release_private_key(client.get()));

    // However, a client that has not disabled renegotiation can never release
    // the key.
    ASSERT_TRUE(CreateClientAndServer(&client, &server, client_ctx.get(),
                                      server_ctx.get()));
    SSL_set_renegotiate_mode(client.get(), ssl_renegotiate_freely);
    check_first_server_round_trip(client.get(), server.get());
    ASSERT_EQ(-1, SSL_do_handshake(client.get()));
    ASSERT_EQ(SSL_ERROR_WANT_READ, SSL_get_error(client.get(), -1));
    EXPECT_FALSE(SSL_can_release_private_key(client.get()));
  }

  {
    SCOPED_TRACE("TLS 1.2 resumption");
    bssl::UniquePtr<SSL_CTX> server_ctx(
        CreateContextWithTestCertificate(TLS_method()));
    ASSERT_TRUE(server_ctx);
    ASSERT_TRUE(
        SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_2_VERSION));
    bssl::UniquePtr<SSL_SESSION> session =
        CreateClientSession(client_ctx.get(), server_ctx.get());
    ASSERT_TRUE(session);
    bssl::UniquePtr<SSL> client, server;
    ASSERT_TRUE(CreateClientAndServer(&client, &server, client_ctx.get(),
                                      server_ctx.get()));
    SSL_set_session(client.get(), session.get());
    check_first_server_round_trip(client.get(), server.get());
  }

  {
    SCOPED_TRACE("TLS 1.3 1-RTT");
    bssl::UniquePtr<SSL_CTX> server_ctx(
        CreateContextWithTestCertificate(TLS_method()));
    ASSERT_TRUE(server_ctx);
    ASSERT_TRUE(
        SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_3_VERSION));
    bssl::UniquePtr<SSL> client, server;
    ASSERT_TRUE(CreateClientAndServer(&client, &server, client_ctx.get(),
                                      server_ctx.get()));
    check_first_server_round_trip(client.get(), server.get());
  }

  {
    SCOPED_TRACE("TLS 1.3 resumption");
    bssl::UniquePtr<SSL_CTX> server_ctx(
        CreateContextWithTestCertificate(TLS_method()));
    ASSERT_TRUE(server_ctx);
    ASSERT_TRUE(
        SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_3_VERSION));
    bssl::UniquePtr<SSL_SESSION> session =
        CreateClientSession(client_ctx.get(), server_ctx.get());
    ASSERT_TRUE(session);
    bssl::UniquePtr<SSL> client, server;
    ASSERT_TRUE(CreateClientAndServer(&client, &server, client_ctx.get(),
                                      server_ctx.get()));
    SSL_set_session(client.get(), session.get());
    check_first_server_round_trip(client.get(), server.get());
  }
}



TEST(SSLTest, HostMatching) {
  static const char kCertPEM[] = R"(
-----BEGIN CERTIFICATE-----
MIIB9jCCAZ2gAwIBAgIQeudG9R61BOxUvWkeVhU5DTAKBggqhkjOPQQDAjApMRAw
DgYDVQQKEwdBY21lIENvMRUwEwYDVQQDEwxleGFtcGxlMy5jb20wHhcNMjExMjA2
MjA1NjU2WhcNMjIxMjA2MjA1NjU2WjApMRAwDgYDVQQKEwdBY21lIENvMRUwEwYD
VQQDEwxleGFtcGxlMy5jb20wWTATBgcqhkjOPQIBBggqhkjOPQMBBwNCAAS7l2VO
Bl2TjVm9WfGk24+hMbVFUNB+RVHWbCvFvNZAoWiIJ2z34RLGInyZvCZ8xLAvsuaW
ULDDaoeDl1M0t4Hmo4GmMIGjMA4GA1UdDwEB/wQEAwIChDATBgNVHSUEDDAKBggr
BgEFBQcDATAPBgNVHRMBAf8EBTADAQH/MB0GA1UdDgQWBBTTJWurcc1t+VPQBko3
Gsw6cbcWSTBMBgNVHREERTBDggxleGFtcGxlMS5jb22CDGV4YW1wbGUyLmNvbYIP
YSouZXhhbXBsZTQuY29tgg4qLmV4YW1wbGU1LmNvbYcEAQIDBDAKBggqhkjOPQQD
AgNHADBEAiAAv0ljHJGrgyzZDkG6XvNZ5ewxRfnXcZuD0Y7E4giCZgIgNK1qjilu
5DyVbfKeeJhOCtGxqE1dWLXyJBnoRomSYBY=
-----END CERTIFICATE-----
)";
  bssl::UniquePtr<X509> cert(CertFromPEM(kCertPEM));
  ASSERT_TRUE(cert);
  static const char kCertNoSANsPEM[] = R"(
-----BEGIN CERTIFICATE-----
MIIBqzCCAVGgAwIBAgIQeudG9R61BOxUvWkeVhU5DTAKBggqhkjOPQQDAjArMRIw
EAYDVQQKEwlBY21lIENvIDIxFTATBgNVBAMTDGV4YW1wbGUzLmNvbTAeFw0yMTEy
MDYyMDU2NTZaFw0yMjEyMDYyMDU2NTZaMCsxEjAQBgNVBAoTCUFjbWUgQ28gMjEV
MBMGA1UEAxMMZXhhbXBsZTMuY29tMFkwEwYHKoZIzj0CAQYIKoZIzj0DAQcDQgAE
u5dlTgZdk41ZvVnxpNuPoTG1RVDQfkVR1mwrxbzWQKFoiCds9+ESxiJ8mbwmfMSw
L7LmllCww2qHg5dTNLeB5qNXMFUwDgYDVR0PAQH/BAQDAgKEMBMGA1UdJQQMMAoG
CCsGAQUFBwMBMA8GA1UdEwEB/wQFMAMBAf8wHQYDVR0OBBYEFNMla6txzW35U9AG
SjcazDpxtxZJMAoGCCqGSM49BAMCA0gAMEUCIG3YWGWtpVhbcGV7wFKQwTfmvwHW
pw4qCFZlool4hCwsAiEA+2fc6NfSbNpFEtQkDOMJW2ANiScAVEmImNqPfb2klz4=
-----END CERTIFICATE-----
)";
  bssl::UniquePtr<X509> cert_no_sans(CertFromPEM(kCertNoSANsPEM));
  ASSERT_TRUE(cert_no_sans);

  static const char kKeyPEM[] = R"(
-----BEGIN PRIVATE KEY-----
MIGHAgEAMBMGByqGSM49AgEGCCqGSM49AwEHBG0wawIBAQQghsaSZhUzZAcQlLyJ
MDuy7WPdyqNsAX9rmEP650LF/q2hRANCAAS7l2VOBl2TjVm9WfGk24+hMbVFUNB+
RVHWbCvFvNZAoWiIJ2z34RLGInyZvCZ8xLAvsuaWULDDaoeDl1M0t4Hm
-----END PRIVATE KEY-----
)";
  bssl::UniquePtr<EVP_PKEY> key(KeyFromPEM(kKeyPEM));
  ASSERT_TRUE(key);

  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(X509_STORE_add_cert(SSL_CTX_get_cert_store(client_ctx.get()),
                                  cert.get()));
  ASSERT_TRUE(X509_STORE_add_cert(SSL_CTX_get_cert_store(client_ctx.get()),
                                  cert_no_sans.get()));
  SSL_CTX_set_verify(client_ctx.get(),
                     SSL_VERIFY_PEER | SSL_VERIFY_FAIL_IF_NO_PEER_CERT,
                     nullptr);
  X509_VERIFY_PARAM_set_flags(SSL_CTX_get0_param(client_ctx.get()),
                              X509_V_FLAG_NO_CHECK_TIME);

  struct TestCase {
    X509 *cert;
    std::string hostname;
    unsigned flags;
    bool should_match;
  };
  std::vector<TestCase> kTests = {
      // These two names are present as SANs in the certificate.
      {cert.get(), "example1.com", 0, true},
      {cert.get(), "example2.com", 0, true},
      // This is the CN of the certificate, but that shouldn't matter if a SAN
      // extension is present.
      {cert.get(), "example3.com", 0, false},
      // If the SAN is not present, we, for now, look for DNS names in the CN.
      {cert_no_sans.get(), "example3.com", 0, true},
      // ... but this can be turned off.
      {cert_no_sans.get(), "example3.com", X509_CHECK_FLAG_NEVER_CHECK_SUBJECT,
       false},
      // a*.example4.com is a SAN, but is invalid.
      {cert.get(), "abc.example4.com", 0, false},
      // *.example5.com is a SAN in the certificate, which is a normal and valid
      // wildcard.
      {cert.get(), "abc.example5.com", 0, true},
      // This name is not present.
      {cert.get(), "notexample1.com", 0, false},
      // The IPv4 address 1.2.3.4 is a SAN, but that shouldn't match against a
      // hostname that happens to be its textual representation.
      {cert.get(), "1.2.3.4", 0, false},
  };

  for (const TestCase &test : kTests) {
    SCOPED_TRACE(test.hostname);

    bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(server_ctx);
    ASSERT_TRUE(SSL_CTX_use_certificate(server_ctx.get(), test.cert));
    ASSERT_TRUE(SSL_CTX_use_PrivateKey(server_ctx.get(), key.get()));

    ClientConfig config;
    bssl::UniquePtr<SSL> client, server;
    config.verify_hostname = test.hostname;
    config.hostflags = test.flags;
    EXPECT_EQ(test.should_match,
              ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get(), config));
  }
}

TEST(SSLTest, NumTickets) {
  bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(server_ctx);
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(client_ctx);
  bssl::UniquePtr<X509> cert = GetTestCertificate();
  ASSERT_TRUE(cert);
  bssl::UniquePtr<EVP_PKEY> key = GetTestKey();
  ASSERT_TRUE(key);
  ASSERT_TRUE(SSL_CTX_use_certificate(server_ctx.get(), cert.get()));
  ASSERT_TRUE(SSL_CTX_use_PrivateKey(server_ctx.get(), key.get()));
  SSL_CTX_set_session_cache_mode(server_ctx.get(), SSL_SESS_CACHE_BOTH);

  SSL_CTX_set_session_cache_mode(client_ctx.get(), SSL_SESS_CACHE_BOTH);
  static size_t ticket_count;
  SSL_CTX_sess_set_new_cb(client_ctx.get(), [](SSL *, SSL_SESSION *) -> int {
    ticket_count++;
    return 0;
  });

  auto count_tickets = [&]() -> size_t {
    ticket_count = 0;
    bssl::UniquePtr<SSL> client, server;
    if (!ConnectClientAndServer(&client, &server, client_ctx.get(),
                                server_ctx.get()) ||
        !FlushNewSessionTickets(client.get(), server.get())) {
      ADD_FAILURE() << "Could not run handshake";
      return 0;
    }
    return ticket_count;
  };

  // By default, we should send two tickets.
  EXPECT_EQ(count_tickets(), 2u);

  for (size_t num_tickets : {0, 1, 2, 3, 4, 5}) {
    SCOPED_TRACE(num_tickets);
    ASSERT_TRUE(SSL_CTX_set_num_tickets(server_ctx.get(), num_tickets));
    EXPECT_EQ(SSL_CTX_get_num_tickets(server_ctx.get()), num_tickets);
    EXPECT_EQ(count_tickets(), num_tickets);
  }

  // Configuring too many tickets causes us to stop at some point.
  ASSERT_TRUE(SSL_CTX_set_num_tickets(server_ctx.get(), 100000));
  EXPECT_EQ(SSL_CTX_get_num_tickets(server_ctx.get()), 16u);
  EXPECT_EQ(count_tickets(), 16u);
}

TEST(SSLTest, CertSubjectsToStack) {
  const std::string kCert1 = R"(
-----BEGIN CERTIFICATE-----
MIIBzzCCAXagAwIBAgIJANlMBNpJfb/rMAkGByqGSM49BAEwRTELMAkGA1UEBhMC
QVUxEzARBgNVBAgMClNvbWUtU3RhdGUxITAfBgNVBAoMGEludGVybmV0IFdpZGdp
dHMgUHR5IEx0ZDAeFw0xNDA0MjMyMzIxNTdaFw0xNDA1MjMyMzIxNTdaMEUxCzAJ
BgNVBAYTAkFVMRMwEQYDVQQIDApTb21lLVN0YXRlMSEwHwYDVQQKDBhJbnRlcm5l
dCBXaWRnaXRzIFB0eSBMdGQwWTATBgcqhkjOPQIBBggqhkjOPQMBBwNCAATmK2ni
v2Wfl74vHg2UikzVl2u3qR4NRvvdqakendy6WgHn1peoChj5w8SjHlbifINI2xYa
HPUdfvGULUvPciLBo1AwTjAdBgNVHQ4EFgQUq4TSrKuV8IJOFngHVVdf5CaNgtEw
HwYDVR0jBBgwFoAUq4TSrKuV8IJOFngHVVdf5CaNgtEwDAYDVR0TBAUwAwEB/zAJ
BgcqhkjOPQQBA0gAMEUCIQDyoDVeUTo2w4J5m+4nUIWOcAZ0lVfSKXQA9L4Vh13E
BwIgfB55FGohg/B6dGh5XxSZmmi08cueFV7mHzJSYV51yRQ=
-----END CERTIFICATE-----
)";
  const std::vector<uint8_t> kName1 = {
      0x30, 0x45, 0x31, 0x0b, 0x30, 0x09, 0x06, 0x03, 0x55, 0x04, 0x06, 0x13,
      0x02, 0x41, 0x55, 0x31, 0x13, 0x30, 0x11, 0x06, 0x03, 0x55, 0x04, 0x08,
      0x0c, 0x0a, 0x53, 0x6f, 0x6d, 0x65, 0x2d, 0x53, 0x74, 0x61, 0x74, 0x65,
      0x31, 0x21, 0x30, 0x1f, 0x06, 0x03, 0x55, 0x04, 0x0a, 0x0c, 0x18, 0x49,
      0x6e, 0x74, 0x65, 0x72, 0x6e, 0x65, 0x74, 0x20, 0x57, 0x69, 0x64, 0x67,
      0x69, 0x74, 0x73, 0x20, 0x50, 0x74, 0x79, 0x20, 0x4c, 0x74, 0x64};
  const std::string kCert2 = R"(
-----BEGIN CERTIFICATE-----
MIICXjCCAcegAwIBAgIIWjO48ufpunYwDQYJKoZIhvcNAQELBQAwNjEaMBgGA1UE
ChMRQm9yaW5nU1NMIFRFU1RJTkcxGDAWBgNVBAMTD0ludGVybWVkaWF0ZSBDQTAg
Fw0xNTAxMDEwMDAwMDBaGA8yMTAwMDEwMTAwMDAwMFowMjEaMBgGA1UEChMRQm9y
aW5nU1NMIFRFU1RJTkcxFDASBgNVBAMTC2V4YW1wbGUuY29tMIGfMA0GCSqGSIb3
DQEBAQUAA4GNADCBiQKBgQDD0U0ZYgqShJ7oOjsyNKyVXEHqeafmk/bAoPqY/h1c
oPw2E8KmeqiUSoTPjG5IXSblOxcqpbAXgnjPzo8DI3GNMhAf8SYNYsoH7gc7Uy7j
5x8bUrisGnuTHqkqH6d4/e7ETJ7i3CpR8bvK16DggEvQTudLipz8FBHtYhFakfdh
TwIDAQABo3cwdTAOBgNVHQ8BAf8EBAMCBaAwHQYDVR0lBBYwFAYIKwYBBQUHAwEG
CCsGAQUFBwMCMAwGA1UdEwEB/wQCMAAwGQYDVR0OBBIEEKN5pvbur7mlXjeMEYA0
4nUwGwYDVR0jBBQwEoAQjBpoqLV2211Xex+NFLIGozANBgkqhkiG9w0BAQsFAAOB
gQBj/p+JChp//LnXWC1k121LM/ii7hFzQzMrt70bny406SGz9jAjaPOX4S3gt38y
rhjpPukBlSzgQXFg66y6q5qp1nQTD1Cw6NkKBe9WuBlY3iYfmsf7WT8nhlT1CttU
xNCwyMX9mtdXdQicOfNjIGUCD5OLV5PgHFPRKiHHioBAhg==
-----END CERTIFICATE-----
)";
  const std::vector<uint8_t> kName2 = {
      0x30, 0x32, 0x31, 0x1a, 0x30, 0x18, 0x06, 0x03, 0x55, 0x04, 0x0a,
      0x13, 0x11, 0x42, 0x6f, 0x72, 0x69, 0x6e, 0x67, 0x53, 0x53, 0x4c,
      0x20, 0x54, 0x45, 0x53, 0x54, 0x49, 0x4e, 0x47, 0x31, 0x14, 0x30,
      0x12, 0x06, 0x03, 0x55, 0x04, 0x03, 0x13, 0x0b, 0x65, 0x78, 0x61,
      0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d};

  const struct {
    std::vector<std::vector<uint8_t>> existing;
    std::string pem;
    std::vector<std::vector<uint8_t>> expected;
  } kTests[] = {
      // Do nothing.
      {{}, "", {}},
      // Append to an empty list, skipping duplicates.
      {{}, kCert1 + kCert2 + kCert1, {kName1, kName2}},
      // One of the names was already present.
      {{kName1}, kCert1 + kCert2, {kName1, kName2}},
      // Both names were already present.
      {{kName1, kName2}, kCert1 + kCert2, {kName1, kName2}},
      // Preserve existing duplicates.
      {{kName1, kName2, kName2}, kCert1 + kCert2, {kName1, kName2, kName2}},
  };
  for (size_t i = 0; i < OPENSSL_ARRAY_SIZE(kTests); i++) {
    SCOPED_TRACE(i);
    const auto &t = kTests[i];

    bssl::UniquePtr<STACK_OF(X509_NAME)> stack(sk_X509_NAME_new_null());
    ASSERT_TRUE(stack);
    for (const auto &name : t.existing) {
      const uint8_t *inp = name.data();
      bssl::UniquePtr<X509_NAME> name_obj(
          d2i_X509_NAME(nullptr, &inp, name.size()));
      ASSERT_TRUE(name_obj);
      EXPECT_EQ(inp, name.data() + name.size());
      ASSERT_TRUE(bssl::PushToStack(stack.get(), std::move(name_obj)));
    }

    bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(t.pem.data(), t.pem.size()));
    ASSERT_TRUE(bio);
    ASSERT_TRUE(SSL_add_bio_cert_subjects_to_stack(stack.get(), bio.get()));

    // The function should have left |stack|'s comparison function alone.
    EXPECT_EQ(nullptr, sk_X509_NAME_set_cmp_func(stack.get(), nullptr));

    std::vector<std::vector<uint8_t>> expected = t.expected, result;
    for (X509_NAME *name : stack.get()) {
      uint8_t *der = nullptr;
      int der_len = i2d_X509_NAME(name, &der);
      ASSERT_GE(der_len, 0);
      result.push_back(std::vector<uint8_t>(der, der + der_len));
      OPENSSL_free(der);
    }

    // |SSL_add_bio_cert_subjects_to_stack| does not return the output in a
    // well-defined order.
    std::sort(expected.begin(), expected.end());
    std::sort(result.begin(), result.end());
    EXPECT_EQ(result, expected);
  }
}

TEST(SSLTest, EmptyClientCAList) {
  if (SkipTempFileTests()) {
    GTEST_SKIP();
  }

  TemporaryFile empty;
  ASSERT_TRUE(empty.Init());
  bssl::UniquePtr<STACK_OF(X509_NAME)> names(
      SSL_load_client_CA_file(empty.path().c_str()));
  EXPECT_FALSE(names);
}

TEST(SSLTest, EmptyWriteBlockedOnHandshakeData) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);
  // Configure only TLS 1.3. This test requires post-handshake NewSessionTicket.
  ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_3_VERSION));

  // Connect a client and server with tiny buffer between the two.
  bssl::UniquePtr<SSL> client(SSL_new(client_ctx.get())),
      server(SSL_new(server_ctx.get()));
  ASSERT_TRUE(client);
  ASSERT_TRUE(server);
  SSL_set_connect_state(client.get());
  SSL_set_accept_state(server.get());
  BIO *bio1, *bio2;
  ASSERT_TRUE(BIO_new_bio_pair(&bio1, 1, &bio2, 1));
  SSL_set_bio(client.get(), bio1, bio1);
  SSL_set_bio(server.get(), bio2, bio2);
  ASSERT_TRUE(CompleteHandshakes(client.get(), server.get()));

  // We defer NewSessionTicket to the first write, so the server has a pending
  // NewSessionTicket. See https://boringssl-review.googlesource.com/34948. This
  // means an empty write will flush the ticket. However, the transport only
  // allows one byte through, so this will fail with |SSL_ERROR_WANT_WRITE|.
  int ret = SSL_write(server.get(), nullptr, 0);
  ASSERT_EQ(ret, -1);
  ASSERT_EQ(SSL_get_error(server.get(), ret), SSL_ERROR_WANT_WRITE);

  // Attempting to write non-zero data should not trip |SSL_R_BAD_WRITE_RETRY|.
  const uint8_t kData[] = {'h', 'e', 'l', 'l', 'o'};
  ret = SSL_write(server.get(), kData, sizeof(kData));
  ASSERT_EQ(ret, -1);
  ASSERT_EQ(SSL_get_error(server.get(), ret), SSL_ERROR_WANT_WRITE);

  // Byte by byte, the data should eventually get through.
  uint8_t buf[sizeof(kData)];
  for (;;) {
    ret = SSL_read(client.get(), buf, sizeof(buf));
    ASSERT_EQ(ret, -1);
    ASSERT_EQ(SSL_get_error(client.get(), ret), SSL_ERROR_WANT_READ);

    ret = SSL_write(server.get(), kData, sizeof(kData));
    if (ret > 0) {
      ASSERT_EQ(ret, 5);
      break;
    }
    ASSERT_EQ(ret, -1);
    ASSERT_EQ(SSL_get_error(server.get(), ret), SSL_ERROR_WANT_WRITE);
  }

  ret = SSL_read(client.get(), buf, sizeof(buf));
  ASSERT_EQ(ret, static_cast<int>(sizeof(kData)));
  ASSERT_EQ(Bytes(buf, ret), Bytes(kData));
}

// Test that |SSL_ERROR_SYSCALL| continues to work after a close_notify.
TEST(SSLTest, ErrorSyscallAfterCloseNotify) {
  // Make a custom |BIO| where writes fail, but without pushing to the error
  // queue.
  bssl::UniquePtr<BIO_METHOD> method(BIO_meth_new(0, nullptr));
  ASSERT_TRUE(method);
  BIO_meth_set_create(method.get(), [](BIO *b) -> int {
    BIO_set_init(b, 1);
    return 1;
  });
  static bool write_failed = false;
  BIO_meth_set_write(method.get(), [](BIO *, const char *, int) -> int {
    // Fail the operation and don't add to the error queue.
    write_failed = true;
    return -1;
  });
  bssl::UniquePtr<BIO> wbio_silent_error(BIO_new(method.get()));
  ASSERT_TRUE(wbio_silent_error);

  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);
  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));

  // Replace the write |BIO| with |wbio_silent_error|.
  SSL_set0_wbio(client.get(), wbio_silent_error.release());

  // Writes should fail. There is nothing in the error queue, so
  // |SSL_ERROR_SYSCALL| indicates the caller needs to check out-of-band.
  const uint8_t data[1] = {0};
  int ret = SSL_write(client.get(), data, sizeof(data));
  EXPECT_EQ(ret, -1);
  EXPECT_EQ(SSL_get_error(client.get(), ret), SSL_ERROR_SYSCALL);
  EXPECT_TRUE(write_failed);
  write_failed = false;

  // Send a close_notify from the server. It should return 0 because
  // close_notify was sent, but not received. Confusingly, this is a success
  // output for |SSL_shutdown|'s API.
  EXPECT_EQ(SSL_shutdown(server.get()), 0);

  // Read the close_notify on the client.
  uint8_t buf[1];
  ret = SSL_read(client.get(), buf, sizeof(buf));
  EXPECT_EQ(ret, 0);
  EXPECT_EQ(SSL_get_error(client.get(), ret), SSL_ERROR_ZERO_RETURN);

  // Further calls to |SSL_read| continue to report |SSL_ERROR_ZERO_RETURN|.
  ret = SSL_read(client.get(), buf, sizeof(buf));
  EXPECT_EQ(ret, 0);
  EXPECT_EQ(SSL_get_error(client.get(), ret), SSL_ERROR_ZERO_RETURN);

  // Although the client has seen close_notify, it should continue to report
  // |SSL_ERROR_SYSCALL| when its writes fail.
  ret = SSL_write(client.get(), data, sizeof(data));
  EXPECT_EQ(ret, -1);
  EXPECT_EQ(SSL_get_error(client.get(), ret), SSL_ERROR_SYSCALL);
  EXPECT_TRUE(write_failed);
  write_failed = false;

  // Cause |BIO_write| to fail with a return value of zero instead.
  // |SSL_get_error| should not misinterpret this as a close_notify.
  //
  // This is not actually a correct implementation of |BIO_write|, but the rest
  // of the code treats zero from |BIO_write| as an error, so ensure it does so
  // correctly. Fixing https://crbug.com/boringssl/503 will make this case moot.
  BIO_meth_set_write(method.get(), [](BIO *, const char *, int) -> int {
    write_failed = true;
    return 0;
  });
  ret = SSL_write(client.get(), data, sizeof(data));
  EXPECT_EQ(ret, 0);
  EXPECT_EQ(SSL_get_error(client.get(), ret), SSL_ERROR_SYSCALL);
  EXPECT_TRUE(write_failed);
  write_failed = false;
}

}  // namespace
BSSL_NAMESPACE_END
