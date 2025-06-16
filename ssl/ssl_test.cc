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



struct HybridHandshakeTest {
  // The curves rule string to apply to the client
  const char *client_rule;
  // TLS version that the client is configured with
  uint16_t client_version;
  // The curves rule string to apply to the server
  const char *server_rule;
  // TLS version that the server is configured with
  uint16_t server_version;
  // The group that is expected to be negotiated
  uint16_t expected_group;
  // Is a HelloRetryRequest expected?
  bool is_hrr_expected;
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

static const HybridHandshakeTest kHybridHandshakeTests[] = {
  // The corresponding hybrid group should be negotiated when client
  // and server support only that group
  {
    "X25519Kyber768Draft00",
    TLS1_3_VERSION,
    "X25519Kyber768Draft00",
    TLS1_3_VERSION,
    SSL_GROUP_X25519_KYBER768_DRAFT00,
    false,
  },

  {
    "SecP256r1Kyber768Draft00",
    TLS1_3_VERSION,
    "SecP256r1Kyber768Draft00",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1_KYBER768_DRAFT00,
    false,
  },

  // The client's preferred hybrid group should be negotiated when also
  // supported by the server, even if the server "prefers"/supports other groups.
  {
    "X25519Kyber768Draft00:x25519",
    TLS1_3_VERSION,
    "x25519:prime256v1:X25519Kyber768Draft00",
    TLS1_3_VERSION,
    SSL_GROUP_X25519_KYBER768_DRAFT00,
    false,
  },

  {
    "X25519Kyber768Draft00:x25519",
    TLS1_3_VERSION,
    "X25519Kyber768Draft00:x25519",
    TLS1_3_VERSION,
    SSL_GROUP_X25519_KYBER768_DRAFT00,
    false,
  },

  {
    "SecP256r1Kyber768Draft00",
    TLS1_3_VERSION,
    "X25519Kyber768Draft00:secp384r1:x25519:SecP256r1Kyber768Draft00",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1_KYBER768_DRAFT00,
    false,
  },

  // The client lists PQ/hybrid groups as both first and second preferences.
  // The key share logic is implemented such that the client will always
  // attempt to send one hybrid key share and one classical key share.
  // Therefore, the client will send key shares [SecP256r1Kyber768Draft00, x25519],
  // skipping X25519Kyber768Draft00, and the server will choose to negotiate
  // x25519 since it is the only mutually supported group.
  {
    "SecP256r1Kyber768Draft00:X25519Kyber768Draft00:x25519",
    TLS1_3_VERSION,
    "secp384r1:x25519",
    TLS1_3_VERSION,
    SSL_GROUP_X25519,
    false,
  },

  // The client will send key shares [x25519, SecP256r1Kyber768Draft00].
  // The server will negotiate SecP256r1Kyber768Draft00 since it is the only
  // mutually supported group.
  {
    "x25519:secp384r1:SecP256r1Kyber768Draft00",
    TLS1_3_VERSION,
    "SecP256r1Kyber768Draft00:prime256v1",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1_KYBER768_DRAFT00,
    false,
  },

  // The client will send key shares [x25519, SecP256r1Kyber768Draft00]. The
  // server will negotiate x25519 since the client listed it as its first
  // preference, even though it supports SecP256r1Kyber768Draft00.
  {
    "x25519:prime256v1:SecP256r1Kyber768Draft00",
    TLS1_3_VERSION,
    "prime256v1:x25519:SecP256r1Kyber768Draft00",
    TLS1_3_VERSION,
    SSL_GROUP_X25519,
    false,
  },

  // The client will send key shares [SecP256r1Kyber768Draft00, x25519].
  // The server will negotiate SecP256r1Kyber768Draft00 since the client listed
  // it as its first preference.
  {
    "SecP256r1Kyber768Draft00:x25519:prime256v1",
    TLS1_3_VERSION,
    "prime256v1:x25519:SecP256r1Kyber768Draft00",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1_KYBER768_DRAFT00,
    false,
  },

  // In the supported_groups extension, the client will indicate its
  // preferences, in order, as [SecP256r1Kyber768Draft00, X25519Kyber768Draft00,
  // x25519, prime256v1]. From those groups, it will send key shares
  // [SecP256r1Kyber768Draft00, x25519]. The server supports, and receives a
  // key share for, x25519. However, when selecting a mutually supported group
  // to negotiate, the server recognizes that the client prefers
  // X25519Kyber768Draft00 over x25519. Since the server also supports
  // X25519Kyber768Draft00, but did not receive a key share for it, it will
  // select it and send an HRR. This ensures that the client's highest
  // preference group will be negotiated, even at the expense of an additional
  // round-trip.
  //
  // In our SSL implementation, this situation is unique to the case where the
  // client supports both ECC and hybrid/PQ. When sending key shares, the
  // client will send at most two key shares in one of the following ways:

  // (a) one ECC key share - if the client supports only ECC;
  // (b) one PQ key share - if the client supports only PQ;
  // (c) one ECC and one PQ key share - if the client supports ECC and PQ.
  //
  // One of the above cases will be true irrespective of how many groups
  // the client supports. If, say, the client supports four ECC groups
  // and zero PQ groups, it will still only send a single ECC share. In cases
  // (a) and (b), either the server supports that group and chooses to
  // negotiate it, or it doesn't support it and sends an HRR. Case (c) is the
  // only case where the server might receive a key share for a mutually
  // supported group, but chooses to respect the client's preference order
  // defined in the supported_groups extension at the expense of an additional
  // round-trip.
  {
    "SecP256r1Kyber768Draft00:X25519Kyber768Draft00:x25519:prime256v1",
    TLS1_3_VERSION,
    "X25519Kyber768Draft00:prime256v1:x25519",
    TLS1_3_VERSION,
    SSL_GROUP_X25519_KYBER768_DRAFT00,
    true,
  },

  // Like the previous case, but the client's prioritization of ECC and PQ
  // is inverted.
  {
    "x25519:prime256v1:SecP256r1Kyber768Draft00:X25519Kyber768Draft00",
    TLS1_3_VERSION,
    "X25519Kyber768Draft00:prime256v1",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1,
    true,
  },

  // The client will send key shares [SecP256r1Kyber768Draft00, x25519]. The
  // server will negotiate X25519Kyber768Draft00 after an HRR.
  {
    "SecP256r1Kyber768Draft00:X25519Kyber768Draft00:x25519:prime256v1",
    TLS1_3_VERSION,
    "X25519Kyber768Draft00:prime256v1",
    TLS1_3_VERSION,
    SSL_GROUP_X25519_KYBER768_DRAFT00,
    true,
  },

  // EC should be negotiated when client prefers EC, or server does not
  // support hybrid
  {
    "X25519Kyber768Draft00:x25519",
    TLS1_3_VERSION,
    "x25519",
    TLS1_3_VERSION,
    SSL_GROUP_X25519,
    false,
  },
  {
    "x25519:SecP256r1Kyber768Draft00",
    TLS1_3_VERSION,
    "x25519",
    TLS1_3_VERSION,
    SSL_GROUP_X25519,
    false,
  },
  {
    "prime256v1:X25519Kyber768Draft00",
    TLS1_3_VERSION,
    "X25519Kyber768Draft00:prime256v1",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1,
    false,
  },
  {
    "prime256v1:x25519:SecP256r1Kyber768Draft00",
    TLS1_3_VERSION,
    "x25519:prime256v1:SecP256r1Kyber768Draft00",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1,
    false,
  },

  // EC should be negotiated, after a HelloRetryRequest, if the server
  // supports only curves for which it did not initially receive a key share
  {
    "X25519Kyber768Draft00:x25519:SecP256r1Kyber768Draft00:prime256v1",
    TLS1_3_VERSION,
    "prime256v1",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1,
    true,
  },
  {
    "X25519Kyber768Draft00:SecP256r1Kyber768Draft00:prime256v1:x25519",
    TLS1_3_VERSION,
    "secp224r1:secp384r1:secp521r1:x25519",
    TLS1_3_VERSION,
    SSL_GROUP_X25519,
    true,
  },

  // Hybrid should be negotiated, after a HelloRetryRequest, if the server
  // supports only curves for which it did not initially receive a key share
  {
    "x25519:prime256v1:SecP256r1Kyber768Draft00:X25519Kyber768Draft00",
    TLS1_3_VERSION,
    "secp224r1:X25519Kyber768Draft00:secp521r1",
    TLS1_3_VERSION,
    SSL_GROUP_X25519_KYBER768_DRAFT00,
    true,
  },
  {
    "X25519Kyber768Draft00:x25519:prime256v1:SecP256r1Kyber768Draft00",
    TLS1_3_VERSION,
    "SecP256r1Kyber768Draft00",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1_KYBER768_DRAFT00,
    true,
  },

  // If there is no overlap between client and server groups,
  // the handshake should fail
  {
    "SecP256r1Kyber768Draft00:X25519Kyber768Draft00:secp384r1",
    TLS1_3_VERSION,
    "prime256v1:x25519",
    TLS1_3_VERSION,
    0,
    false,
  },
  {
    "secp384r1:SecP256r1Kyber768Draft00:X25519Kyber768Draft00",
    TLS1_3_VERSION,
    "prime256v1:x25519",
    TLS1_3_VERSION,
    0,
    false,
  },
  {
    "secp384r1:SecP256r1Kyber768Draft00",
    TLS1_3_VERSION,
    "prime256v1:x25519:X25519Kyber768Draft00",
    TLS1_3_VERSION,
    0,
    false,
  },
  {
    "SecP256r1Kyber768Draft00",
    TLS1_3_VERSION,
    "X25519Kyber768Draft00",
    TLS1_3_VERSION,
    0,
    false,
  },

  // If the client supports hybrid TLS 1.3, but the server
  // only supports TLS 1.2, then TLS 1.2 EC should be negotiated.
  {
    "SecP256r1Kyber768Draft00:prime256v1",
    TLS1_3_VERSION,
    "prime256v1:x25519",
    TLS1_2_VERSION,
    SSL_GROUP_SECP256R1,
    false,
  },

  // Same as above, but server also has SecP256r1Kyber768Draft00 in it's
  // supported list, but can't use it since TLS 1.3 is the minimum version that
  // supports PQ.
  {
    "SecP256r1Kyber768Draft00:prime256v1",
    TLS1_3_VERSION,
    "SecP256r1Kyber768Draft00:prime256v1:x25519",
    TLS1_2_VERSION,
    SSL_GROUP_SECP256R1,
    false,
  },

  // If the client configures the curve list to include a hybrid
  // curve, then initiates a 1.2 handshake, it will not advertise
  // hybrid groups because hybrid is not supported for 1.2. So
  // a 1.2 EC handshake will be negotiated (even if the server
  // supports 1.3 with corresponding hybrid group).
  {
    "SecP256r1Kyber768Draft00:x25519",
    TLS1_2_VERSION,
    "SecP256r1Kyber768Draft00:x25519",
    TLS1_3_VERSION,
    SSL_GROUP_X25519,
    false,
  },
  {
    "SecP256r1Kyber768Draft00:prime256v1",
    TLS1_2_VERSION,
    "prime256v1:x25519",
    TLS1_2_VERSION,
    SSL_GROUP_SECP256R1,
    false,
  },
  // The corresponding hybrid group should be negotiated when client
  // and server support only that group
  {
    "X25519MLKEM768",
    TLS1_3_VERSION,
    "X25519MLKEM768",
    TLS1_3_VERSION,
    SSL_GROUP_X25519_MLKEM768,
    false,
  },

  {
    "SecP256r1MLKEM768",
    TLS1_3_VERSION,
    "SecP256r1MLKEM768",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1_MLKEM768,
    false,
  },

  {
    "SecP384r1MLKEM1024",
    TLS1_3_VERSION,
    "SecP384r1MLKEM1024",
    TLS1_3_VERSION,
    SSL_GROUP_SECP384R1_MLKEM1024,
    false,
  },

  // The client's preferred hybrid group should be negotiated when also
  // supported by the server, even if the server "prefers"/supports other groups.
  {
    "X25519MLKEM768:x25519",
    TLS1_3_VERSION,
    "x25519:prime256v1:X25519MLKEM768",
    TLS1_3_VERSION,
    SSL_GROUP_X25519_MLKEM768,
    false,
  },

  {
    "X25519MLKEM768:x25519",
    TLS1_3_VERSION,
    "X25519MLKEM768:x25519",
    TLS1_3_VERSION,
    SSL_GROUP_X25519_MLKEM768,
    false,
  },

  {
    "SecP256r1MLKEM768",
    TLS1_3_VERSION,
    "X25519MLKEM768:secp384r1:x25519:SecP256r1MLKEM768",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1_MLKEM768,
    false,
  },

  {
    "X25519MLKEM768:SecP256r1MLKEM768:SecP384r1MLKEM1024",
    TLS1_3_VERSION,
    "SecP384r1MLKEM1024:SecP256r1MLKEM768:X25519MLKEM768",
    TLS1_3_VERSION,
    SSL_GROUP_X25519_MLKEM768,
    false,
  },

  {
    "SecP384r1MLKEM1024:SecP256r1MLKEM768:X25519MLKEM768",
    TLS1_3_VERSION,
    "X25519MLKEM768:SecP256r1MLKEM768:SecP384r1MLKEM1024",
    TLS1_3_VERSION,
    SSL_GROUP_SECP384R1_MLKEM1024,
    false,
  },

  // The client lists PQ/hybrid groups as both first and second preferences.
  // The key share logic is implemented such that the client will always
  // attempt to send one hybrid key share and one classical key share.
  // Therefore, the client will send key shares [SecP256r1MLKEM768, x25519],
  // skipping X25519MLKEM768, and the server will choose to negotiate
  // x25519 since it is the only mutually supported group.
  {
    "SecP256r1MLKEM768:X25519MLKEM768:x25519",
    TLS1_3_VERSION,
    "secp384r1:x25519",
    TLS1_3_VERSION,
    SSL_GROUP_X25519,
    false,
  },

  // The client will send key shares [x25519, SecP256r1MLKEM768].
  // The server will negotiate SecP256r1MLKEM768 since it is the only
  // mutually supported group.
  {
    "x25519:secp384r1:SecP256r1MLKEM768",
    TLS1_3_VERSION,
    "SecP256r1MLKEM768:prime256v1",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1_MLKEM768,
    false,
  },

  // The client will send key shares [x25519, SecP256r1MLKEM768]. The
  // server will negotiate x25519 since the client listed it as its first
  // preference, even though it supports SecP256r1MLKEM768.
  {
    "x25519:prime256v1:SecP256r1MLKEM768",
    TLS1_3_VERSION,
    "prime256v1:x25519:SecP256r1MLKEM768",
    TLS1_3_VERSION,
    SSL_GROUP_X25519,
    false,
  },

  // The client will send key shares [SecP256r1MLKEM768, x25519].
  // The server will negotiate SecP256r1MLKEM768 since the client listed
  // it as its first preference.
  {
    "SecP256r1MLKEM768:x25519:prime256v1",
    TLS1_3_VERSION,
    "prime256v1:x25519:SecP256r1MLKEM768",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1_MLKEM768,
    false,
  },

  // In the supported_groups extension, the client will indicate its
  // preferences, in order, as [SecP256r1MLKEM768, X25519MLKEM768,
  // x25519, prime256v1]. From those groups, it will send key shares
  // [SecP256r1MLKEM768, x25519]. The server supports, and receives a
  // key share for, x25519. However, when selecting a mutually supported group
  // to negotiate, the server recognizes that the client prefers
  // X25519MLKEM768 over x25519. Since the server also supports
  // X25519MLKEM768, but did not receive a key share for it, it will
  // select it and send an HRR. This ensures that the client's highest
  // preference group will be negotiated, even at the expense of an additional
  // round-trip.
  //
  // In our SSL implementation, this situation is unique to the case where the
  // client supports both ECC and hybrid/PQ. When sending key shares, the
  // client will send at most two key shares in one of the following ways:

  // (a) one ECC key share - if the client supports only ECC;
  // (b) one PQ key share - if the client supports only PQ;
  // (c) one ECC and one PQ key share - if the client supports ECC and PQ.
  //
  // One of the above cases will be true irrespective of how many groups
  // the client supports. If, say, the client supports four ECC groups
  // and zero PQ groups, it will still only send a single ECC share. In cases
  // (a) and (b), either the server supports that group and chooses to
  // negotiate it, or it doesn't support it and sends an HRR. Case (c) is the
  // only case where the server might receive a key share for a mutually
  // supported group, but chooses to respect the client's preference order
  // defined in the supported_groups extension at the expense of an additional
  // round-trip.
  {
    "SecP256r1MLKEM768:X25519MLKEM768:x25519:prime256v1",
    TLS1_3_VERSION,
    "X25519MLKEM768:prime256v1:x25519",
    TLS1_3_VERSION,
    SSL_GROUP_X25519_MLKEM768,
    true,
  },

  // Like the previous case, but the client's prioritization of ECC and PQ
  // is inverted.
  {
    "x25519:prime256v1:SecP256r1MLKEM768:X25519MLKEM768",
    TLS1_3_VERSION,
    "X25519MLKEM768:prime256v1",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1,
    true,
  },

  // The client will send key shares [SecP256r1MLKEM768, x25519]. The
  // server will negotiate X25519MLKEM768 after an HRR.
  {
    "SecP256r1MLKEM768:X25519MLKEM768:x25519:prime256v1",
    TLS1_3_VERSION,
    "X25519MLKEM768:prime256v1",
    TLS1_3_VERSION,
    SSL_GROUP_X25519_MLKEM768,
    true,
  },

  // EC should be negotiated when client prefers EC, or server does not
  // support hybrid
  {
    "X25519MLKEM768:x25519",
    TLS1_3_VERSION,
    "x25519",
    TLS1_3_VERSION,
    SSL_GROUP_X25519,
    false,
  },
  {
    "x25519:SecP256r1MLKEM768",
    TLS1_3_VERSION,
    "x25519",
    TLS1_3_VERSION,
    SSL_GROUP_X25519,
    false,
  },
  {
    "prime256v1:X25519MLKEM768",
    TLS1_3_VERSION,
    "X25519MLKEM768:prime256v1",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1,
    false,
  },
  {
    "prime256v1:x25519:SecP256r1MLKEM768",
    TLS1_3_VERSION,
    "x25519:prime256v1:SecP256r1MLKEM768",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1,
    false,
  },

  // EC should be negotiated, after a HelloRetryRequest, if the server
  // supports only curves for which it did not initially receive a key share
  {
    "X25519MLKEM768:x25519:SecP256r1MLKEM768:prime256v1",
    TLS1_3_VERSION,
    "prime256v1",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1,
    true,
  },
  {
    "X25519MLKEM768:SecP256r1MLKEM768:prime256v1:x25519",
    TLS1_3_VERSION,
    "secp224r1:secp384r1:secp521r1:x25519",
    TLS1_3_VERSION,
    SSL_GROUP_X25519,
    true,
  },

  // Hybrid should be negotiated, after a HelloRetryRequest, if the server
  // supports only curves for which it did not initially receive a key share
  {
    "x25519:prime256v1:SecP256r1MLKEM768:X25519MLKEM768",
    TLS1_3_VERSION,
    "secp224r1:X25519MLKEM768:secp521r1",
    TLS1_3_VERSION,
    SSL_GROUP_X25519_MLKEM768,
    true,
  },
  {
    "X25519MLKEM768:x25519:prime256v1:SecP256r1MLKEM768",
    TLS1_3_VERSION,
    "SecP256r1MLKEM768",
    TLS1_3_VERSION,
    SSL_GROUP_SECP256R1_MLKEM768,
    true,
  },

  // If there is no overlap between client and server groups,
  // the handshake should fail
  {
    "SecP256r1MLKEM768:X25519MLKEM768:secp384r1",
    TLS1_3_VERSION,
    "prime256v1:x25519",
    TLS1_3_VERSION,
    0,
    false,
  },
  {
    "secp384r1:SecP256r1MLKEM768:X25519MLKEM768",
    TLS1_3_VERSION,
    "prime256v1:x25519",
    TLS1_3_VERSION,
    0,
    false,
  },
  {
    "secp384r1:SecP256r1MLKEM768",
    TLS1_3_VERSION,
    "prime256v1:x25519:X25519MLKEM768",
    TLS1_3_VERSION,
    0,
    false,
  },
  {
    "SecP256r1MLKEM768",
    TLS1_3_VERSION,
    "X25519MLKEM768",
    TLS1_3_VERSION,
    0,
    false,
  },

  // If the client supports hybrid TLS 1.3, but the server
  // only supports TLS 1.2, then TLS 1.2 EC should be negotiated.
  {
    "SecP256r1MLKEM768:prime256v1",
    TLS1_3_VERSION,
    "prime256v1:x25519",
    TLS1_2_VERSION,
    SSL_GROUP_SECP256R1,
    false,
  },

  // Same as above, but server also has SecP256r1MLKEM768 in it's
  // supported list, but can't use it since TLS 1.3 is the minimum version that
  // supports PQ.
  {
    "SecP256r1MLKEM768:prime256v1",
    TLS1_3_VERSION,
    "SecP256r1MLKEM768:prime256v1:x25519",
    TLS1_2_VERSION,
    SSL_GROUP_SECP256R1,
    false,
  },

  // If the client configures the curve list to include a hybrid
  // curve, then initiates a 1.2 handshake, it will not advertise
  // hybrid groups because hybrid is not supported for 1.2. So
  // a 1.2 EC handshake will be negotiated (even if the server
  // supports 1.3 with corresponding hybrid group).
  {
    "SecP256r1MLKEM768:x25519",
    TLS1_2_VERSION,
    "SecP256r1MLKEM768:x25519",
    TLS1_3_VERSION,
    SSL_GROUP_X25519,
    false,
  },
  {
    "SecP256r1MLKEM768:prime256v1",
    TLS1_2_VERSION,
    "prime256v1:x25519",
    TLS1_2_VERSION,
    SSL_GROUP_SECP256R1,
    false,
  },
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

// kOpenSSLSession is a serialized SSL_SESSION.
static const char kOpenSSLSession[] =
    "MIIFqgIBAQICAwMEAsAvBCAG5Q1ndq4Yfmbeo1zwLkNRKmCXGdNgWvGT3cskV0yQ"
    "kAQwJlrlzkAWBOWiLj/jJ76D7l+UXoizP2KI2C7I2FccqMmIfFmmkUy32nIJ0mZH"
    "IWoJoQYCBFRDO46iBAICASyjggR6MIIEdjCCA16gAwIBAgIIK9dUvsPWSlUwDQYJ"
    "KoZIhvcNAQEFBQAwSTELMAkGA1UEBhMCVVMxEzARBgNVBAoTCkdvb2dsZSBJbmMx"
    "JTAjBgNVBAMTHEdvb2dsZSBJbnRlcm5ldCBBdXRob3JpdHkgRzIwHhcNMTQxMDA4"
    "MTIwNzU3WhcNMTUwMTA2MDAwMDAwWjBoMQswCQYDVQQGEwJVUzETMBEGA1UECAwK"
    "Q2FsaWZvcm5pYTEWMBQGA1UEBwwNTW91bnRhaW4gVmlldzETMBEGA1UECgwKR29v"
    "Z2xlIEluYzEXMBUGA1UEAwwOd3d3Lmdvb2dsZS5jb20wggEiMA0GCSqGSIb3DQEB"
    "AQUAA4IBDwAwggEKAoIBAQCcKeLrplAC+Lofy8t/wDwtB6eu72CVp0cJ4V3lknN6"
    "huH9ct6FFk70oRIh/VBNBBz900jYy+7111Jm1b8iqOTQ9aT5C7SEhNcQFJvqzH3e"
    "MPkb6ZSWGm1yGF7MCQTGQXF20Sk/O16FSjAynU/b3oJmOctcycWYkY0ytS/k3LBu"
    "Id45PJaoMqjB0WypqvNeJHC3q5JjCB4RP7Nfx5jjHSrCMhw8lUMW4EaDxjaR9KDh"
    "PLgjsk+LDIySRSRDaCQGhEOWLJZVLzLo4N6/UlctCHEllpBUSvEOyFga52qroGjg"
    "rf3WOQ925MFwzd6AK+Ich0gDRg8sQfdLH5OuP1cfLfU1AgMBAAGjggFBMIIBPTAd"
    "BgNVHSUEFjAUBggrBgEFBQcDAQYIKwYBBQUHAwIwGQYDVR0RBBIwEIIOd3d3Lmdv"
    "b2dsZS5jb20waAYIKwYBBQUHAQEEXDBaMCsGCCsGAQUFBzAChh9odHRwOi8vcGtp"
    "Lmdvb2dsZS5jb20vR0lBRzIuY3J0MCsGCCsGAQUFBzABhh9odHRwOi8vY2xpZW50"
    "czEuZ29vZ2xlLmNvbS9vY3NwMB0GA1UdDgQWBBQ7a+CcxsZByOpc+xpYFcIbnUMZ"
    "hTAMBgNVHRMBAf8EAjAAMB8GA1UdIwQYMBaAFErdBhYbvPZotXb1gba7Yhq6WoEv"
    "MBcGA1UdIAQQMA4wDAYKKwYBBAHWeQIFATAwBgNVHR8EKTAnMCWgI6Ahhh9odHRw"
    "Oi8vcGtpLmdvb2dsZS5jb20vR0lBRzIuY3JsMA0GCSqGSIb3DQEBBQUAA4IBAQCa"
    "OXCBdoqUy5bxyq+Wrh1zsyyCFim1PH5VU2+yvDSWrgDY8ibRGJmfff3r4Lud5kal"
    "dKs9k8YlKD3ITG7P0YT/Rk8hLgfEuLcq5cc0xqmE42xJ+Eo2uzq9rYorc5emMCxf"
    "5L0TJOXZqHQpOEcuptZQ4OjdYMfSxk5UzueUhA3ogZKRcRkdB3WeWRp+nYRhx4St"
    "o2rt2A0MKmY9165GHUqMK9YaaXHDXqBu7Sefr1uSoAP9gyIJKeihMivsGqJ1TD6Z"
    "cc6LMe+dN2P8cZEQHtD1y296ul4Mivqk3jatUVL8/hCwgch9A8O4PGZq9WqBfEWm"
    "IyHh1dPtbg1lOXdYCWtjpAIEAKUDAgEUqQUCAwGJwKqBpwSBpBwUQvoeOk0Kg36S"
    "YTcLEkXqKwOBfF9vE4KX0NxeLwjcDTpsuh3qXEaZ992r1N38VDcyS6P7I6HBYN9B"
    "sNHM362zZnY27GpTw+Kwd751CLoXFPoaMOe57dbBpXoro6Pd3BTbf/Tzr88K06yE"
    "OTDKPNj3+inbMaVigtK4PLyPq+Topyzvx9USFgRvyuoxn0Hgb+R0A3j6SLRuyOdA"
    "i4gv7Y5oliyntgMBAQA=";

// kCustomSession is a custom serialized SSL_SESSION generated by
// filling in missing fields from |kOpenSSLSession|. This includes
// providing |peer_sha256|, so |peer| is not serialized.
static const char kCustomSession[] =
    "MIIBZAIBAQICAwMEAsAvBCAG5Q1ndq4Yfmbeo1zwLkNRKmCXGdNgWvGT3cskV0yQ"
    "kAQwJlrlzkAWBOWiLj/jJ76D7l+UXoizP2KI2C7I2FccqMmIfFmmkUy32nIJ0mZH"
    "IWoJoQYCBFRDO46iBAICASykAwQBAqUDAgEUqAcEBXdvcmxkqQUCAwGJwKqBpwSB"
    "pBwUQvoeOk0Kg36SYTcLEkXqKwOBfF9vE4KX0NxeLwjcDTpsuh3qXEaZ992r1N38"
    "VDcyS6P7I6HBYN9BsNHM362zZnY27GpTw+Kwd751CLoXFPoaMOe57dbBpXoro6Pd"
    "3BTbf/Tzr88K06yEOTDKPNj3+inbMaVigtK4PLyPq+Topyzvx9USFgRvyuoxn0Hg"
    "b+R0A3j6SLRuyOdAi4gv7Y5oliynrSIEIAYGBgYGBgYGBgYGBgYGBgYGBgYGBgYG"
    "BgYGBgYGBgYGrgMEAQevAwQBBLADBAEF";

// kBoringSSLSession is a serialized SSL_SESSION generated from bssl client.
static const char kBoringSSLSession[] =
    "MIIRwQIBAQICAwMEAsAvBCDdoGxGK26mR+8lM0uq6+k9xYuxPnwAjpcF9n0Yli9R"
    "kQQwbyshfWhdi5XQ1++7n2L1qqrcVlmHBPpr6yknT/u4pUrpQB5FZ7vqvNn8MdHf"
    "9rWgoQYCBFXgs7uiBAICHCCjggR6MIIEdjCCA16gAwIBAgIIf+yfD7Y6UicwDQYJ"
    "KoZIhvcNAQELBQAwSTELMAkGA1UEBhMCVVMxEzARBgNVBAoTCkdvb2dsZSBJbmMx"
    "JTAjBgNVBAMTHEdvb2dsZSBJbnRlcm5ldCBBdXRob3JpdHkgRzIwHhcNMTUwODEy"
    "MTQ1MzE1WhcNMTUxMTEwMDAwMDAwWjBoMQswCQYDVQQGEwJVUzETMBEGA1UECAwK"
    "Q2FsaWZvcm5pYTEWMBQGA1UEBwwNTW91bnRhaW4gVmlldzETMBEGA1UECgwKR29v"
    "Z2xlIEluYzEXMBUGA1UEAwwOd3d3Lmdvb2dsZS5jb20wggEiMA0GCSqGSIb3DQEB"
    "AQUAA4IBDwAwggEKAoIBAQC0MeG5YGQ0t+IeJeoneP/PrhEaieibeKYkbKVLNZpo"
    "PLuBinvhkXZo3DC133NpCBpy6ZktBwamqyixAyuk/NU6OjgXqwwxfQ7di1AInLIU"
    "792c7hFyNXSUCG7At8Ifi3YwBX9Ba6u/1d6rWTGZJrdCq3QU11RkKYyTq2KT5mce"
    "Tv9iGKqSkSTlp8puy/9SZ/3DbU3U+BuqCFqeSlz7zjwFmk35acdCilpJlVDDN5C/"
    "RCh8/UKc8PaL+cxlt531qoTENvYrflBno14YEZlCBZsPiFeUSILpKEj3Ccwhy0eL"
    "EucWQ72YZU8mUzXBoXGn0zA0crFl5ci/2sTBBGZsylNBAgMBAAGjggFBMIIBPTAd"
    "BgNVHSUEFjAUBggrBgEFBQcDAQYIKwYBBQUHAwIwGQYDVR0RBBIwEIIOd3d3Lmdv"
    "b2dsZS5jb20waAYIKwYBBQUHAQEEXDBaMCsGCCsGAQUFBzAChh9odHRwOi8vcGtp"
    "Lmdvb2dsZS5jb20vR0lBRzIuY3J0MCsGCCsGAQUFBzABhh9odHRwOi8vY2xpZW50"
    "czEuZ29vZ2xlLmNvbS9vY3NwMB0GA1UdDgQWBBS/bzHxcE73Q4j3slC4BLbMtLjG"
    "GjAMBgNVHRMBAf8EAjAAMB8GA1UdIwQYMBaAFErdBhYbvPZotXb1gba7Yhq6WoEv"
    "MBcGA1UdIAQQMA4wDAYKKwYBBAHWeQIFATAwBgNVHR8EKTAnMCWgI6Ahhh9odHRw"
    "Oi8vcGtpLmdvb2dsZS5jb20vR0lBRzIuY3JsMA0GCSqGSIb3DQEBCwUAA4IBAQAb"
    "qdWPZEHk0X7iKPCTHL6S3w6q1eR67goxZGFSM1lk1hjwyu7XcLJuvALVV9uY3ovE"
    "kQZSHwT+pyOPWQhsSjO+1GyjvCvK/CAwiUmBX+bQRGaqHsRcio7xSbdVcajQ3bXd"
    "X+s0WdbOpn6MStKAiBVloPlSxEI8pxY6x/BBCnTIk/+DMB17uZlOjG3vbAnkDkP+"
    "n0OTucD9sHV7EVj9XUxi51nOfNBCN/s7lpUjDS/NJ4k3iwOtbCPswiot8vLO779a"
    "f07vR03r349Iz/KTzk95rlFtX0IU+KYNxFNsanIXZ+C9FYGRXkwhHcvFb4qMUB1y"
    "TTlM80jBMOwyjZXmjRAhpAIEAKUDAgEUqQUCAwGJwKqBpwSBpOgebbmn9NRUtMWH"
    "+eJpqA5JLMFSMCChOsvKey3toBaCNGU7HfAEiiXNuuAdCBoK262BjQc2YYfqFzqH"
    "zuppopXCvhohx7j/tnCNZIMgLYt/O9SXK2RYI5z8FhCCHvB4CbD5G0LGl5EFP27s"
    "Jb6S3aTTYPkQe8yZSlxevg6NDwmTogLO9F7UUkaYmVcMQhzssEE2ZRYNwSOU6KjE"
    "0Yj+8fAiBtbQriIEIN2L8ZlpaVrdN5KFNdvcmOxJu81P8q53X55xQyGTnGWwsgMC"
    "ARezggvvMIIEdjCCA16gAwIBAgIIf+yfD7Y6UicwDQYJKoZIhvcNAQELBQAwSTEL"
    "MAkGA1UEBhMCVVMxEzARBgNVBAoTCkdvb2dsZSBJbmMxJTAjBgNVBAMTHEdvb2ds"
    "ZSBJbnRlcm5ldCBBdXRob3JpdHkgRzIwHhcNMTUwODEyMTQ1MzE1WhcNMTUxMTEw"
    "MDAwMDAwWjBoMQswCQYDVQQGEwJVUzETMBEGA1UECAwKQ2FsaWZvcm5pYTEWMBQG"
    "A1UEBwwNTW91bnRhaW4gVmlldzETMBEGA1UECgwKR29vZ2xlIEluYzEXMBUGA1UE"
    "AwwOd3d3Lmdvb2dsZS5jb20wggEiMA0GCSqGSIb3DQEBAQUAA4IBDwAwggEKAoIB"
    "AQC0MeG5YGQ0t+IeJeoneP/PrhEaieibeKYkbKVLNZpoPLuBinvhkXZo3DC133Np"
    "CBpy6ZktBwamqyixAyuk/NU6OjgXqwwxfQ7di1AInLIU792c7hFyNXSUCG7At8If"
    "i3YwBX9Ba6u/1d6rWTGZJrdCq3QU11RkKYyTq2KT5mceTv9iGKqSkSTlp8puy/9S"
    "Z/3DbU3U+BuqCFqeSlz7zjwFmk35acdCilpJlVDDN5C/RCh8/UKc8PaL+cxlt531"
    "qoTENvYrflBno14YEZlCBZsPiFeUSILpKEj3Ccwhy0eLEucWQ72YZU8mUzXBoXGn"
    "0zA0crFl5ci/2sTBBGZsylNBAgMBAAGjggFBMIIBPTAdBgNVHSUEFjAUBggrBgEF"
    "BQcDAQYIKwYBBQUHAwIwGQYDVR0RBBIwEIIOd3d3Lmdvb2dsZS5jb20waAYIKwYB"
    "BQUHAQEEXDBaMCsGCCsGAQUFBzAChh9odHRwOi8vcGtpLmdvb2dsZS5jb20vR0lB"
    "RzIuY3J0MCsGCCsGAQUFBzABhh9odHRwOi8vY2xpZW50czEuZ29vZ2xlLmNvbS9v"
    "Y3NwMB0GA1UdDgQWBBS/bzHxcE73Q4j3slC4BLbMtLjGGjAMBgNVHRMBAf8EAjAA"
    "MB8GA1UdIwQYMBaAFErdBhYbvPZotXb1gba7Yhq6WoEvMBcGA1UdIAQQMA4wDAYK"
    "KwYBBAHWeQIFATAwBgNVHR8EKTAnMCWgI6Ahhh9odHRwOi8vcGtpLmdvb2dsZS5j"
    "b20vR0lBRzIuY3JsMA0GCSqGSIb3DQEBCwUAA4IBAQAbqdWPZEHk0X7iKPCTHL6S"
    "3w6q1eR67goxZGFSM1lk1hjwyu7XcLJuvALVV9uY3ovEkQZSHwT+pyOPWQhsSjO+"
    "1GyjvCvK/CAwiUmBX+bQRGaqHsRcio7xSbdVcajQ3bXdX+s0WdbOpn6MStKAiBVl"
    "oPlSxEI8pxY6x/BBCnTIk/+DMB17uZlOjG3vbAnkDkP+n0OTucD9sHV7EVj9XUxi"
    "51nOfNBCN/s7lpUjDS/NJ4k3iwOtbCPswiot8vLO779af07vR03r349Iz/KTzk95"
    "rlFtX0IU+KYNxFNsanIXZ+C9FYGRXkwhHcvFb4qMUB1yTTlM80jBMOwyjZXmjRAh"
    "MIID8DCCAtigAwIBAgIDAjqDMA0GCSqGSIb3DQEBCwUAMEIxCzAJBgNVBAYTAlVT"
    "MRYwFAYDVQQKEw1HZW9UcnVzdCBJbmMuMRswGQYDVQQDExJHZW9UcnVzdCBHbG9i"
    "YWwgQ0EwHhcNMTMwNDA1MTUxNTU2WhcNMTYxMjMxMjM1OTU5WjBJMQswCQYDVQQG"
    "EwJVUzETMBEGA1UEChMKR29vZ2xlIEluYzElMCMGA1UEAxMcR29vZ2xlIEludGVy"
    "bmV0IEF1dGhvcml0eSBHMjCCASIwDQYJKoZIhvcNAQEBBQADggEPADCCAQoCggEB"
    "AJwqBHdc2FCROgajguDYUEi8iT/xGXAaiEZ+4I/F8YnOIe5a/mENtzJEiaB0C1NP"
    "VaTOgmKV7utZX8bhBYASxF6UP7xbSDj0U/ck5vuR6RXEz/RTDfRK/J9U3n2+oGtv"
    "h8DQUB8oMANA2ghzUWx//zo8pzcGjr1LEQTrfSTe5vn8MXH7lNVg8y5Kr0LSy+rE"
    "ahqyzFPdFUuLH8gZYR/Nnag+YyuENWllhMgZxUYi+FOVvuOAShDGKuy6lyARxzmZ"
    "EASg8GF6lSWMTlJ14rbtCMoU/M4iarNOz0YDl5cDfsCx3nuvRTPPuj5xt970JSXC"
    "DTWJnZ37DhF5iR43xa+OcmkCAwEAAaOB5zCB5DAfBgNVHSMEGDAWgBTAephojYn7"
    "qwVkDBF9qn1luMrMTjAdBgNVHQ4EFgQUSt0GFhu89mi1dvWBtrtiGrpagS8wDgYD"
    "VR0PAQH/BAQDAgEGMC4GCCsGAQUFBwEBBCIwIDAeBggrBgEFBQcwAYYSaHR0cDov"
    "L2cuc3ltY2QuY29tMBIGA1UdEwEB/wQIMAYBAf8CAQAwNQYDVR0fBC4wLDAqoCig"
    "JoYkaHR0cDovL2cuc3ltY2IuY29tL2NybHMvZ3RnbG9iYWwuY3JsMBcGA1UdIAQQ"
    "MA4wDAYKKwYBBAHWeQIFATANBgkqhkiG9w0BAQsFAAOCAQEAqvqpIM1qZ4PtXtR+"
    "3h3Ef+AlBgDFJPupyC1tft6dgmUsgWM0Zj7pUsIItMsv91+ZOmqcUHqFBYx90SpI"
    "hNMJbHzCzTWf84LuUt5oX+QAihcglvcpjZpNy6jehsgNb1aHA30DP9z6eX0hGfnI"
    "Oi9RdozHQZJxjyXON/hKTAAj78Q1EK7gI4BzfE00LshukNYQHpmEcxpw8u1VDu4X"
    "Bupn7jLrLN1nBz/2i8Jw3lsA5rsb0zYaImxssDVCbJAJPZPpZAkiDoUGn8JzIdPm"
    "X4DkjYUiOnMDsWCOrmji9D6X52ASCWg23jrW4kOVWzeBkoEfu43XrVJkFleW2V40"
    "fsg12DCCA30wggLmoAMCAQICAxK75jANBgkqhkiG9w0BAQUFADBOMQswCQYDVQQG"
    "EwJVUzEQMA4GA1UEChMHRXF1aWZheDEtMCsGA1UECxMkRXF1aWZheCBTZWN1cmUg"
    "Q2VydGlmaWNhdGUgQXV0aG9yaXR5MB4XDTAyMDUyMTA0MDAwMFoXDTE4MDgyMTA0"
    "MDAwMFowQjELMAkGA1UEBhMCVVMxFjAUBgNVBAoTDUdlb1RydXN0IEluYy4xGzAZ"
    "BgNVBAMTEkdlb1RydXN0IEdsb2JhbCBDQTCCASIwDQYJKoZIhvcNAQEBBQADggEP"
    "ADCCAQoCggEBANrMGGMw/fQXIxpWflvfPGw45HG3eJHUvKHYTPioQ7YD6U0hBwiI"
    "2lgvZjkpvQV4i5046AW3an5xpObEYKaw74DkiSgPniXW7YPzraaRx5jJQhg1FJ2t"
    "mEaSLk/K8YdDwRaVVy1Q74ktgHpXrfLuX2vSAI25FPgUFTXZwEaje3LIkb/JVSvN"
    "0Jc+nCZkzN/Ogxlxyk7m1NV7qRnNVd7I7NJeOFPlXE+MLf5QIzb8ZubLjqQ5GQC3"
    "lQI5kQsO/jgu0R0FmvZNPm8PBx2vLB6PYDni+jZTEznUXiYr2z2oFL0y6xgDKFIE"
    "ceWrMz3hOLsHNoRinHnqFjD0X8Ar6HFr5PkCAwEAAaOB8DCB7TAfBgNVHSMEGDAW"
    "gBRI5mj5K9KylddH2CMgEE8zmJCf1DAdBgNVHQ4EFgQUwHqYaI2J+6sFZAwRfap9"
    "ZbjKzE4wDwYDVR0TAQH/BAUwAwEB/zAOBgNVHQ8BAf8EBAMCAQYwOgYDVR0fBDMw"
    "MTAvoC2gK4YpaHR0cDovL2NybC5nZW90cnVzdC5jb20vY3Jscy9zZWN1cmVjYS5j"
    "cmwwTgYDVR0gBEcwRTBDBgRVHSAAMDswOQYIKwYBBQUHAgEWLWh0dHBzOi8vd3d3"
    "Lmdlb3RydXN0LmNvbS9yZXNvdXJjZXMvcmVwb3NpdG9yeTANBgkqhkiG9w0BAQUF"
    "AAOBgQB24RJuTksWEoYwBrKBCM/wCMfHcX5m7sLt1Dsf//DwyE7WQziwuTB9GNBV"
    "g6JqyzYRnOhIZqNtf7gT1Ef+i1pcc/yu2RsyGTirlzQUqpbS66McFAhJtrvlke+D"
    "NusdVm/K2rxzY5Dkf3s+Iss9B+1fOHSc4wNQTqGvmO5h8oQ/Eg==";

// kBadSessionExtraField is a custom serialized SSL_SESSION generated by
// replacing the final (optional) element of |kCustomSession| with tag
// number 99.
static const char kBadSessionExtraField[] =
    "MIIBdgIBAQICAwMEAsAvBCAG5Q1ndq4Yfmbeo1zwLkNRKmCXGdNgWvGT3cskV0yQ"
    "kAQwJlrlzkAWBOWiLj/jJ76D7l+UXoizP2KI2C7I2FccqMmIfFmmkUy32nIJ0mZH"
    "IWoJoQYCBFRDO46iBAICASykAwQBAqUDAgEUphAEDnd3dy5nb29nbGUuY29tqAcE"
    "BXdvcmxkqQUCAwGJwKqBpwSBpBwUQvoeOk0Kg36SYTcLEkXqKwOBfF9vE4KX0Nxe"
    "LwjcDTpsuh3qXEaZ992r1N38VDcyS6P7I6HBYN9BsNHM362zZnY27GpTw+Kwd751"
    "CLoXFPoaMOe57dbBpXoro6Pd3BTbf/Tzr88K06yEOTDKPNj3+inbMaVigtK4PLyP"
    "q+Topyzvx9USFgRvyuoxn0Hgb+R0A3j6SLRuyOdAi4gv7Y5oliynrSIEIAYGBgYG"
    "BgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGrgMEAQevAwQBBOMDBAEF";

// kBadSessionVersion is a custom serialized SSL_SESSION generated by replacing
// the version of |kCustomSession| with 2.
static const char kBadSessionVersion[] =
    "MIIBdgIBAgICAwMEAsAvBCAG5Q1ndq4Yfmbeo1zwLkNRKmCXGdNgWvGT3cskV0yQ"
    "kAQwJlrlzkAWBOWiLj/jJ76D7l+UXoizP2KI2C7I2FccqMmIfFmmkUy32nIJ0mZH"
    "IWoJoQYCBFRDO46iBAICASykAwQBAqUDAgEUphAEDnd3dy5nb29nbGUuY29tqAcE"
    "BXdvcmxkqQUCAwGJwKqBpwSBpBwUQvoeOk0Kg36SYTcLEkXqKwOBfF9vE4KX0Nxe"
    "LwjcDTpsuh3qXEaZ992r1N38VDcyS6P7I6HBYN9BsNHM362zZnY27GpTw+Kwd751"
    "CLoXFPoaMOe57dbBpXoro6Pd3BTbf/Tzr88K06yEOTDKPNj3+inbMaVigtK4PLyP"
    "q+Topyzvx9USFgRvyuoxn0Hgb+R0A3j6SLRuyOdAi4gv7Y5oliynrSIEIAYGBgYG"
    "BgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGrgMEAQevAwQBBLADBAEF";

// kBadSessionTrailingData is a custom serialized SSL_SESSION with trailing data
// appended.
static const char kBadSessionTrailingData[] =
    "MIIBdgIBAQICAwMEAsAvBCAG5Q1ndq4Yfmbeo1zwLkNRKmCXGdNgWvGT3cskV0yQ"
    "kAQwJlrlzkAWBOWiLj/jJ76D7l+UXoizP2KI2C7I2FccqMmIfFmmkUy32nIJ0mZH"
    "IWoJoQYCBFRDO46iBAICASykAwQBAqUDAgEUphAEDnd3dy5nb29nbGUuY29tqAcE"
    "BXdvcmxkqQUCAwGJwKqBpwSBpBwUQvoeOk0Kg36SYTcLEkXqKwOBfF9vE4KX0Nxe"
    "LwjcDTpsuh3qXEaZ992r1N38VDcyS6P7I6HBYN9BsNHM362zZnY27GpTw+Kwd751"
    "CLoXFPoaMOe57dbBpXoro6Pd3BTbf/Tzr88K06yEOTDKPNj3+inbMaVigtK4PLyP"
    "q+Topyzvx9USFgRvyuoxn0Hgb+R0A3j6SLRuyOdAi4gv7Y5oliynrSIEIAYGBgYG"
    "BgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGrgMEAQevAwQBBLADBAEFAAAA";

static bool DecodeBase64(std::vector<uint8_t> *out, const char *in) {
  size_t len;
  if (!EVP_DecodedLength(&len, strlen(in))) {
    fprintf(stderr, "EVP_DecodedLength failed\n");
    return false;
  }

  out->resize(len);
  if (!EVP_DecodeBase64(out->data(), &len, len, (const uint8_t *)in,
                        strlen(in))) {
    fprintf(stderr, "EVP_DecodeBase64 failed\n");
    return false;
  }
  out->resize(len);
  return true;
}

TEST(SSLTest, SessionEncoding) {
  for (const char *input_b64 : {
           kOpenSSLSession,
           kCustomSession,
           kBoringSSLSession,
       }) {
    SCOPED_TRACE(std::string(input_b64));
    // Decode the input.
    std::vector<uint8_t> input;
    ASSERT_TRUE(DecodeBase64(&input, input_b64));

    // Verify the SSL_SESSION decodes.
    bssl::UniquePtr<SSL_CTX> ssl_ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ssl_ctx);
    bssl::UniquePtr<SSL_SESSION> session(
        SSL_SESSION_from_bytes(input.data(), input.size(), ssl_ctx.get()));
    ASSERT_TRUE(session) << "SSL_SESSION_from_bytes failed";

    // Verify the SSL_SESSION encoding round-trips.
    size_t encoded_len;
    bssl::UniquePtr<uint8_t> encoded;
    uint8_t *encoded_raw;
    ASSERT_TRUE(SSL_SESSION_to_bytes(session.get(), &encoded_raw, &encoded_len))
        << "SSL_SESSION_to_bytes failed";
    encoded.reset(encoded_raw);
    EXPECT_EQ(Bytes(encoded.get(), encoded_len), Bytes(input))
        << "SSL_SESSION_to_bytes did not round-trip";

    // Verify the SSL_SESSION also decodes with the legacy API.
    const uint8_t *cptr = input.data();
    session.reset(d2i_SSL_SESSION(NULL, &cptr, input.size()));
    ASSERT_TRUE(session) << "d2i_SSL_SESSION failed";
    EXPECT_EQ(cptr, input.data() + input.size());

    // Verify the SSL_SESSION encoding round-trips via the legacy API.
    int len = i2d_SSL_SESSION(session.get(), NULL);
    ASSERT_GT(len, 0) << "i2d_SSL_SESSION failed";
    ASSERT_EQ(static_cast<size_t>(len), input.size())
        << "i2d_SSL_SESSION(NULL) returned invalid length";

    encoded.reset((uint8_t *)OPENSSL_malloc(input.size()));
    ASSERT_TRUE(encoded);

    uint8_t *ptr = encoded.get();
    len = i2d_SSL_SESSION(session.get(), &ptr);
    ASSERT_GT(len, 0) << "i2d_SSL_SESSION failed";
    ASSERT_EQ(static_cast<size_t>(len), input.size())
        << "i2d_SSL_SESSION(NULL) returned invalid length";
    ASSERT_EQ(ptr, encoded.get() + input.size())
        << "i2d_SSL_SESSION did not advance ptr correctly";
    EXPECT_EQ(Bytes(encoded.get(), encoded_len), Bytes(input))
        << "SSL_SESSION_to_bytes did not round-trip";

    // Verify that |i2d_SSL_SESSION| works correctly when |pp| is non-NULL, but
    // |*pp| is NULL. A newly-allocated buffer containing the result should be
    // created. See |i2d_SAMPLE| for more details.
    uint8_t *ptr2 = nullptr;
    int len2 = i2d_SSL_SESSION(session.get(), &ptr2);
    ASSERT_TRUE(ptr2);
    ASSERT_GT(len2, 0);
    bssl::UniquePtr<uint8_t> encoded2(ptr2);
    EXPECT_EQ(Bytes(encoded2.get(), len2), Bytes(input))
        << "SSL_SESSION_to_bytes did not round-trip";
  }

  for (const char *input_b64 : {
           kBadSessionExtraField,
           kBadSessionVersion,
           kBadSessionTrailingData,
       }) {
    SCOPED_TRACE(std::string(input_b64));
    std::vector<uint8_t> input;
    ASSERT_TRUE(DecodeBase64(&input, input_b64));

    // Verify that the SSL_SESSION fails to decode.
    bssl::UniquePtr<SSL_CTX> ssl_ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ssl_ctx);
    bssl::UniquePtr<SSL_SESSION> session(
        SSL_SESSION_from_bytes(input.data(), input.size(), ssl_ctx.get()));
    EXPECT_FALSE(session) << "SSL_SESSION_from_bytes unexpectedly succeeded";
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

// CreateSessionWithTicket returns a sample |SSL_SESSION| with the specified
// version and ticket length or nullptr on failure.
static bssl::UniquePtr<SSL_SESSION> CreateSessionWithTicket(uint16_t version,
                                                            size_t ticket_len) {
  std::vector<uint8_t> der;
  if (!DecodeBase64(&der, kOpenSSLSession)) {
    return nullptr;
  }

  bssl::UniquePtr<SSL_CTX> ssl_ctx(SSL_CTX_new(TLS_method()));
  if (!ssl_ctx) {
    return nullptr;
  }
  // Use a garbage ticket.
  std::vector<uint8_t> ticket(ticket_len, 'a');
  bssl::UniquePtr<SSL_SESSION> session(
      SSL_SESSION_from_bytes(der.data(), der.size(), ssl_ctx.get()));
  if (!session || !SSL_SESSION_set_protocol_version(session.get(), version) ||
      !SSL_SESSION_set_ticket(session.get(), ticket.data(), ticket.size())) {
    return nullptr;
  }
  // Fix up the timeout.
#if defined(BORINGSSL_UNSAFE_DETERMINISTIC_MODE)
  SSL_SESSION_set_time(session.get(), 1234);
#else
  SSL_SESSION_set_time(session.get(), time(nullptr));
#endif
  return session;
}



// GetClientHelloLen creates a client SSL connection with the specified version
// and ticket length. It returns the length of the ClientHello, not including
// the record header, on success and zero on error.
static size_t GetClientHelloLen(uint16_t max_version, uint16_t session_version,
                                size_t ticket_len) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_SESSION> session =
      CreateSessionWithTicket(session_version, ticket_len);
  if (!ctx || !session) {
    return 0;
  }

  // Set a one-element cipher list so the baseline ClientHello is unpadded.
  bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
  if (!ssl || !SSL_set_session(ssl.get(), session.get()) ||
      !SSL_set_strict_cipher_list(ssl.get(), "ECDHE-RSA-AES128-GCM-SHA256") ||
      !SSL_set_max_proto_version(ssl.get(), max_version)) {
    return 0;
  }

  std::vector<uint8_t> client_hello;
  if (!GetClientHello(ssl.get(), &client_hello) ||
      client_hello.size() <= SSL3_RT_HEADER_LENGTH) {
    return 0;
  }

  return client_hello.size() - SSL3_RT_HEADER_LENGTH;
}

TEST(SSLTest, Padding) {
  struct PaddingVersions {
    uint16_t max_version, session_version;
  };
  static const PaddingVersions kPaddingVersions[] = {
      // Test the padding extension at TLS 1.2.
      {TLS1_2_VERSION, TLS1_2_VERSION},
      // Test the padding extension at TLS 1.3 with a TLS 1.2 session, so there
      // will be no PSK binder after the padding extension.
      {TLS1_3_VERSION, TLS1_2_VERSION},
      // Test the padding extension at TLS 1.3 with a TLS 1.3 session, so there
      // will be a PSK binder after the padding extension.
      {TLS1_3_VERSION, TLS1_3_VERSION},

  };

  struct PaddingTest {
    size_t input_len, padded_len;
  };
  static const PaddingTest kPaddingTests[] = {
      // ClientHellos of length below 0x100 do not require padding.
      {0xfe, 0xfe},
      {0xff, 0xff},
      // ClientHellos of length 0x100 through 0x1fb are padded up to 0x200.
      {0x100, 0x200},
      {0x123, 0x200},
      {0x1fb, 0x200},
      // ClientHellos of length 0x1fc through 0x1ff get padded beyond 0x200. The
      // padding extension takes a minimum of four bytes plus one required
      // content
      // byte. (To work around yet more server bugs, we avoid empty final
      // extensions.)
      {0x1fc, 0x201},
      {0x1fd, 0x202},
      {0x1fe, 0x203},
      {0x1ff, 0x204},
      // Finally, larger ClientHellos need no padding.
      {0x200, 0x200},
      {0x201, 0x201},
  };

  for (const PaddingVersions &versions : kPaddingVersions) {
    SCOPED_TRACE(versions.max_version);
    SCOPED_TRACE(versions.session_version);

    // Sample a baseline length.
    size_t base_len =
        GetClientHelloLen(versions.max_version, versions.session_version, 1);
    ASSERT_NE(base_len, 0u) << "Baseline length could not be sampled";

    for (const PaddingTest &test : kPaddingTests) {
      SCOPED_TRACE(test.input_len);
      ASSERT_LE(base_len, test.input_len) << "Baseline ClientHello too long";

      size_t padded_len =
          GetClientHelloLen(versions.max_version, versions.session_version,
                            1 + test.input_len - base_len);
      EXPECT_EQ(padded_len, test.padded_len)
          << "ClientHello was not padded to expected length";
    }
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





static bssl::UniquePtr<X509> GetED25519TestCertificate() {
  static const char kCertPEM[] =
      "-----BEGIN CERTIFICATE-----\n"
      "MIIBRDCB9wIUKI+32tShPulvafJa3xZvj29Z9xgwBQYDK2VwMEUxCzAJBgNVBAYT\n"
      "AkFVMRMwEQYDVQQIDApTb21lLVN0YXRlMSEwHwYDVQQKDBhJbnRlcm5ldCBXaWRn\n"
      "aXRzIFB0eSBMdGQwHhcNMjMwNzE4MTg0NzU4WhcNMjMwNzE5MTg0NzU4WjBFMQsw\n"
      "CQYDVQQGEwJBVTETMBEGA1UECAwKU29tZS1TdGF0ZTEhMB8GA1UECgwYSW50ZXJu\n"
      "ZXQgV2lkZ2l0cyBQdHkgTHRkMCowBQYDK2VwAyEAprAzqgxux8R4ZXaxn5mM/5E9\n"
      "0RNE59r47BJikdOoeUwwBQYDK2VwA0EAMELt0XRGFYo4qkWwOsoSYcdGYqlxVlf9\n"
      "AhTPaJ6SSzjv3n4r60wfe8Z2OPn415tcj2IIm42T64itI4OAX0aTCg==\n"
      "-----END CERTIFICATE-----\n";
  return CertFromPEM(kCertPEM);
}

static bssl::UniquePtr<EVP_PKEY> GetED25519TestKey() {
  static const char kKeyPEM[] =
      "-----BEGIN PRIVATE KEY-----\n"
      "MC4CAQAwBQYDK2VwBCIEIGPkz4xAobc5gtRidkHl+fxNLHfiWo3efRG2G8Z617yk\n"
      "-----END PRIVATE KEY-----\n";
  return KeyFromPEM(kKeyPEM);
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

static int XORCompressFunc(SSL *ssl, CBB *out, const uint8_t *in,
                           size_t in_len) {
  for (size_t i = 0; i < in_len; i++) {
    if (!CBB_add_u8(out, in[i] ^ 0x55)) {
      return 0;
    }
  }

  SSL_set_app_data(ssl, XORCompressFunc);

  return 1;
}

static int XORDecompressFunc(SSL *ssl, CRYPTO_BUFFER **out,
                             size_t uncompressed_len, const uint8_t *in,
                             size_t in_len) {
  if (in_len != uncompressed_len) {
    return 0;
  }

  uint8_t *data;
  *out = CRYPTO_BUFFER_alloc(&data, uncompressed_len);
  if (*out == nullptr) {
    return 0;
  }

  for (size_t i = 0; i < in_len; i++) {
    data[i] = in[i] ^ 0x55;
  }

  SSL_set_app_data(ssl, XORDecompressFunc);

  return 1;
}

TEST(SSLTest, CertCompression) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx(
      CreateContextWithTestCertificate(TLS_method()));
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_set_max_proto_version(server_ctx.get(), TLS1_3_VERSION));
  ASSERT_TRUE(SSL_CTX_add_cert_compression_alg(
      client_ctx.get(), 0x1234, XORCompressFunc, XORDecompressFunc));
  ASSERT_TRUE(SSL_CTX_add_cert_compression_alg(
      server_ctx.get(), 0x1234, XORCompressFunc, XORDecompressFunc));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));

  EXPECT_TRUE(SSL_get_app_data(client.get()) == XORDecompressFunc);
  EXPECT_TRUE(SSL_get_app_data(server.get()) == XORCompressFunc);
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

struct EncodeDecodeKATTestParam {
  const char *input;
  const char *output;
};

static const EncodeDecodeKATTestParam kEncodeDecodeKATs[] = {
    // V1 input round-trips as V2 output
    {"308201173082011302010102020303020240003081fa0201010408000000000000000104"
     "0800000000000000010420000004d29e62f41ded4bb33d0faa6ffada380e2c489dfbfb44"
     "4f574e475244010420cf3926d1ec5a562a642935a8050222b0aed93ffd9d1cac682274d9"
     "42e99e42a604020000020100020103040cb9b409f5129440622f87f84402010c040c1f49"
     "e2e989c66a263e9c227502010c020100020100020100a05b3059020101020203030402cc"
     "a80400043085668dcf9f0921094ebd7f91bf2a8c60d276e4c279fd85a989402f67868232"
     "4fd8098dc19d900b856d0a77e048e3ced2a104020204d2a20402021c20a4020400b10301"
     "01ffb20302011da206040474657374a7030101ff020108020100a0030101ff",
     "308201803082017c02010102020303020240003082016202010204080000000000000001"
     "040800000000000000010420000004d29e62f41ded4bb33d0faa6ffada380e2c489dfbfb"
     "444f574e475244010420cf3926d1ec5a562a642935a8050222b0aed93ffd9d1cac682274"
     "d942e99e42a6040200000201000201030440b9b409f5129440622f87f84402010c040c1f"
     "49e2e989c66a263e9c227502010c020100020100020100a05b3059020101020203030402"
     "cca80400043085668dcf02010c04401f49e2e989c66a263e9c227502010c020100020100"
     "020100a05b3059020101020203030402cca80400043085668dcf9f0921094ebd7f91bf2a"
     "8c60d276e4c27902010c020100020100020100a05b3059020101020203030402cca80400"
     "043085668dcf9f0921094ebd7f91bf2a8c60d276e4c279fd85a989402f678682324fd809"
     "8dc19d900b856d0a77e048e3ced2a104020204d2a20402021c20a4020400b1030101ffb2"
     "0302011da206040474657374a7030101ff020108020100a0030101ff"},
    // In runner.go, the test case "Basic-Server-TLS-Sync-SSL_Transfer" is used
    // to generate below bytes by adding print statement on the output of
    // |SSL_to_bytes| in bssl_shim.cc.
    // We've bumped the buffer size in the |previous_client/server_finished|
    // fields. This verifies that the original size is parsable and reencoded
    // with the new size.
    {"308201173082011302010102020303020240003081fa0201020408000000000000000104"
     "0800000000000000010420000004d29e62f41ded4bb33d0faa6ffada380e2c489dfbfb44"
     "4f574e475244010420cf3926d1ec5a562a642935a8050222b0aed93ffd9d1cac682274d9"
     "42e99e42a604020000020100020103040cb9b409f5129440622f87f84402010c040c1f49"
     "e2e989c66a263e9c227502010c020100020100020100a05b3059020101020203030402cc"
     "a80400043085668dcf9f0921094ebd7f91bf2a8c60d276e4c279fd85a989402f67868232"
     "4fd8098dc19d900b856d0a77e048e3ced2a104020204d2a20402021c20a4020400b10301"
     "01ffb20302011da206040474657374a7030101ff020108020100a0030101ff",
     "308201803082017c02010102020303020240003082016202010204080000000000000001"
     "040800000000000000010420000004d29e62f41ded4bb33d0faa6ffada380e2c489dfbfb"
     "444f574e475244010420cf3926d1ec5a562a642935a8050222b0aed93ffd9d1cac682274"
     "d942e99e42a6040200000201000201030440b9b409f5129440622f87f84402010c040c1f"
     "49e2e989c66a263e9c227502010c020100020100020100a05b3059020101020203030402"
     "cca80400043085668dcf02010c04401f49e2e989c66a263e9c227502010c020100020100"
     "020100a05b3059020101020203030402cca80400043085668dcf9f0921094ebd7f91bf2a"
     "8c60d276e4c27902010c020100020100020100a05b3059020101020203030402cca80400"
     "043085668dcf9f0921094ebd7f91bf2a8c60d276e4c279fd85a989402f678682324fd809"
     "8dc19d900b856d0a77e048e3ced2a104020204d2a20402021c20a4020400b1030101ffb2"
     "0302011da206040474657374a7030101ff020108020100a0030101ff"},
     // In runner.go, the test case
     // "TLS-TLS13-AES_128_GCM_SHA256-server-SSL_Transfer" is used to generate
     // below bytes by adding print statement on the output of |SSL_to_bytes| in
     // bssl_shim.cc.
     // We've bumped the buffer size in the |previous_client/server_finished|
     // fields. This verifies that the original size is parsable and reencoded
     // with the new size.
    {"308203883082038402010102020304020240003082036a020102040800000000000000000"
      "408000000000000000004206beca5c14aff6b92757545948b883c6c175327814bedcf38a6"
      "b2e4c43bc02d180420a32aee5b7705a19e4bb2b47f4918199c76cee7245f1311bc4ba3888"
      "3d33f236a04020000020100020101040c000000000000000000000000020100040c000000"
      "000000000000000000020100020100020100020100a04e304c02010102020304040213010"
      "40004200b66320d38c8fa1b0dfe9e37fcf2bf0bafb43077fa31ed2f1220dd245cef4c4da1"
      "04020204d2a205020302a300a4020400b20302011db9050203093a80a206040474657374a"
      "b03020100ac03010100ad03010100ae03010100af03020100b032043034c0893be938bade"
      "e7029ca3cfea4c821dde48e03f0d07641cba33b247bc161c0000000000000000000000000"
      "0000000b103020120b232043094b319ed2f41ee11aa73e141a238e5724c04f2aa8298c16b"
      "43c910c40cc98d1500000000000000000000000000000000b303020120b432043015a178c"
      "e69c0110ad36da8d58ca8428d9615ff07fc6a4e1bbab026c1bb0c02180000000000000000"
      "0000000000000000b503020120b88201700482016c040000b20002a30056355452010000a"
      "027abfd1f1aa28cee6e8e2396112e8285f150768898158dbce97a1aef0a63fa6dda1002a4"
      "d75942a3739c11e4b25827f529ab59d22e34e0cf0b59b9336eb60edbb1f686c072ab33c30"
      "e784f876da5b4c7fddd67f4a2ffa995f8c9ccf2128200ae9668d626866b1b7c6bb111867a"
      "87ed2a96122736595374f8fe5343e6ca492b278b67b1571423f2c1bcb673922e9044e9094"
      "9975ff72ab4a0eb659d8de664cac600042a2a0000040000b20002a3009e8c6738010100a0"
      "27abfd1f1aa28cee6e8e2396112e82851f15c84668b2f1d717681d1a3c6d2ea52d3401d31"
      "10a04498246480b96a7e5b3c39ea6cef3a2a86b81896f1621950472d858d18796c97e8320"
      "4daf94c1f30dfe763cd282fbee718a679dca8bff3cc8e11724062232e573bcf0252dc4d39"
      "0baa2b7f49a164b46d2d685e9fe826465cc135130f3e2e47838658af57173f864070fdce2"
      "41be58ecbd60d18128dfa28f4b1a00042a2a0000ba2330210201010204030013013016020"
      "101020117040e300c0201010201000201000101ffbb233021020101020403001301301602"
      "0101020117040e300c0201010201000201000101ff020108020100a0030101ff",
      "308203f0308203ec0201010202030402024000308203d202010204080000000000000000"
      "0408000000000000000004206beca5c14aff6b92757545948b883c6c175327814bedcf38"
      "a6b2e4c43bc02d180420a32aee5b7705a19e4bb2b47f4918199c76cee7245f1311bc4ba3"
      "8883d33f236a040200000201000201010440000000000000000000000000020100040c00"
      "0000000000000000000000020100020100020100020100a04e304c020101020203040402"
      "1301040004200b66320d0201000440000000000000000000000000020100020100020100"
      "020100a04e304c0201010202030404021301040004200b66320d38c8fa1b0dfe9e37fcf2"
      "bf0bafb43077fa020100020100020100020100a04e304c02010102020304040213010400"
      "04200b66320d38c8fa1b0dfe9e37fcf2bf0bafb43077fa31ed2f1220dd245cef4c4da104"
      "020204d2a205020302a300a4020400b20302011db9050203093a80a206040474657374ab"
      "03020100ac03010100ad03010100ae03010100af03020100b032043034c0893be938bade"
      "e7029ca3cfea4c821dde48e03f0d07641cba33b247bc161c000000000000000000000000"
      "00000000b103020120b232043094b319ed2f41ee11aa73e141a238e5724c04f2aa8298c1"
      "6b43c910c40cc98d1500000000000000000000000000000000b303020120b432043015a1"
      "78ce69c0110ad36da8d58ca8428d9615ff07fc6a4e1bbab026c1bb0c0218000000000000"
      "00000000000000000000b503020120b88201700482016c040000b20002a3005635545201"
      "0000a027abfd1f1aa28cee6e8e2396112e8285f150768898158dbce97a1aef0a63fa6dda"
      "1002a4d75942a3739c11e4b25827f529ab59d22e34e0cf0b59b9336eb60edbb1f686c072"
      "ab33c30e784f876da5b4c7fddd67f4a2ffa995f8c9ccf2128200ae9668d626866b1b7c6b"
      "b111867a87ed2a96122736595374f8fe5343e6ca492b278b67b1571423f2c1bcb673922e"
      "9044e90949975ff72ab4a0eb659d8de664cac600042a2a0000040000b20002a3009e8c67"
      "38010100a027abfd1f1aa28cee6e8e2396112e82851f15c84668b2f1d717681d1a3c6d2e"
      "a52d3401d3110a04498246480b96a7e5b3c39ea6cef3a2a86b81896f1621950472d858d1"
      "8796c97e83204daf94c1f30dfe763cd282fbee718a679dca8bff3cc8e11724062232e573"
      "bcf0252dc4d390baa2b7f49a164b46d2d685e9fe826465cc135130f3e2e47838658af571"
      "73f864070fdce241be58ecbd60d18128dfa28f4b1a00042a2a0000ba2330210201010204"
      "030013013016020101020117040e300c0201010201000201000101ffbb23302102010102"
      "04030013013016020101020117040e300c0201010201000201000101ff020108020100a0"
      "030101ff"},
    // In runner.go, the test case
    // "TLS-ECH-Server-Cipher-HKDF-SHA256-AES-256-GCM-SSL_Transfer" is used
    // to generate below bytes by adding print statement on the output of
    // |SSL_to_bytes| in bssl_shim.cc.
    {"308203e3308203df0201010202030402024000308203c502010204080000000000000000"
     "04080000000000000000042028431b914ffdb44ea92ca53d5734976c6a16f141d44f180b"
     "0816a5cb2b8e79030420bdaf544fa82d833d58c92213e44e850cc0b8147699b0b410d4aa"
     "2a277030f3220402000002010002010104409e155007d04cd03cf4d8a95ce244dc978a87"
     "e1808f0f6c6acb51ad7bf8063ae000000000000000000000000000000000000000000000"
     "0000000000000000000002012004406680e8c36429d465ea520ae74a2062a5e07c39f34b"
     "688024ae2edfab2898670700000000000000000000000000000000000000000000000000"
     "00000000000000020120020100020100020100a04e304c02010102020304040213030400"
     "0420df74ecd172087ad53083d505145ec4f6cf0ec5ed64b67ba526d55c918a0f8936a104"
     "020204d2a205020302a300a4020400b20302011db9050203093a80a210040e7365637265"
     "742e6578616d706c65ab03020100ac03010100ad03010100ae03010100af03020100b032"
     "0430c40f9f95646fa700d58934e79c36b84ba3502d33df04248d56cded3444927e300000"
     "0000000000000000000000000000b103020120b23204307a1a99bf276b5e5be57dd68968"
     "411594e77b1a48cf2c03cc5c143985aa40b32e00000000000000000000000000000000b3"
     "03020120b4320430cbf50af88bc5a610910139172a468663675882caacaf176aa961b12a"
     "38a0df2a00000000000000000000000000000000b503020120b703020101b88201700482"
     "016c040000b20002a300bbccf972010000a041e0b13ecd71dfb3d9e3cb451e37cfde8197"
     "3a1b73106b6669b53475781f0203a3f32f45cef7742cf0efb86d850081254f20d3b6bd83"
     "30bc70331464905bcd99383c33e42c7d34bfeb47b387bf43b5c796daa4581f8b0043b7eb"
     "216911f8eebaf1e8bd5d05277943d5a319cc03d9555e414990099f56ee887145f34e8bff"
     "27f06d1865aa64d548a22208318566959a097c080fa3e5e0d4b1d933132ef32929950004"
     "5a5a0000040000b20002a3002ecba343010100a041e0b13ecd71dfb3d9e3cb451e37cfde"
     "289f90201519fb0dff08aa9e14a9f4ee1434edce481e49d22f061529bb4d230258f3dac8"
     "86c2c1100bee2ccc7be889a90b417270c30b3b770558ef6f3c444ddefd08e673f788931d"
     "86542c4a1e7ec44b0957bb315c17851bd8498b1d1131a79e19c66463e0566985ef55deb5"
     "48fe370058ba83566278d01b3a565075b8ef2a82bea17ae95fa91b7b3ffa611a7d8a6331"
     "00045a5a0000ba15301302010102040300130330080201010201050400bb153013020101"
     "02040300130330080201010201050400020108020100a0030101ff", nullptr}
};

class EncodeDecodeKATTest
    : public testing::TestWithParam<EncodeDecodeKATTestParam> {};

INSTANTIATE_TEST_SUITE_P(EncodeAndDecodeKATTests, EncodeDecodeKATTest,
                         testing::ValuesIn(kEncodeDecodeKATs));

TEST_P(EncodeDecodeKATTest, RoundTrips) {
  std::string input(GetParam().input);
  std::string output;
  if (GetParam().output) {
    output = std::string(GetParam().output);
  } else {
    output = std::string(GetParam().input);
  }

  std::vector<uint8_t> input_bytes;
  ASSERT_TRUE(DecodeHex(&input_bytes, input));
  std::vector<uint8_t> output_bytes;
  ASSERT_TRUE(DecodeHex(&output_bytes, output));

  bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_method()));
  // Check the bytes are decoded successfully.
  bssl::UniquePtr<SSL> ssl(
      SSL_from_bytes(input_bytes.data(), input_bytes.size(), server_ctx.get()));
  ASSERT_TRUE(ssl);
  // Check the ssl can be encoded successfully.
  size_t encoded_len;
  uint8_t *encoded;
  ASSERT_TRUE(SSL_to_bytes(ssl.get(), &encoded, &encoded_len));
  bssl::UniquePtr<uint8_t> encoded_ptr;
  encoded_ptr.reset(encoded);
  // Check the encoded bytes are the same as the test input.
  ASSERT_EQ(output_bytes.size(), encoded_len);
  ASSERT_EQ(OPENSSL_memcmp(output_bytes.data(), encoded, encoded_len), 0);
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

// Test that failures are supressed on (potentially)
// transient empty reads.
TEST(SSLTest, IntermittentEmptyRead) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);
  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));

  // Create a fake read BIO that returns 0 on read to simulate empty read
  bssl::UniquePtr<BIO_METHOD> method(BIO_meth_new(0, nullptr));
  ASSERT_TRUE(method);
  ASSERT_TRUE(BIO_meth_set_create(method.get(), [](BIO *b) -> int {
    BIO_set_init(b, 1);
    return 1;
  }));
  ASSERT_TRUE(BIO_meth_set_read(method.get(), [](BIO *, char *, int) -> int {
    return 0;
  }));
  bssl::UniquePtr<BIO> rbio_empty(BIO_new(method.get()));
  ASSERT_TRUE(rbio_empty);
  BIO_set_flags(rbio_empty.get(), BIO_FLAGS_READ);

  // Save off client rbio and use empty read BIO
  bssl::UniquePtr<BIO> client_rbio(SSL_get_rbio(client.get()));
  ASSERT_TRUE(client_rbio);
  // Up-ref |client_rbio| as SSL_CTX dtor will also attempt to free it
  ASSERT_TRUE(BIO_up_ref(client_rbio.get()));
  SSL_set0_rbio(client.get(), rbio_empty.release());

  // Server writes some data to the client
  const uint8_t write_data[] = {1, 2, 3};
  int ret = SSL_write(server.get(), write_data, (int) sizeof(write_data));
  EXPECT_EQ(ret, (int) sizeof(write_data));
  EXPECT_EQ(SSL_get_error(server.get(), ret), SSL_ERROR_NONE);

  uint8_t read_data[] = {0, 0, 0};
  ret = SSL_read(client.get(), read_data, sizeof(read_data));
  EXPECT_EQ(ret, 0);
  // On empty read, client should still want a read so caller will retry.
  // This would have returned |SSL_ERROR_SYSCALL| in OpenSSL 1.0.2.
  EXPECT_EQ(SSL_get_error(client.get(), ret), SSL_ERROR_WANT_READ);

  // Reset client rbio, read should succeed
  SSL_set0_rbio(client.get(), client_rbio.release());
  ret = SSL_read(client.get(), read_data, sizeof(read_data));
  EXPECT_EQ(ret, (int) sizeof(write_data));
  EXPECT_EQ(OPENSSL_memcmp(read_data, write_data, sizeof(write_data)), 0);
  EXPECT_EQ(SSL_get_error(client.get(), ret), SSL_ERROR_NONE);

  // Subsequent attempts to read should fail
  ret = SSL_read(client.get(), read_data, sizeof(read_data));
  EXPECT_LT(ret, 0);
  EXPECT_EQ(SSL_get_error(client.get(), ret), SSL_ERROR_WANT_READ);
}

// Test that |SSL_shutdown|, when quiet shutdown is enabled, simulates receiving
// a close_notify, down to |SSL_read| reporting |SSL_ERROR_ZERO_RETURN|.
TEST(SSLTest, QuietShutdown) {
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  bssl::UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);
  SSL_CTX_set_quiet_shutdown(server_ctx.get(), 1);
  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));

  // Quiet shutdown is enabled, so |SSL_shutdown| on the server should
  // immediately return that bidirectional shutdown "completed".
  EXPECT_EQ(SSL_shutdown(server.get()), 1);

  // Shut down writes so the client gets an EOF.
  EXPECT_TRUE(BIO_shutdown_wr(SSL_get_wbio(server.get())));

  // Confirm no close notify was actually sent. Client reads should report a
  // transport EOF, not a close_notify. (Both have zero return, but
  // |SSL_get_error| is different.)
  char buf[1];
  int ret = SSL_read(client.get(), buf, sizeof(buf));
  EXPECT_EQ(ret, 0);
  EXPECT_EQ(SSL_get_error(client.get(), ret), SSL_ERROR_SYSCALL);

  // The server believes bidirectional shutdown completed, so reads should
  // replay the (simulated) close_notify.
  ret = SSL_read(server.get(), buf, sizeof(buf));
  EXPECT_EQ(ret, 0);
  EXPECT_EQ(SSL_get_error(server.get(), ret), SSL_ERROR_ZERO_RETURN);
}

TEST(SSLTest, InvalidSignatureAlgorithm) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);

  static const uint16_t kInvalidPrefs[] = {1234};
  EXPECT_FALSE(SSL_CTX_set_signing_algorithm_prefs(
      ctx.get(), kInvalidPrefs, OPENSSL_ARRAY_SIZE(kInvalidPrefs)));
  EXPECT_FALSE(SSL_CTX_set_verify_algorithm_prefs(
      ctx.get(), kInvalidPrefs, OPENSSL_ARRAY_SIZE(kInvalidPrefs)));

  static const uint16_t kDuplicatePrefs[] = {SSL_SIGN_RSA_PKCS1_SHA256,
                                             SSL_SIGN_RSA_PKCS1_SHA256};
  EXPECT_FALSE(SSL_CTX_set_signing_algorithm_prefs(
      ctx.get(), kDuplicatePrefs, OPENSSL_ARRAY_SIZE(kDuplicatePrefs)));
  EXPECT_FALSE(SSL_CTX_set_verify_algorithm_prefs(
      ctx.get(), kDuplicatePrefs, OPENSSL_ARRAY_SIZE(kDuplicatePrefs)));
}

TEST(SSLTest, ErrorStrings) {
  int warning_value = SSL3_AD_CLOSE_NOTIFY | (SSL3_AL_WARNING << 8);
  int fatal_value = SSL3_AD_UNEXPECTED_MESSAGE | (SSL3_AL_FATAL << 8);
  int unknown_value = 99999;

  EXPECT_EQ(Bytes(SSL_alert_desc_string(warning_value)), Bytes("CN"));
  EXPECT_EQ(Bytes(SSL_alert_desc_string(fatal_value)), Bytes("UM"));
  EXPECT_EQ(Bytes(SSL_alert_desc_string(unknown_value)), Bytes("UK"));

  EXPECT_EQ(Bytes(SSL_alert_type_string(warning_value)), Bytes("W"));
  EXPECT_EQ(Bytes(SSL_alert_type_string(fatal_value)), Bytes("F"));
  EXPECT_EQ(Bytes(SSL_alert_type_string(unknown_value)), Bytes("U"));
}

TEST(SSLTest, NameLists) {
  struct {
    size_t (*func)(const char **, size_t);
    std::vector<std::string> expected;
  } kTests[] = {
      {SSL_get_all_version_names, {"TLSv1.3", "DTLSv1.2", "unknown"}},
      {SSL_get_all_standard_cipher_names,
       {"TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256", "TLS_AES_128_GCM_SHA256"}},
      {SSL_get_all_cipher_names,
       {"ECDHE-ECDSA-AES128-GCM-SHA256", "TLS_AES_128_GCM_SHA256", "(NONE)"}},
      {SSL_get_all_group_names, {"P-256", "X25519"}},
      {SSL_get_all_signature_algorithm_names,
       {"rsa_pkcs1_sha256", "ecdsa_secp256r1_sha256", "ecdsa_sha256"}},
  };
  for (const auto &t : kTests) {
    size_t num = t.func(nullptr, 0);
    EXPECT_GT(num, 0u);

    std::vector<const char*> list(num);
    EXPECT_EQ(num, t.func(list.data(), list.size()));

    // Check the expected values are in the list.
    for (const auto &s : t.expected) {
      EXPECT_NE(list.end(), std::find(list.begin(), list.end(), s))
          << "Could not find " << s;
    }

    // Passing in a larger buffer should leave excess space alone.
    std::vector<const char *> list2(num + 1, "placeholder");
    EXPECT_EQ(num, t.func(list2.data(), list2.size()));
    for (size_t i = 0; i < num; i++) {
      EXPECT_STREQ(list[i], list2[i]);
    }
    EXPECT_STREQ(list2.back(), "placeholder");

    // Passing in a shorter buffer should truncate the list.
    for (size_t l = 0; l < num; l++) {
      SCOPED_TRACE(l);
      list2.resize(l);
      EXPECT_EQ(num, t.func(list2.data(), list2.size()));
      for (size_t i = 0; i < l; i++) {
        EXPECT_STREQ(list[i], list2[i]);
      }
    }
  }
}


TEST(SSLTest, SessionPrint) {
 static const std::array<std::string, 15> kExpectedTLS13{
      {"SSL-Session:", "    Protocol  :", "    Cipher    : ",
       "    Session-ID: ", "    Session-ID-ctx:", "    Resumption PSK:",
       "    PSK identity:", "    TLS session ticket lifetime hint:",
       "    TLS session ticket:", "    61",
       "    Start Time:", "    Timeout   :", "    Verify return code:",
       "    Extended master secret:", "    Max Early Data:"}};

  static const std::array<std::string, 14> kExpectedTLS12{
      {"SSL-Session:", "    Protocol  :", "    Cipher    : ",
       "    Session-ID: ", "    Session-ID-ctx:", "    Master-Key:",
       "    PSK identity:", "    TLS session ticket lifetime hint:",
       "    TLS session ticket:", "    61",
       "    Start Time:", "    Timeout   :", "    Verify return code:",
       "    Extended master secret:"}};

  bssl::UniquePtr<SSL_SESSION> session(
      CreateSessionWithTicket(TLS1_3_VERSION, 10));
  bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_mem()));
  EXPECT_TRUE(SSL_SESSION_print(bio.get(), session.get()));
  const uint8_t *out;
  size_t outlen;
  ASSERT_TRUE(BIO_mem_contents(bio.get(), &out, &outlen));

  // Iterate through |kExpectedTLS13| and verify that |SSL_SESSION_print| has
  // the expected format.
  std::istringstream iss_tls13((std::string((char *)out, outlen)));
  std::string line;
  for (const auto &expected : kExpectedTLS13) {
    std::getline(iss_tls13, line);
    EXPECT_EQ(line.substr(0, expected.length()), expected);
  }

  session = CreateSessionWithTicket(TLS1_2_VERSION, 10);
  bio.reset(BIO_new(BIO_s_mem()));
  EXPECT_TRUE(SSL_SESSION_print(bio.get(), session.get()));
  ASSERT_TRUE(BIO_mem_contents(bio.get(), &out, &outlen));
  // Iterate through |kExpectedTLS12| and verify that |SSL_SESSION_print| has
  // the expected format.
  std::istringstream iss_tls12((std::string((char *)out, outlen)));
  for (const auto &expected : kExpectedTLS12) {
    std::getline(iss_tls12, line);
    EXPECT_EQ(line.substr(0, expected.length()), expected);
  }
}

class PerformHybridHandshakeTest : public testing::TestWithParam<HybridHandshakeTest> {};
INSTANTIATE_TEST_SUITE_P(PerformHybridHandshakeTests, PerformHybridHandshakeTest, testing::ValuesIn(kHybridHandshakeTests));

// This test runs through an overall handshake flow for all of the cases
// defined in kHybridHandshakeTests. This test runs through both positive and
// negative cases; refer to the comments inline in kHybridHandshakeTests for
// specifics about each test case.
TEST_P(PerformHybridHandshakeTest, PerformHybridHandshake) {
  HybridHandshakeTest t = GetParam();
  // Set up client and server with test case parameters
  bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(SSL_CTX_set1_curves_list(client_ctx.get(), t.client_rule));
  ASSERT_TRUE(
      SSL_CTX_set_max_proto_version(client_ctx.get(), t.client_version));

  bssl::UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(server_ctx);
  ASSERT_TRUE(SSL_CTX_set1_curves_list(server_ctx.get(), t.server_rule));
  ASSERT_TRUE(
      SSL_CTX_set_max_proto_version(server_ctx.get(), t.server_version));

  bssl::UniquePtr<SSL> client, server;
  ASSERT_TRUE(CreateClientAndServer(&client, &server, client_ctx.get(),
                                    server_ctx.get()));

  if (t.expected_group != 0) {
    // In this case, assert that the handshake completes as expected.
    ASSERT_TRUE(CompleteHandshakes(client.get(), server.get()));

    SSL_SESSION *client_session = SSL_get_session(client.get());
    ASSERT_TRUE(client_session);
    EXPECT_EQ(t.expected_group, client_session->group_id);
    EXPECT_EQ(t.is_hrr_expected, SSL_used_hello_retry_request(client.get()));
    EXPECT_EQ(std::min(t.client_version, t.server_version),
              client_session->ssl_version);

    SSL_SESSION *server_session = SSL_get_session(server.get());
    ASSERT_TRUE(server_session);
    EXPECT_EQ(t.expected_group, server_session->group_id);
    EXPECT_EQ(t.is_hrr_expected, SSL_used_hello_retry_request(server.get()));
    EXPECT_EQ(std::min(t.client_version, t.server_version),
              server_session->ssl_version);
  } else {
    // In this case, we expect the handshake to fail because client and
    // server configurations are not compatible.
    ASSERT_FALSE(CompleteHandshakes(client.get(), server.get()));

    ASSERT_FALSE(client.get()->s3->initial_handshake_complete);
    EXPECT_EQ(t.is_hrr_expected, SSL_used_hello_retry_request(client.get()));

    ASSERT_FALSE(server.get()->s3->initial_handshake_complete);
    EXPECT_EQ(t.is_hrr_expected, SSL_used_hello_retry_request(server.get()));
  }
}

TEST(SSLTest, SSLFileTests) {
#if defined(OPENSSL_ANDROID)
  // On Android, when running from an APK, temporary file creations do not work.
  // See b/36991167#comment8.
  GTEST_SKIP();
#endif

  char rsa_pem_filename[PATH_MAX];
  char ecdsa_pem_filename[PATH_MAX];
  ASSERT_TRUE(createTempFILEpath(rsa_pem_filename));
  ASSERT_TRUE(createTempFILEpath(ecdsa_pem_filename));

  ScopedFILE rsa_pem(fopen(rsa_pem_filename, "w"));
  ScopedFILE ecdsa_pem(fopen(ecdsa_pem_filename, "w"));
  ASSERT_TRUE(rsa_pem);
  ASSERT_TRUE(ecdsa_pem);

  bssl::UniquePtr<X509> rsa_leaf = GetChainTestCertificate();
  bssl::UniquePtr<X509> rsa_intermediate = GetChainTestIntermediate();
  bssl::UniquePtr<X509> ecdsa_leaf = GetECDSATestCertificate();
  ASSERT_TRUE(PEM_write_X509(rsa_pem.get(), rsa_leaf.get()));
  ASSERT_TRUE(PEM_write_X509(rsa_pem.get(), rsa_intermediate.get()));
  ASSERT_TRUE(PEM_write_X509(ecdsa_pem.get(), ecdsa_leaf.get()));
  rsa_pem.reset();
  ecdsa_pem.reset();

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  // Load a certificate into |ctx| and verify that |ssl| inherits it.
  EXPECT_TRUE(SSL_CTX_use_certificate_chain_file(ctx.get(), rsa_pem_filename));
  bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl);
  EXPECT_EQ(X509_cmp(SSL_get_certificate(ssl.get()), rsa_leaf.get()), 0);

  // Load a new cert into |ssl| and verify that it's correctly loaded.
  EXPECT_TRUE(SSL_use_certificate_chain_file(ssl.get(), ecdsa_pem_filename));
  EXPECT_EQ(X509_cmp(SSL_get_certificate(ssl.get()), ecdsa_leaf.get()), 0);

  ASSERT_EQ(remove(rsa_pem_filename), 0);
  ASSERT_EQ(remove(ecdsa_pem_filename), 0);
}

TEST(SSLTest, IncompatibleTLSVersionState) {
  // Using the following ASN.1 DER Sequence where 42 is the serialization
  // format version number of some future version not currently supported:
  // SEQUENCE {
  //   SEQUENCE {
  //     INTEGER { 42 }
  //   }
  // }
  static constexpr size_t INCOMPATIBLE_DER_LEN = 7;
  static const uint8_t INCOMPATIBLE_DER[INCOMPATIBLE_DER_LEN] = {
      0x30, 0x05, 0x30, 0x03, 0x02, 0x01, 0x2a};

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);

  ASSERT_FALSE(
      SSL_from_bytes(INCOMPATIBLE_DER, INCOMPATIBLE_DER_LEN, ctx.get()));
  ASSERT_EQ(ERR_GET_LIB(ERR_peek_error()), ERR_LIB_SSL);
  ASSERT_EQ(ERR_GET_REASON(ERR_peek_error()),
            SSL_R_SERIALIZATION_INVALID_SERDE_VERSION);
}

// Test that it is possible for the certificate to be configured on a mix of
// SSL_CTX and SSL. This ensures that we do not inadvertently overshare objects
// in SSL_new.
TEST(SSLTest, MixContextAndConnection) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  bssl::UniquePtr<X509> cert = GetTestCertificate();
  ASSERT_TRUE(cert);
  bssl::UniquePtr<EVP_PKEY> key = GetTestKey();
  ASSERT_TRUE(key);

  // Configure the certificate, but not the private key, on the context.
  ASSERT_TRUE(SSL_CTX_use_certificate(ctx.get(), cert.get()));

  bssl::UniquePtr<SSL> ssl1(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl1.get());
  bssl::UniquePtr<SSL> ssl2(SSL_new(ctx.get()));
  ASSERT_TRUE(ssl2.get());

  // There is no private key configured yet.
  EXPECT_FALSE(SSL_CTX_get0_privatekey(ctx.get()));
  EXPECT_FALSE(SSL_get_privatekey(ssl1.get()));
  EXPECT_FALSE(SSL_get_privatekey(ssl2.get()));

  // Configuring the private key on |ssl1| works.
  ASSERT_TRUE(SSL_use_PrivateKey(ssl1.get(), key.get()));
  EXPECT_TRUE(SSL_get_privatekey(ssl1.get()));

  // It does not impact the other connection or the context.
  EXPECT_FALSE(SSL_CTX_get0_privatekey(ctx.get()));
  EXPECT_FALSE(SSL_get_privatekey(ssl2.get()));
}

static size_t test_ecc_privkey_calls = 0;

static enum ssl_private_key_result_t test_ecc_privkey_complete(SSL *ssl,
                                                           uint8_t *out,
                                                           size_t *out_len,
                                                           size_t max_out) {
  test_ecc_privkey_calls += 1;
  return ssl_private_key_success;
}

static enum ssl_private_key_result_t test_ecc_privkey_sign(
    SSL *ssl, uint8_t *out, size_t *out_len, size_t max_out,
    uint16_t signature_algorithm, const uint8_t *in, size_t in_len) {
  bssl::UniquePtr<EVP_PKEY> pkey(GetECDSATestKey());

  if (EVP_PKEY_id(pkey.get()) !=
      SSL_get_signature_algorithm_key_type(signature_algorithm)) {
      return ssl_private_key_failure;
  }

  const EVP_MD *md = SSL_get_signature_algorithm_digest(signature_algorithm);
  bssl::ScopedEVP_MD_CTX ctx;
  EVP_PKEY_CTX *pctx = nullptr;
  if (!EVP_DigestSignInit(ctx.get(), &pctx, md, nullptr,
                          pkey.get())) {
    return ssl_private_key_failure;
  }

  size_t len = 0;
  if (!EVP_DigestSign(ctx.get(), nullptr, &len, in, in_len) || len > max_out) {
    return ssl_private_key_failure;
  }

  *out_len = max_out;

  if (!EVP_DigestSign(ctx.get(), out, out_len, in, in_len)) {
    return ssl_private_key_failure;
  }

  return test_ecc_privkey_complete(ssl, out, out_len, max_out);
}

static enum ssl_private_key_result_t test_ecc_privkey_decrypt(
    SSL *ssl, uint8_t *out, size_t *out_len, size_t max_out, const uint8_t *in,
    size_t in_len) {
  return ssl_private_key_failure;
}

static const SSL_PRIVATE_KEY_METHOD test_ecc_private_key_method = {
    test_ecc_privkey_sign,
    test_ecc_privkey_decrypt,
    test_ecc_privkey_complete,
};

TEST(SSLTest, SSLPrivateKeyMethod) {
  {
    bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
    bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_method()));

    bssl::UniquePtr<X509> ecdsa_cert(GetECDSATestCertificate());
    bssl::UniquePtr<CRYPTO_BUFFER> ecdsa_leaf =
        x509_to_buffer(ecdsa_cert.get());
    std::vector<CRYPTO_BUFFER *> chain = {
        ecdsa_leaf.get(),
    };

    // Index should be have been set to default, 0, but no key loaded
    EXPECT_EQ(server_ctx->cert->cert_private_key_idx, SSL_PKEY_RSA);
    EXPECT_EQ(
        server_ctx->cert->cert_private_keys[SSL_PKEY_RSA].privatekey.get(),
        nullptr);
    EXPECT_EQ(server_ctx->cert->key_method, nullptr);


    // Load a certificate chain containg the leaf but set private key method
    ASSERT_TRUE(SSL_CTX_set_chain_and_key(server_ctx.get(), &chain[0],
                                          chain.size(), nullptr,
                                          &test_ecc_private_key_method));

    // Should be initiall zero
    ASSERT_EQ(test_ecc_privkey_calls, (size_t)0);

    // Index must be ECC key now, but key_method must be set.
    ASSERT_EQ(server_ctx->cert->cert_private_key_idx, SSL_PKEY_ECC);
    ASSERT_EQ(server_ctx->cert->key_method, &test_ecc_private_key_method);

    bssl::UniquePtr<SSL> client, server;
    ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                       server_ctx.get(), ClientConfig(),
                                       false));

    ASSERT_TRUE(CompleteHandshakes(client.get(), server.get()));

    ASSERT_EQ(test_ecc_privkey_calls, (size_t)1);

    // Check the internal slot index to verify that the correct slot was used
    // during the handshake.
    ASSERT_EQ(server->config->cert->cert_private_key_idx, SSL_PKEY_ECC);
    ASSERT_EQ(server->config->cert->key_method, &test_ecc_private_key_method);
  }

  {
    size_t current_invoke_count = test_ecc_privkey_calls;

    bssl::UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
    bssl::UniquePtr<SSL_CTX> server_ctx(SSL_CTX_new(TLS_method()));

    // Index should be have been set to default, 0, but no key loaded
    EXPECT_EQ(server_ctx->cert->cert_private_key_idx, SSL_PKEY_RSA);
    EXPECT_EQ(
        server_ctx->cert->cert_private_keys[SSL_PKEY_RSA].privatekey.get(),
        nullptr);
    EXPECT_EQ(server_ctx->cert->key_method, nullptr);

    bssl::UniquePtr<X509> ed_cert(GetED25519TestCertificate());
    bssl::UniquePtr<EVP_PKEY> ed_key(GetED25519TestKey());
    bssl::UniquePtr<CRYPTO_BUFFER> ed_leaf = x509_to_buffer(ed_cert.get());
    std::vector<CRYPTO_BUFFER *> ed_chain = {
        ed_leaf.get(),
    };

    // Load a certificate chain containg the leaf but set private key method
    ASSERT_TRUE(SSL_CTX_set_chain_and_key(server_ctx.get(), &ed_chain[0],
                                          ed_chain.size(), ed_key.get(),
                                          nullptr));

    // Index must be ECC key now, but key_method must not be set.
    ASSERT_EQ(server_ctx->cert->cert_private_key_idx, SSL_PKEY_ED25519);
    ASSERT_EQ(server_ctx->cert->key_method, nullptr);

    std::vector<uint16_t> sigalgs = {SSL_SIGN_ED25519};

    ASSERT_TRUE(SSL_CTX_set_signing_algorithm_prefs(
        client_ctx.get(), sigalgs.data(), sigalgs.size()));
    ASSERT_TRUE(SSL_CTX_set_verify_algorithm_prefs(
        client_ctx.get(), sigalgs.data(), sigalgs.size()));

    bssl::UniquePtr<SSL> client, server;
    ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                       server_ctx.get(), ClientConfig(),
                                       false));

    ASSERT_TRUE(CompleteHandshakes(client.get(), server.get()));

    // This should still be the same, as we didn't use the private key method
    // functionality, so it shouldn't have incremented.
    ASSERT_EQ(test_ecc_privkey_calls, current_invoke_count);

    // Check the internal slot index to verify that the correct slot was used
    // during the handshake and that key_method was not set.
    ASSERT_EQ(server->config->cert->cert_private_key_idx, SSL_PKEY_ED25519);
    ASSERT_EQ(server->config->cert->key_method, nullptr);
  }
}

}  // namespace
BSSL_NAMESPACE_END
