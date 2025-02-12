/* Copyright (c) 2019, Google Inc.
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

#include <signal.h>
#include <algorithm>
#include <map>
#include <string>
#include <vector>
#include <cstring>

#include <sstream>

#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <string.h>
#include <cstdarg>
#include <iostream>

#include <openssl/aead.h>
#include <openssl/aes.h>
#include <openssl/bn.h>
#include <openssl/cipher.h>
#include <openssl/cmac.h>
#include <openssl/ctrdrbg.h>
#include <openssl/curve25519.h>
#include <openssl/dh.h>
#include <openssl/digest.h>
#include <openssl/ec.h>
#include <openssl/ec_key.h>
#include <openssl/ecdh.h>
#include <openssl/ecdsa.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/experimental/kem_deterministic_api.h>
#include <openssl/hkdf.h>
#include <openssl/hmac.h>
#include <openssl/kdf.h>
#include <openssl/obj.h>
#include <openssl/rsa.h>
#include <openssl/sha.h>
#include <openssl/span.h>
#include <openssl/sshkdf.h>

#include "../../../../crypto/fipsmodule/ec/internal.h"
#include "../../../../crypto/fipsmodule/hmac/internal.h"
#include "../../../../crypto/fipsmodule/rand/internal.h"
#include "../../../../crypto/fipsmodule/curve25519/internal.h"
#include "../../../../crypto/fipsmodule/ml_dsa/ml_dsa.h"
#include "../../../../crypto/fipsmodule/ml_dsa/ml_dsa_ref/params.h"
#include "modulewrapper.h"


namespace bssl {
namespace acvp {

#define LOG_ERROR(...) fprintf(stderr, __VA_ARGS__)

#define AES_GCM_NONCE_LENGTH 12

constexpr size_t kMaxArgLength = (1 << 20);

RequestBuffer::~RequestBuffer() = default;

class RequestBufferImpl : public RequestBuffer {
 public:
  ~RequestBufferImpl() = default;

  std::vector<uint8_t> buf;
  Span<const uint8_t> args[kMaxArgs];
};

// static
std::unique_ptr<RequestBuffer> RequestBuffer::New() {
  return std::unique_ptr<RequestBuffer>(new RequestBufferImpl);
}

static bool ReadAll(std::istream *stream, void *in_data, size_t data_len) {
  size_t read = stream->read(static_cast<char *>(in_data), data_len).gcount();

  if (read != data_len) {
    return false;
  }
  return true;
}

Span<const Span<const uint8_t>> ParseArgsFromStream(std::istream *stream,
                                                    RequestBuffer *in_buffer) {
  RequestBufferImpl *buffer = static_cast<RequestBufferImpl *>(in_buffer);
  uint32_t nums[1 + kMaxArgs];
  const Span<const Span<const uint8_t>> empty_span;

  if (!ReadAll(stream, nums, sizeof(uint32_t) * 2)) {
    return empty_span;
  }

  const size_t num_args = nums[0];
  if (num_args == 0) {
    LOG_ERROR("Invalid, zero-argument operation requested.\n");
    return empty_span;
  } else if (num_args > kMaxArgs) {
    LOG_ERROR("Operation requested with %zu args, but %zu is the limit.\n",
              num_args, kMaxArgs);
    return empty_span;
  }

  if (num_args > 1 &&
      !ReadAll(stream, &nums[2], sizeof(uint32_t) * (num_args - 1))) {
    return empty_span;
  }

  size_t need = 0;
  for (size_t i = 0; i < num_args; i++) {
    const size_t arg_length = nums[i + 1];
    if (i == 0 && arg_length > kMaxNameLength) {
      LOG_ERROR("Operation with name of length %zu exceeded limit of %zu.\n",
                arg_length, kMaxNameLength);
      return empty_span;
    } else if (arg_length > kMaxArgLength) {
      LOG_ERROR(
          "Operation with argument of length %zu exceeded limit of %zu.\n",
          arg_length, kMaxArgLength);
      return empty_span;
    }

    // This static_assert confirms that the following addition doesn't
    // overflow.
    static_assert((kMaxArgs - 1 * kMaxArgLength) + kMaxNameLength > (1 << 30),
                  "Argument limits permit excessive messages");
    need += arg_length;
  }

  if (need > buffer->buf.size()) {
    size_t alloced = need + (need >> 1);
    if (alloced < need) {
      abort();
    }
    buffer->buf.resize(alloced);
  }

  if (!ReadAll(stream, buffer->buf.data(), need)) {
    return empty_span;
  }

  size_t offset = 0;
  for (size_t i = 0; i < num_args; i++) {
    buffer->args[i] = Span<const uint8_t>(&buffer->buf[offset], nums[i + 1]);
    offset += nums[i + 1];
  }

  return Span<const Span<const uint8_t>>(buffer->args, num_args);
}

bool WriteReplyToStream(std::ostream *stream,
                        const std::vector<Span<const uint8_t>> &spans) {
  if (spans.empty() || spans.size() > kMaxArgs) {
    abort();
  }
  uint32_t nums[1 + kMaxArgs];
  nums[0] = spans.size();
  for (size_t i = 0; i < spans.size(); i++) {
    const auto &span = spans[i];
    nums[i + 1] = span.size();
  }
  stream->write(reinterpret_cast<const char *>(nums),
                sizeof(uint32_t) * (1 + spans.size()));

  for (size_t i = 0; i < spans.size(); i++) {
    const auto &span = spans[i];
    if (span.empty()) {
      continue;
    }
    stream->write(reinterpret_cast<const char *>(span.data()),
                  sizeof(uint8_t) * span.size());
  }

  stream->flush();
  return true;
}

static bool GetConfig(const Span<const uint8_t> args[],
                      ReplyCallback write_reply) {
  static constexpr char kConfig[] =
      R"([
      {
        "algorithm": "SHA2-224",
        "revision": "1.0",
        "messageLength": [{
          "min": 0, "max": 65528, "increment": 8
        }],
        "performLargeDataTest": [1, 2, 4, 8]
      },
      {
        "algorithm": "SHA2-256",
        "revision": "1.0",
        "messageLength": [{
          "min": 0, "max": 65528, "increment": 8
        }],
        "performLargeDataTest": [1, 2, 4, 8]
      },
      {
        "algorithm": "SHA2-384",
        "revision": "1.0",
        "messageLength": [{
          "min": 0, "max": 65528, "increment": 8
        }],
        "performLargeDataTest": [1, 2, 4, 8]
      },
      {
        "algorithm": "SHA2-512",
        "revision": "1.0",
        "messageLength": [{
          "min": 0, "max": 65528, "increment": 8
        }],
        "performLargeDataTest": [1, 2, 4, 8]
      },
      {
        "algorithm": "SHA2-512/224",
        "revision": "1.0",
        "messageLength": [{
          "min": 0, "max": 65528, "increment": 8
        }],
        "performLargeDataTest": [1, 2, 4, 8]
      },
      {
        "algorithm": "SHA2-512/256",
        "revision": "1.0",
        "messageLength": [{
          "min": 0, "max": 65528, "increment": 8
        }],
        "performLargeDataTest": [1, 2, 4, 8]
      },
      {
        "algorithm": "SHA3-224",
        "revision": "2.0",
        "messageLength": [{
          "min": 0, "max": 65536, "increment": 8
        }],
        "performLargeDataTest": [1, 2, 4, 8]
      },
      {
        "algorithm": "SHA3-256",
        "revision": "2.0",
        "messageLength": [{
          "min": 0, "max": 65536, "increment": 8
          }],
        "performLargeDataTest": [1, 2, 4, 8]
      },
      {
        "algorithm": "SHA3-384",
        "revision": "2.0",
        "messageLength": [{
          "min": 0, "max": 65536, "increment": 8
        }],
        "performLargeDataTest": [1, 2, 4, 8]
      },
      {
        "algorithm": "SHA3-512",
        "revision": "2.0",
        "messageLength": [{
          "min": 0, "max": 65536, "increment": 8
          }],
        "performLargeDataTest": [1, 2, 4, 8]
      },
      {
        "algorithm": "SHAKE-128",
        "revision": "1.0",
        "messageLength": [{
          "min": 0, "max": 65536, "increment": 8
        }],
        "outputLen": [{
            "min": 128,
            "max": 8192,
            "increment": 8
        }],
        "performLargeDataTest": [1, 2, 4, 8]
      },
      {
        "algorithm": "SHAKE-256",
        "revision": "1.0",
        "messageLength": [{
          "min": 0, "max": 65536, "increment": 8
        }],
        "outputLen": [{
            "min": 128,
            "max": 8192,
            "increment": 8
        }],
        "performLargeDataTest": [1, 2, 4, 8]
      },
      {
        "algorithm": "SHA-1",
        "revision": "1.0",
        "messageLength": [{
          "min": 0, "max": 65528, "increment": 8
        }],
        "performLargeDataTest": [1, 2, 4, 8]
      },
      {
        "algorithm": "ACVP-AES-XTS",
        "revision": "2.0",
        "direction": ["encrypt", "decrypt"],
        "keyLen": [256],
        "payloadLen": [1024],
        "tweakMode": ["number"],
        "dataUnitLenMatchesPayload": true
      },
      {
        "algorithm": "ACVP-AES-ECB",
        "revision": "1.0",
        "direction": ["encrypt", "decrypt"],
        "keyLen": [128, 192, 256]
      },
      {
        "algorithm": "ACVP-AES-CTR",
        "revision": "1.0",
        "direction": ["encrypt", "decrypt"],
        "keyLen": [128, 192, 256],
        "payloadLen": [{
          "min": 8, "max": 128, "increment": 8
        }],
        "incrementalCounter": true,
        "overflowCounter": true,
        "performCounterTests": true
      },
      {
        "algorithm": "ACVP-AES-CBC",
        "revision": "1.0",
        "direction": ["encrypt", "decrypt"],
        "keyLen": [128, 192, 256]
      },
      {
        "algorithm": "ACVP-AES-GCM",
        "revision": "1.0",
        "direction": ["encrypt", "decrypt"],
        "keyLen": [128, 192, 256],
        "payloadLen": [{
          "min": 0, "max": 65536, "increment": 8
        }],
        "aadLen": [{
          "min": 0, "max": 65536, "increment": 8
        }],
        "tagLen": [32, 64, 96, 104, 112, 120, 128],
        "ivLen": [96],
        "ivGen": ["external", "internal"],
        "ivGenMode": "8.2.2"
      },
      {
        "algorithm": "ACVP-AES-GMAC",
        "revision": "1.0",
        "direction": ["encrypt", "decrypt"],
        "keyLen": [128, 192, 256],
        "payloadLen": [{
          "min": 0, "max": 65536, "increment": 8
        }],
        "aadLen": [{
          "min": 0, "max": 65536, "increment": 8
        }],
        "tagLen": [32, 64, 96, 104, 112, 120, 128],
        "ivLen": [96],
        "ivGen": "external"
      },
      {
        "algorithm": "ACVP-AES-KW",
        "revision": "1.0",
        "direction": [
            "encrypt",
            "decrypt"
        ],
        "kwCipher": [
            "cipher"
        ],
        "keyLen": [
            128, 192, 256
        ],
        "payloadLen": [{"min": 128, "max": 4096, "increment": 64}]
      },
      {
        "algorithm": "ACVP-AES-KWP",
        "revision": "1.0",
        "direction": [
            "encrypt",
            "decrypt"
        ],
        "kwCipher": [
            "cipher"
        ],
        "keyLen": [
            128, 192, 256
        ],
        "payloadLen": [{"min": 8, "max": 4096, "increment": 8}]
      },
      {
        "algorithm": "ACVP-AES-CCM",
        "revision": "1.0",
        "direction": [
            "encrypt",
            "decrypt"
        ],
        "keyLen": [
            128
        ],
        "payloadLen": [{"min": 0, "max": 256, "increment": 8}],
        "ivLen": [104],
        "tagLen": [32, 64],
        "aadLen": [{"min": 0, "max": 524288, "increment": 8}]
      },
      {
        "algorithm": "HMAC-SHA-1",
        "revision": "1.0",
        "keyLen": [{
          "min": 8, "max": 524288, "increment": 8
        }],
        "macLen": [{
          "min": 32, "max": 160, "increment": 8
        }]
      },
      {
        "algorithm": "HMAC-SHA2-224",
        "revision": "1.0",
        "keyLen": [{
          "min": 8, "max": 524288, "increment": 8
        }],
        "macLen": [{
          "min": 32, "max": 224, "increment": 8
        }]
      },
      {
        "algorithm": "HMAC-SHA2-256",
        "revision": "1.0",
        "keyLen": [{
          "min": 8, "max": 524288, "increment": 8
        }],
        "macLen": [{
          "min": 32, "max": 256, "increment": 8
        }]
      },
      {
        "algorithm": "HMAC-SHA2-384",
        "revision": "1.0",
        "keyLen": [{
          "min": 8, "max": 524288, "increment": 8
        }],
        "macLen": [{
          "min": 32, "max": 384, "increment": 8
        }]
      },
      {
        "algorithm": "HMAC-SHA2-512",
        "revision": "1.0",
        "keyLen": [{
          "min": 8, "max": 524288, "increment": 8
        }],
        "macLen": [{
          "min": 32, "max": 512, "increment": 8
        }]
      },
      {
        "algorithm": "HMAC-SHA2-512/224",
        "revision": "1.0",
        "keyLen": [{
          "min": 8, "max": 524288, "increment": 8
        }],
        "macLen": [{
          "min": 32, "max": 224, "increment": 8
        }]
      },
      {
        "algorithm": "HMAC-SHA2-512/256",
        "revision": "1.0",
        "keyLen": [{
          "min": 8, "max": 524288, "increment": 8
        }],
        "macLen": [{
          "min": 32, "max": 256, "increment": 8
        }]
      },
      {
        "vsId": 0,
        "algorithm": "PBKDF",
        "revision": "1.0",
        "capabilities": [
          {
            "iterationCount": [
              {
                "min": 1,
                "max": 10000,
                "increment": 1
              }
            ],
            "passwordLen": [
              {
                "min": 8,
                "max": 64,
                "increment": 1
              }
            ],
            "saltLen": [
              {
                "min": 128,
                "max": 512,
                "increment": 8
              }
            ],
            "keyLen": [
              {
                "min": 112,
                "max": 2048,
                "increment": 8
              }
            ],
            "hmacAlg": [
              "SHA-1",
              "SHA2-224",
              "SHA2-256",
              "SHA2-384",
              "SHA2-512",
              "SHA2-512/224",
              "SHA2-512/256"
            ]
          }
        ]
      },
      {
        "algorithm": "ctrDRBG",
        "revision": "1.0",
        "predResistanceEnabled": [false],
        "reseedImplemented": true,
        "capabilities": [{
          "mode": "AES-256",
          "derFuncEnabled": false,
          "entropyInputLen": [384],
          "nonceLen": [0],
          "persoStringLen": [{"min": 0, "max": 384, "increment": 16}],
          "additionalInputLen": [
            {"min": 0, "max": 384, "increment": 16}
          ],
          "returnedBitsLen": 2048
        }]
      },
      {
        "algorithm": "ECDSA",
        "mode": "keyGen",
        "revision": "1.0",
        "curve": [
          "P-224",
          "P-256",
          "P-384",
          "P-521"
        ],
        "secretGenerationMode": [
          "testing candidates"
        ]
      },
      {
        "algorithm": "ECDSA",
        "mode": "keyVer",
        "revision": "1.0",
        "curve": [
          "P-224",
          "P-256",
          "P-384",
          "P-521"
        ]
      },
      {
        "algorithm": "ECDSA",
        "mode": "sigGen",
        "revision": "1.0",
        "capabilities": [{
          "curve": [
            "P-224",
            "P-256",
            "P-384",
            "P-521"
          ],
          "hashAlg": [
            "SHA2-224",
            "SHA2-256",
            "SHA2-384",
            "SHA2-512",
            "SHA2-512/224",
            "SHA2-512/256",
            "SHA3-224",
            "SHA3-256",
            "SHA3-384",
            "SHA3-512"
          ]
        }]
      },
      {
        "algorithm": "ECDSA",
        "mode": "sigVer",
        "revision": "1.0",
        "capabilities": [{
          "curve": [
            "P-224",
            "P-256",
            "P-384",
            "P-521"
          ],
          "hashAlg": [
            "SHA-1",
            "SHA2-224",
            "SHA2-256",
            "SHA2-384",
            "SHA2-512",
            "SHA2-512/224",
            "SHA2-512/256",
            "SHA3-224",
            "SHA3-256",
            "SHA3-384",
            "SHA3-512"
          ]
        }]
      },)"
      R"({
        "algorithm": "RSA",
        "mode": "keyGen",
        "revision": "FIPS186-5",
        "infoGeneratedByServer": true,
        "pubExpMode": "fixed",
        "fixedPubExp": "010001",
        "keyFormat": "standard",
        "capabilities": [{
          "randPQ": "probable",
          "properties": [{
              "modulo": 2048,
              "primeTest": [
                "2powSecStr"
              ],
              "pMod8": 0,
              "qMod8": 0
            },{
              "modulo": 3072,
              "primeTest": [
                "2powSecStr"
              ],
              "pMod8": 0,
              "qMod8": 0
            },{
              "modulo": 4096,
              "primeTest": [
                "2powSecStr"
              ],
              "pMod8": 0,
              "qMod8": 0
            },{
              "modulo": 6144,
              "primeTest": [
                "2powSecStr"
              ],
              "pMod8": 0,
              "qMod8": 0
            },{
              "modulo": 8192,
              "primeTest": [
                "2powSecStr"
              ],
              "pMod8": 0,
              "qMod8": 0
          }]
        }]
      },)"
      R"({
        "algorithm": "RSA",
        "mode": "sigGen",
        "revision": "FIPS186-5",
        "capabilities": [{
          "sigType": "pkcs1v1.5",
          "properties": [{
              "modulo": 2048,
              "hashPair": [{
                  "hashAlg": "SHA2-224"
                },{
                  "hashAlg": "SHA2-256"
                },{
                  "hashAlg": "SHA2-384"
                },{
                  "hashAlg": "SHA2-512"
                },{
                  "hashAlg": "SHA2-512/224"
                },{
                  "hashAlg": "SHA2-512/256"
                },{
                  "hashAlg": "SHA3-224"
                },{
                  "hashAlg": "SHA3-256"
                },{
                  "hashAlg": "SHA3-384"
                },{
                  "hashAlg": "SHA3-512"
              }]
            },{
              "modulo": 3072,
              "hashPair": [{
                  "hashAlg": "SHA2-224"
                },{
                  "hashAlg": "SHA2-256"
                },{
                  "hashAlg": "SHA2-384"
                },{
                  "hashAlg": "SHA2-512"
                },{
                  "hashAlg": "SHA2-512/224"
                },{
                  "hashAlg": "SHA2-512/256"
                },{
                  "hashAlg": "SHA3-224"
                },{
                  "hashAlg": "SHA3-256"
                },{
                  "hashAlg": "SHA3-384"
                },{
                  "hashAlg": "SHA3-512"
              }]
            },{
              "modulo": 4096,
              "hashPair": [{
                  "hashAlg": "SHA2-224"
                },{
                  "hashAlg": "SHA2-256"
                },{
                  "hashAlg": "SHA2-384"
                },{
                  "hashAlg": "SHA2-512"
                },{
                  "hashAlg": "SHA2-512/224"
                },{
                  "hashAlg": "SHA2-512/256"
                },{
                  "hashAlg": "SHA3-224"
                },{
                  "hashAlg": "SHA3-256"
                },{
                  "hashAlg": "SHA3-384"
                },{
                  "hashAlg": "SHA3-512"
              }]
            }]
          },{
            "sigType": "pss",
            "properties": [{
                "modulo": 2048,
                "maskFunction": ["mgf1"],
                "hashPair": [{
                    "hashAlg": "SHA2-224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA2-256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA2-384",
                    "saltLen": 48
                  },{
                    "hashAlg": "SHA2-512",
                    "saltLen": 64
                  },{
                    "hashAlg": "SHA2-512/224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA2-512/256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA3-224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA3-256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA3-384",
                    "saltLen": 48
                  },{
                    "hashAlg": "SHA3-512",
                    "saltLen": 64
                }]
              },{
                "modulo": 3072,
                "maskFunction": ["mgf1"],
                "hashPair": [{
                    "hashAlg": "SHA2-224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA2-256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA2-384",
                    "saltLen": 48
                  },{
                    "hashAlg": "SHA2-512",
                    "saltLen": 64
                  },{
                    "hashAlg": "SHA2-512/224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA2-512/256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA3-224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA3-256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA3-384",
                    "saltLen": 48
                  },{
                    "hashAlg": "SHA3-512",
                    "saltLen": 64
                }]
              },{
                "modulo": 4096,
                "maskFunction": ["mgf1"],
                "hashPair": [{
                    "hashAlg": "SHA2-224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA2-256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA2-384",
                    "saltLen": 48
                  },{
                    "hashAlg": "SHA2-512",
                    "saltLen": 64
                  },{
                    "hashAlg": "SHA2-512/224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA2-512/256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA3-224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA3-256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA3-384",
                    "saltLen": 48
                  },{
                    "hashAlg": "SHA3-512",
                    "saltLen": 64
                }]
            }]
        }]
      },)"
      R"({
        "algorithm": "RSA",
        "mode": "sigVer",
        "revision": "FIPS186-4",
        "pubExpMode": "fixed",
        "fixedPubExp": "010001",
        "capabilities": [{
            "sigType": "pkcs1v1.5",
            "properties": [{
                "modulo": 1024,
                "hashPair": [{
                    "hashAlg": "SHA-1"
                  },{
                    "hashAlg": "SHA2-224"
                  },{
                    "hashAlg": "SHA2-256"
                  },{
                    "hashAlg": "SHA2-384"
                  },{
                    "hashAlg": "SHA2-512"
                  },{
                    "hashAlg": "SHA2-512/224"
                  },{
                    "hashAlg": "SHA2-512/256"
                }]
              },{
                "modulo": 2048,
                "hashPair": [{
                    "hashAlg": "SHA-1"
                }]
              },{
                "modulo": 3072,
                "hashPair": [{
                    "hashAlg": "SHA-1"
                }]
              },{
                "modulo": 4096,
                "hashPair": [{
                    "hashAlg": "SHA-1"
                }]
            }]
          },{
            "sigType": "pss",
            "properties": [{
                "modulo": 1024,
                "hashPair": [{
                    "hashAlg": "SHA-1",
                    "saltLen": 20
                  },{
                    "hashAlg": "SHA2-224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA2-256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA2-384",
                    "saltLen": 48
                  },{
                    "hashAlg": "SHA2-512/224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA2-512/256",
                    "saltLen": 32
                }]
              },{
                "modulo": 2048,
                "hashPair": [{
                    "hashAlg": "SHA-1",
                    "saltLen": 20
                }]
              },{
                "modulo": 3072,
                "hashPair": [{
                    "hashAlg": "SHA-1",
                    "saltLen": 20
                }]
              },{
                "modulo": 4096,
                "hashPair": [{
                    "hashAlg": "SHA-1",
                    "saltLen": 20
                }]
            }]
        }]
      },)"
      R"({
        "algorithm": "RSA",
        "mode": "sigVer",
        "revision": "FIPS186-5",
        "pubExpMode": "fixed",
        "fixedPubExp": "010001",
        "capabilities": [{
            "sigType": "pkcs1v1.5",
            "properties": [{
                "modulo": 2048,
                "hashPair": [{
                    "hashAlg": "SHA2-224"
                  },{
                    "hashAlg": "SHA2-256"
                  },{
                    "hashAlg": "SHA2-384"
                  },{
                    "hashAlg": "SHA2-512"
                  },{
                    "hashAlg": "SHA2-512/224"
                  },{
                    "hashAlg": "SHA2-512/256"
                  },{
                    "hashAlg": "SHA3-224"
                  },{
                    "hashAlg": "SHA3-256"
                  },{
                    "hashAlg": "SHA3-384"
                  },{
                    "hashAlg": "SHA3-512"
                }]
              },{
                "modulo": 3072,
                "hashPair": [{
                    "hashAlg": "SHA2-224"
                  },{
                    "hashAlg": "SHA2-256"
                  },{
                    "hashAlg": "SHA2-384"
                  },{
                    "hashAlg": "SHA2-512"
                  },{
                    "hashAlg": "SHA2-512/224"
                  },{
                    "hashAlg": "SHA2-512/256"
                  },{
                    "hashAlg": "SHA3-224"
                  },{
                    "hashAlg": "SHA3-256"
                  },{
                    "hashAlg": "SHA3-384"
                  },{
                    "hashAlg": "SHA3-512"
                }]
              },{
                "modulo": 4096,
                "hashPair": [{
                    "hashAlg": "SHA2-224"
                  },{
                    "hashAlg": "SHA2-256"
                  },{
                    "hashAlg": "SHA2-384"
                  },{
                    "hashAlg": "SHA2-512"
                  },{
                    "hashAlg": "SHA2-512/224"
                  },{
                    "hashAlg": "SHA2-512/256"
                  },{
                    "hashAlg": "SHA3-224"
                  },{
                    "hashAlg": "SHA3-256"
                  },{
                    "hashAlg": "SHA3-384"
                  },{
                    "hashAlg": "SHA3-512"
                }]
            }]
          },{
            "sigType": "pss",
            "properties": [{
                "modulo": 2048,
                "maskFunction": ["mgf1"],
                "hashPair": [{
                    "hashAlg": "SHA2-224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA2-256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA2-384",
                    "saltLen": 48
                  },{
                    "hashAlg": "SHA2-512",
                    "saltLen": 64
                  },{
                    "hashAlg": "SHA2-512/224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA2-512/256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA3-224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA3-256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA3-384",
                    "saltLen": 48
                  },{
                    "hashAlg": "SHA3-512",
                    "saltLen": 64
                }]
              },{
                "modulo": 3072,
                "maskFunction": ["mgf1"],
                "hashPair": [{
                    "hashAlg": "SHA2-224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA2-256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA2-384",
                    "saltLen": 48
                  },{
                    "hashAlg": "SHA2-512",
                    "saltLen": 64
                  },{
                    "hashAlg": "SHA2-512/224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA2-512/256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA3-224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA3-256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA3-384",
                    "saltLen": 48
                  },{
                    "hashAlg": "SHA3-512",
                    "saltLen": 64
                }]
              },{
                "modulo": 4096,
                "maskFunction": ["mgf1"],
                "hashPair": [{
                    "hashAlg": "SHA2-224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA2-256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA2-384",
                    "saltLen": 48
                  },{
                    "hashAlg": "SHA2-512",
                    "saltLen": 64
                  },{
                    "hashAlg": "SHA2-512/224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA2-512/256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA3-224",
                    "saltLen": 28
                  },{
                    "hashAlg": "SHA3-256",
                    "saltLen": 32
                  },{
                    "hashAlg": "SHA3-384",
                    "saltLen": 48
                  },{
                    "hashAlg": "SHA3-512",
                    "saltLen": 64
                }]
            }]
        }]
      },)"
      R"({
        "algorithm": "CMAC-AES",
        "acvptoolTestOnly": true,
        "revision": "1.0",
        "capabilities": [{
          "direction": ["gen", "ver"],
          "msgLen": [{
            "min": 0,
            "max": 524288,
            "increment": 8
          }],
          "keyLen": [128, 256],
          "macLen": [{
            "min": 8,
            "max": 128,
            "increment": 8
          }]
        }]
      },
      {
        "algorithm": "KDF",
        "revision": "1.0",
        "capabilities": [{
          "kdfMode": "feedback",
          "macMode": [
            "HMAC-SHA-1",
            "HMAC-SHA2-224",
            "HMAC-SHA2-256",
            "HMAC-SHA2-384",
            "HMAC-SHA2-512",
            "HMAC-SHA2-512/224",
            "HMAC-SHA2-512/256"
          ],
          "customKeyInLength": 0,
          "supportedLengths": [{
            "min": 8,
            "max": 1024,
            "increment": 8
          }],
          "fixedDataOrder": ["after fixed data"],
          "counterLength": [8],
          "supportsEmptyIv": true,
          "requiresEmptyIv": true
        },{
          "kdfMode": "counter",
          "macMode": [
            "HMAC-SHA-1",
            "HMAC-SHA2-224",
            "HMAC-SHA2-256",
            "HMAC-SHA2-384",
            "HMAC-SHA2-512",
            "HMAC-SHA2-512/224",
            "HMAC-SHA2-512/256"
          ],
          "supportedLengths": [{
            "min": 8,
            "max": 4096,
            "increment": 8
          }],
          "fixedDataOrder": ["before fixed data"],
          "counterLength": [32]
        }]
      },
      {
        "algorithm": "kdf-components",
        "revision": "1.0",
        "mode": "tls",
        "tlsVersion": [
          "v1.0/1.1",
          "v1.2"
        ],
        "hashAlg": [
          "SHA2-256",
          "SHA2-384",
          "SHA2-512"
        ]
      },
      {
        "algorithm": "kdf-components",
        "mode": "ssh",
        "revision": "1.0",
        "isSample": true,
        "hashAlg": [
          "SHA-1",
          "SHA2-224",
          "SHA2-256",
          "SHA2-384",
          "SHA2-512"
        ],
        "cipher": [
          "TDES",
          "AES-128",
          "AES-192",
          "AES-256"
        ]
      },
      {
        "algorithm": "TLS-v1.2",
        "revision": "RFC7627",
        "mode": "KDF",
        "hashAlg": [
          "SHA2-256",
          "SHA2-384",
          "SHA2-512"
        ]
      },
      {
        "vsId": 0,
        "algorithm": "KDA",
        "mode": "HKDF",
        "revision": "Sp800-56Cr1",
        "isSample": true,
        "fixedInfoPattern": "uPartyInfo||vPartyInfo||l",
        "encoding": [
          "concatenation"
        ],
        "hmacAlg": [
          "SHA-1",
          "SHA2-224",
          "SHA2-256",
          "SHA2-384",
          "SHA2-512",
          "SHA2-512/224",
          "SHA2-512/256"
        ],
        "macSaltMethods": [
          "default",
          "random"
        ],
        "l": 1024,
        "z": [
          {
            "min": 224,
            "max": 65536,
            "increment": 8
          }
        ],
        "performMultiExpansionTests": false
      },
      {
        "algorithm": "KAS-ECC-SSC",
        "revision": "Sp800-56Ar3",
        "scheme": {
          "ephemeralUnified": {
            "kasRole": [
              "initiator",
              "responder"
            ]
          },
          "staticUnified": {
            "kasRole": [
              "initiator",
              "responder"
            ]
          }
        },
        "domainParameterGenerationMethods": [
          "P-224",
          "P-256",
          "P-384",
          "P-521"
        ]
      },
      {
        "algorithm": "KAS-FFC-SSC",
        "revision": "Sp800-56Ar3",
        "scheme": {
          "dhEphem": {
            "kasRole": [
              "initiator",
              "responder"
            ]
          }
        },
        "domainParameterGenerationMethods": [
          "FB",
          "FC"
        ]
      },
      {
        "algorithm": "KDA",
        "mode": "OneStep",
        "revision": "Sp800-56Cr2",
        "prereqVals": [],
        "auxFunctions": [
          {"auxFunctionName": "SHA-1"},
          {"auxFunctionName": "SHA2-224"},
          {"auxFunctionName": "SHA2-256"},
          {"auxFunctionName": "SHA2-384"},
          {"auxFunctionName": "SHA2-512"},
          {"auxFunctionName": "SHA2-512/224"},
          {"auxFunctionName": "SHA2-512/256"},
          {"auxFunctionName": "SHA3-224"},
          {"auxFunctionName": "SHA3-256"},
          {"auxFunctionName": "SHA3-384"},
          {"auxFunctionName": "SHA3-512"},
          {"auxFunctionName": "HMAC-SHA-1", "macSaltMethods": ["default", "random"]},
          {"auxFunctionName": "HMAC-SHA2-224", "macSaltMethods": ["default", "random"]},
          {"auxFunctionName": "HMAC-SHA2-256", "macSaltMethods": ["default", "random"]},
          {"auxFunctionName": "HMAC-SHA2-384", "macSaltMethods": ["default", "random"]},
          {"auxFunctionName": "HMAC-SHA2-512", "macSaltMethods": ["default", "random"]},
          {"auxFunctionName": "HMAC-SHA2-512/224", "macSaltMethods": ["default", "random"]},
          {"auxFunctionName": "HMAC-SHA2-512/256", "macSaltMethods": ["default", "random"]}
        ],
        "fixedInfoPattern": "uPartyInfo||vPartyInfo",
        "encoding": ["concatenation"],
        "z": [{"min": 224, "max": 8192, "increment": 8}],
        "l": 2048
      },)"
      R"({
        "algorithm": "ML-KEM",
        "mode": "keyGen",
        "revision": "FIPS203",
        "parameterSets": ["ML-KEM-512", "ML-KEM-768", "ML-KEM-1024"]
      },
      {
        "algorithm": "ML-KEM",
        "mode": "encapDecap",
        "revision": "FIPS203",
        "parameterSets": ["ML-KEM-512", "ML-KEM-768", "ML-KEM-1024"],
        "functions": ["encapsulation", "decapsulation"]
      },)"
      R"({
        "algorithm": "EDDSA",
        "mode": "keyGen",
        "revision": "1.0",
        "curve": ["ED-25519"]
      },{
        "algorithm": "EDDSA",
        "mode": "keyVer",
        "revision": "1.0",
        "curve": ["ED-25519"]
      },{
        "algorithm": "EDDSA",
        "mode": "sigGen",
        "revision": "1.0",
        "curve": ["ED-25519"],
        "pure": true,
        "preHash": true,
        "contextLength": [{"min": 0, "max": 255, "increment": 1}]
      },{
        "algorithm": "EDDSA",
        "mode": "sigVer",
        "revision": "1.0",
        "curve": ["ED-25519"],
        "pure": true,
        "preHash": true,
        "contextLength": [{"min": 0, "max": 255, "increment": 1}]
      },)"
      R"({
        "algorithm": "ML-DSA",
        "mode": "keyGen",
        "revision": "FIPS204",
        "parameterSets": ["ML-DSA-44", "ML-DSA-65", "ML-DSA-87"]
      },{
        "algorithm": "ML-DSA",
        "mode": "sigGen",
        "revision": "FIPS204",
        "capabilities": [
        {
          "parameterSets": [
            "ML-DSA-44",
            "ML-DSA-65",
            "ML-DSA-87"
          ],
          "messageLength": [
            {
              "min": 8,
              "max": 65536,
              "increment": 8
            }
          ]
        }
      ],
        "deterministic": [false],
        "externalMu": [
          true,
          false
        ],
        "signatureInterfaces": ["internal"]
      },{
        "algorithm": "ML-DSA",
        "mode": "sigVer",
        "revision": "FIPS204",
        "capabilities": [
        {
          "parameterSets": [
            "ML-DSA-44",
            "ML-DSA-65",
            "ML-DSA-87"
          ],
          "messageLength": [
            {
              "min": 8,
              "max": 65536,
              "increment": 8
            }
          ]
        }
      ],
        "deterministic": [false],
        "externalMu": [
          true,
          false
        ],
        "signatureInterfaces": ["internal"]
      }])";
  return write_reply({Span<const uint8_t>(
      reinterpret_cast<const uint8_t *>(kConfig), sizeof(kConfig) - 1)});
}

template <uint8_t *(*OneShotHash)(const uint8_t *, size_t, uint8_t *),
          size_t DigestLength>
static bool Hash(const Span<const uint8_t> args[], ReplyCallback write_reply) {
  uint8_t digest[DigestLength];
  OneShotHash(args[0].data(), args[0].size(), digest);
  return write_reply({Span<const uint8_t>(digest)});
}

template <const EVP_MD *(MDFunc)(), size_t DigestLength>
static bool HashSha3(const Span<const uint8_t> args[],
                     ReplyCallback write_reply) {
  uint8_t digest[DigestLength];
  const EVP_MD *md = MDFunc();
  unsigned int md_out_size = DigestLength;

  EVP_Digest(args[0].data(), args[0].size(), digest, &md_out_size, md, NULL);

  return write_reply({Span<const uint8_t>(digest)});
}

template <const EVP_MD *(MDFunc)()>
static bool HashXof(const Span<const uint8_t> args[],
                    ReplyCallback write_reply) {
  // NOTE: Max outLen supported by ACVP is 65536 bits (8192 bytes). If that
  //       changes, we'll need to use a bigger stack-allocated array size here.
  //       https://pages.nist.gov/ACVP/draft-celi-acvp-sha3.html#name-capabilities-registration
  uint8_t digest[8192];
  const EVP_MD *md = MDFunc();
  const uint8_t *outlen_bytes = args[1].data();
  // MD outLen is passed to modulewrapper as a length-4 byte array representing
  // a little-endian unsigned 32-bit integer.
  uint32_t md_out_size = CRYPTO_load_u32_le(outlen_bytes);

  EVP_Digest(args[0].data(), args[0].size(), digest, &md_out_size, md, NULL);

  return write_reply({Span<const uint8_t>(digest, md_out_size)});
}

template <uint8_t *(*OneShotHash)(const uint8_t *, size_t, uint8_t *),
          size_t DigestLength>
static bool HashMCT(const Span<const uint8_t> args[],
                    ReplyCallback write_reply) {
  if (args[0].size() != DigestLength) {
    return false;
  }

  uint8_t buf[DigestLength * 3];
  memcpy(buf, args[0].data(), DigestLength);
  memcpy(buf + DigestLength, args[0].data(), DigestLength);
  memcpy(buf + 2 * DigestLength, args[0].data(), DigestLength);

  for (size_t i = 0; i < 1000; i++) {
    uint8_t digest[DigestLength];
    OneShotHash(buf, sizeof(buf), digest);
    memmove(buf, buf + DigestLength, DigestLength * 2);
    memcpy(buf + DigestLength * 2, digest, DigestLength);
  }

  return write_reply(
      {Span<const uint8_t>(buf + 2 * DigestLength, DigestLength)});
}

template <const EVP_MD *(MDFunc)(), size_t DigestLength>
static bool HashMCTSha3(const Span<const uint8_t> args[],
                        ReplyCallback write_reply) {
  if (args[0].size() != DigestLength) {
    return false;
  }
  const EVP_MD *evp_md = MDFunc();
  unsigned int md_out_size = DigestLength;

  // The following logic conforms to the Monte Carlo tests described in
  // https://pages.nist.gov/ACVP/draft-celi-acvp-sha3.html#name-monte-carlo-tests-for-sha3-
  unsigned char md[1001][DigestLength];
  unsigned char msg[1001][DigestLength];

  memcpy(md[0], args[0].data(), DigestLength);

  for (size_t i = 1; i <= 1000; i++) {
    memcpy(msg[i], md[i - 1], DigestLength);
    EVP_Digest(msg[i], sizeof(msg[i]), md[i], &md_out_size, evp_md, NULL);
  }

  return write_reply({Span<const uint8_t>(md[1000])});
}

template <const EVP_MD *(MDFunc)()>
static bool HashMCTXof(const Span<const uint8_t> args[],
                       ReplyCallback write_reply) {
  const uint8_t *max_outlen_bytes = args[1].data();
  const uint8_t *min_outlen_bytes = args[2].data();
  const uint8_t *outlen_bytes = args[3].data();

  // The various output lens are passed to modulewrapper as a length-4 byte
  // array representing a little-endian unsigned 32-bit integer.
  uint32_t min_output_len = CRYPTO_load_u32_le(min_outlen_bytes);
  uint32_t max_output_len = CRYPTO_load_u32_le(max_outlen_bytes);
  uint32_t output_len = CRYPTO_load_u32_le(outlen_bytes);
  uint32_t range = max_output_len - min_output_len + 1;

  const size_t array_len = 1001;
  std::vector<std::vector<uint8_t>> md(array_len);
  std::vector<std::vector<uint8_t>> msg(array_len, std::vector<uint8_t>(16));

  // Zero out |msg| to clear any residual stack garbage before XOF computation
  for (size_t i = 0; i < array_len; i++) {
    OPENSSL_cleanse(msg[i].data(), 16 * sizeof(uint8_t));
  }

  // The following logic conforms to the SHAKE Monte Carlo tests described in
  // https://pages.nist.gov/ACVP/draft-celi-acvp-sha3.html#name-monte-carlo-tests-for-sha3-
  md[0].resize(args[0].size());
  memcpy(md[0].data(), args[0].data(), args[0].size());

  for (size_t i = 1; i < array_len; i++) {
    md[i].resize(output_len);

    size_t msg_size = std::min<size_t>(md[i - 1].size(), 16);
    memcpy(msg[i].data(), md[i - 1].data(), msg_size);

    EVP_Digest(msg[i].data(), msg[i].size(), md[i].data(), &output_len,
               MDFunc(), NULL);

    uint16_t rightmost_output_bits =
        (md[i][output_len - 2] << 8) | md[i][output_len - 1];
    output_len = min_output_len + (rightmost_output_bits % range);
  }

  // We're sending the new output len back to the ACVP tool as a length-4 byte
  // array representing a little-endian unsigned 32-bit integer as well.
  uint8_t new_outlen_bytes[4];
  CRYPTO_store_u32_le(new_outlen_bytes, output_len);

  return write_reply(
      {Span<const uint8_t>(md[1000]), Span<const uint8_t>(new_outlen_bytes)});
}

// The following logic conforms to the Large Data Tests described in
// https://pages.nist.gov/ACVP/draft-celi-acvp-sha.html#name-large-data-tests-for-sha-1-
// Which are the same for SHA-1, SHA2, and SHA3
static unsigned char *BuildLDTMessage(const bssl::Span<const uint8_t> part_msg,
                                      int times) {
  size_t full_msg_size = part_msg.size() * times;
  unsigned char *full_msg = (unsigned char *)malloc(full_msg_size);
  for (int i = 0; i < times; i++) {
    memcpy(full_msg + i * part_msg.size(), part_msg.data(), part_msg.size());
  }

  return full_msg;
}

template <uint8_t *(*OneShotHash)(const uint8_t *, size_t, uint8_t *),
          size_t DigestLength>
static bool HashLDT(const Span<const uint8_t> args[],
                    ReplyCallback write_reply) {
  uint8_t digest[DigestLength];
  int times;
  memcpy(&times, args[1].data(), sizeof(int));

  unsigned char *msg = BuildLDTMessage(args[0], times);

  OneShotHash(msg, args[0].size() * times, digest);
  free(msg);
  return write_reply({Span<const uint8_t>(digest)});
}

template <const EVP_MD *(MDFunc)(), size_t DigestLength>
static bool HashLDTSha3(const Span<const uint8_t> args[],
                        ReplyCallback write_reply) {
  uint8_t digest[DigestLength];
  const EVP_MD *md = MDFunc();
  unsigned int md_out_size = DigestLength;

  int times;
  memcpy(&times, args[1].data(), sizeof(int));

  unsigned char *msg = BuildLDTMessage(args[0], times);

  EVP_Digest(msg, args[0].size() * times, digest, &md_out_size, md, nullptr);
  free(msg);
  return write_reply({Span<const uint8_t>(digest)});
}

static uint32_t GetIterations(const Span<const uint8_t> iterations_bytes) {
  uint32_t iterations;
  if (iterations_bytes.size() != sizeof(iterations)) {
    LOG_ERROR(
        "Expected %u-byte input for number of iterations, but found %u "
        "bytes.\n",
        static_cast<unsigned>(sizeof(iterations)),
        static_cast<unsigned>(iterations_bytes.size()));
    abort();
  }

  memcpy(&iterations, iterations_bytes.data(), sizeof(iterations));
  if (iterations == 0 || iterations == UINT32_MAX) {
    LOG_ERROR("Invalid number of iterations: %x.\n",
              static_cast<unsigned>(iterations));
    abort();
  }

  return iterations;
}

template <int (*SetKey)(const uint8_t *key, unsigned bits, AES_KEY *out),
          void (*Block)(const uint8_t *in, uint8_t *out, const AES_KEY *key)>
static bool AES(const Span<const uint8_t> args[], ReplyCallback write_reply) {
  AES_KEY key;
  if (SetKey(args[0].data(), args[0].size() * 8, &key) != 0) {
    return false;
  }
  if (args[1].size() % AES_BLOCK_SIZE != 0) {
    return false;
  }
  std::vector<uint8_t> result(args[1].begin(), args[1].end());
  const uint32_t iterations = GetIterations(args[2]);

  std::vector<uint8_t> prev_result;
  for (uint32_t j = 0; j < iterations; j++) {
    if (j == iterations - 1) {
      prev_result = result;
    }

    for (size_t i = 0; i < args[1].size(); i += AES_BLOCK_SIZE) {
      Block(result.data() + i, result.data() + i, &key);
    }
  }

  return write_reply(
      {Span<const uint8_t>(result), Span<const uint8_t>(prev_result)});
}

template <bool Encrypt>
static bool AES_XTS(const Span<const uint8_t> args[],
                    ReplyCallback write_reply) {
  const EVP_CIPHER *cipher = EVP_aes_256_xts();

  std::vector<uint8_t> key(args[0].begin(), args[0].end());
  std::vector<uint8_t> plaintext(args[1].begin(), args[1].end());
  std::vector<uint8_t> iv(args[2].begin(), args[2].end());

  bssl::Span<const uint8_t> in = plaintext;
  std::vector<uint8_t> out(plaintext.size());

  bssl::ScopedEVP_CIPHER_CTX ctx;
  int len;

  ctx.Reset();
  if (Encrypt) {
    if (!EVP_EncryptInit_ex(ctx.get(), cipher, nullptr, key.data(),
                            iv.data())) {
      LOG_ERROR("Failed XTS encrypt setup");
      return false;
    }
    if (!EVP_EncryptUpdate(ctx.get(), out.data(), &len, in.data(), in.size())) {
      LOG_ERROR("Failed XTS encrypt");
      return false;
    }
  } else {
    if (!EVP_DecryptInit_ex(ctx.get(), cipher, nullptr, key.data(),
                            iv.data())) {
      LOG_ERROR("Failed XTS decrypt setup");
      return false;
    }
    if (!EVP_DecryptUpdate(ctx.get(), out.data(), &len, in.data(), in.size())) {
      LOG_ERROR("Failed XTS decrypt");
      return false;
    }
  }
  out.resize(len);
  return write_reply({Span<const uint8_t>(out)});
}

template <int (*SetKey)(const uint8_t *key, unsigned bits, AES_KEY *out),
          int Direction>
static bool AES_CBC(const Span<const uint8_t> args[],
                    ReplyCallback write_reply) {
  AES_KEY key;
  if (SetKey(args[0].data(), args[0].size() * 8, &key) != 0) {
    return false;
  }
  if (args[1].size() % AES_BLOCK_SIZE != 0 || args[1].empty() ||
      args[2].size() != AES_BLOCK_SIZE) {
    return false;
  }
  std::vector<uint8_t> input(args[1].begin(), args[1].end());
  std::vector<uint8_t> iv(args[2].begin(), args[2].end());
  const uint32_t iterations = GetIterations(args[3]);

  std::vector<uint8_t> result(input.size());
  std::vector<uint8_t> prev_result, prev_input;

  for (uint32_t j = 0; j < iterations; j++) {
    prev_result = result;
    if (j > 0) {
      if (Direction == AES_ENCRYPT) {
        iv = result;
      } else {
        iv = prev_input;
      }
    }

    // AES_cbc_encrypt will mutate the given IV, but we need it later.
    uint8_t iv_copy[AES_BLOCK_SIZE];
    memcpy(iv_copy, iv.data(), sizeof(iv_copy));
    AES_cbc_encrypt(input.data(), result.data(), input.size(), &key, iv_copy,
                    Direction);

    if (Direction == AES_DECRYPT) {
      prev_input = input;
    }

    if (j == 0) {
      input = iv;
    } else {
      input = prev_result;
    }
  }

  return write_reply(
      {Span<const uint8_t>(result), Span<const uint8_t>(prev_result)});
}

static bool AES_CTR(const Span<const uint8_t> args[],
                    ReplyCallback write_reply) {
  static const uint32_t kOneIteration = 1;
  if (args[3].size() != sizeof(kOneIteration) ||
      memcmp(args[3].data(), &kOneIteration, sizeof(kOneIteration))) {
    LOG_ERROR("Only a single iteration supported with AES-CTR\n");
    return false;
  }

  AES_KEY key;
  if (AES_set_encrypt_key(args[0].data(), args[0].size() * 8, &key) != 0) {
    return false;
  }
  if (args[2].size() != AES_BLOCK_SIZE) {
    return false;
  }
  uint8_t iv[AES_BLOCK_SIZE];
  memcpy(iv, args[2].data(), AES_BLOCK_SIZE);
  if (GetIterations(args[3]) != 1) {
    LOG_ERROR("Multiple iterations of AES-CTR is not supported.\n");
    return false;
  }

  std::vector<uint8_t> out;
  out.resize(args[1].size());
  unsigned num = 0;
  uint8_t ecount_buf[AES_BLOCK_SIZE];
  AES_ctr128_encrypt(args[1].data(), out.data(), args[1].size(), &key, iv,
                     ecount_buf, &num);
  return write_reply({Span<const uint8_t>(out)});
}

static bool AESGCMSetup(EVP_AEAD_CTX *ctx, Span<const uint8_t> tag_len_span,
                        Span<const uint8_t> key, Span<const uint8_t> nonce) {
  uint32_t tag_len_32;
  if (tag_len_span.size() != sizeof(tag_len_32)) {
    LOG_ERROR("Tag size value is %u bytes, not an uint32_t\n",
              static_cast<unsigned>(tag_len_span.size()));
    return false;
  }
  memcpy(&tag_len_32, tag_len_span.data(), sizeof(tag_len_32));

  const EVP_AEAD *aead;
  if (nonce.empty()) {
    // Internally generated IVs
    switch (key.size()) {
      case 16:
        aead = EVP_aead_aes_128_gcm_randnonce();
        break;
      case 32:
        aead = EVP_aead_aes_256_gcm_randnonce();
        break;
      default:
        LOG_ERROR("Bad AES-GCM key length %u\n",
                  static_cast<unsigned>(key.size()));
        return false;
    }
    // The 12-byte nonce is appended to the tag and is generated internally for
    // random nonce function. Thus, the "tag" must be extended by 12 bytes
    // for the purpose of the API.
    if (!EVP_AEAD_CTX_init(ctx, aead, key.data(), key.size(),
                           tag_len_32 + AES_GCM_NONCE_LENGTH, nullptr)) {
      LOG_ERROR("Failed to setup AES-GCM with tag length %u\n",
                static_cast<unsigned>(tag_len_32));
      return false;
    }
  } else {
    // External IVs
    switch (key.size()) {
      case 16:
        aead = EVP_aead_aes_128_gcm_tls12();
        break;
      case 24:
        aead = EVP_aead_aes_192_gcm();
        break;
      case 32:
        aead = EVP_aead_aes_256_gcm_tls12();
        break;
      default:
        LOG_ERROR("Bad AES-GCM key length %u\n",
                  static_cast<unsigned>(key.size()));
        return false;
    }
    if (!EVP_AEAD_CTX_init(ctx, aead, key.data(), key.size(), tag_len_32,
                           nullptr)) {
      LOG_ERROR("Failed to setup AES-GCM with tag length %u\n",
                static_cast<unsigned>(tag_len_32));
      return false;
    }
  }



  return true;
}

static bool AESCCMSetup(EVP_AEAD_CTX *ctx, Span<const uint8_t> tag_len_span,
                        Span<const uint8_t> key, Span<const uint8_t> nonce) {
  uint32_t tag_len_32;
  if (tag_len_span.size() != sizeof(tag_len_32)) {
    LOG_ERROR("Tag size value is %u bytes, not an uint32_t\n",
              static_cast<unsigned>(tag_len_span.size()));
    return false;
  }
  memcpy(&tag_len_32, tag_len_span.data(), sizeof(tag_len_32));
  const EVP_AEAD *aead;
  switch (tag_len_32) {
    case 4:
      aead = EVP_aead_aes_128_ccm_bluetooth();
      break;

    case 8:
      aead = EVP_aead_aes_128_ccm_bluetooth_8();
      break;

    default:
      LOG_ERROR(
          "AES-CCM only supports 4- and 8-byte tags, but %u was requested\n",
          static_cast<unsigned>(tag_len_32));
      return false;
  }

  if (key.size() != 16) {
    LOG_ERROR("AES-CCM only supports 128-bit keys, but %u bits were given\n",
              static_cast<unsigned>(key.size() * 8));
    return false;
  }

  if (!EVP_AEAD_CTX_init(ctx, aead, key.data(), key.size(), tag_len_32,
                         nullptr)) {
    LOG_ERROR("Failed to setup AES-CCM with tag length %u\n",
              static_cast<unsigned>(tag_len_32));
    return false;
  }

  return true;
}

template <bool (*SetupFunc)(EVP_AEAD_CTX *ctx, Span<const uint8_t> tag_len_span,
                            Span<const uint8_t> key, Span<const uint8_t> nonce)>
static bool AEADSeal(const Span<const uint8_t> args[],
                     ReplyCallback write_reply) {
  Span<const uint8_t> tag_len_span = args[0];
  Span<const uint8_t> key = args[1];
  Span<const uint8_t> plaintext = args[2];
  Span<const uint8_t> nonce = args[3];
  Span<const uint8_t> ad = args[4];

  bssl::ScopedEVP_AEAD_CTX ctx;
  if (!SetupFunc(ctx.get(), tag_len_span, key, nonce)) {
    return false;
  }

  if (EVP_AEAD_MAX_OVERHEAD + plaintext.size() < EVP_AEAD_MAX_OVERHEAD) {
    return false;
  }
  std::vector<uint8_t> out(EVP_AEAD_MAX_OVERHEAD + plaintext.size());

  size_t out_len;
  if (nonce.empty()) {
    // The nonce parameter when using Internal IV generation must be
    // zero-length.
    if (!EVP_AEAD_CTX_seal(ctx.get(), out.data(), &out_len, out.size(), nullptr,
                           0, plaintext.data(), plaintext.size(), ad.data(),
                           ad.size())) {
      return false;
    }
  } else {
    // External IV AEAD sealing.
    if (!EVP_AEAD_CTX_seal(ctx.get(), out.data(), &out_len, out.size(),
                           nonce.data(), nonce.size(), plaintext.data(),
                           plaintext.size(), ad.data(), ad.size())) {
      return false;
    }
  }

  out.resize(out_len);
  return write_reply({Span<const uint8_t>(out)});
}

template <bool (*SetupFunc)(EVP_AEAD_CTX *ctx, Span<const uint8_t> tag_len_span,
                            Span<const uint8_t> key, Span<const uint8_t> nonce)>
static bool AEADOpen(const Span<const uint8_t> args[],
                     ReplyCallback write_reply) {
  Span<const uint8_t> tag_len_span = args[0];
  Span<const uint8_t> key = args[1];
  Span<const uint8_t> ciphertext = args[2];
  Span<const uint8_t> nonce = args[3];
  Span<const uint8_t> ad = args[4];

  bssl::ScopedEVP_AEAD_CTX ctx;
  if (!SetupFunc(ctx.get(), tag_len_span, key, nonce)) {
    return false;
  }

  std::vector<uint8_t> out(ciphertext.size());
  size_t out_len;
  uint8_t success_flag[1] = {0};

  if (!EVP_AEAD_CTX_open(ctx.get(), out.data(), &out_len, out.size(),
                         nonce.data(), nonce.size(), ciphertext.data(),
                         ciphertext.size(), ad.data(), ad.size())) {
    return write_reply(
        {Span<const uint8_t>(success_flag), Span<const uint8_t>()});
  }

  out.resize(out_len);
  success_flag[0] = 1;
  return write_reply(
      {Span<const uint8_t>(success_flag), Span<const uint8_t>(out)});
}

static bool AESPaddedKeyWrapSetup(AES_KEY *out, bool decrypt,
                                  Span<const uint8_t> key) {
  if ((decrypt ? AES_set_decrypt_key : AES_set_encrypt_key)(
          key.data(), key.size() * 8, out) != 0) {
    LOG_ERROR("Invalid AES key length for AES-KW(P): %u\n",
              static_cast<unsigned>(key.size()));
    return false;
  }
  return true;
}

static bool AESKeyWrapSetup(AES_KEY *out, bool decrypt, Span<const uint8_t> key,
                            Span<const uint8_t> input) {
  if (!AESPaddedKeyWrapSetup(out, decrypt, key)) {
    return false;
  }

  if (input.size() % 8) {
    LOG_ERROR("Invalid AES-KW input length: %u\n",
              static_cast<unsigned>(input.size()));
    return false;
  }

  return true;
}

static bool AESKeyWrapSeal(const Span<const uint8_t> args[],
                           ReplyCallback write_reply) {
  Span<const uint8_t> key = args[1];
  Span<const uint8_t> plaintext = args[2];

  AES_KEY aes;
  if (!AESKeyWrapSetup(&aes, /*decrypt=*/false, key, plaintext) ||
      plaintext.size() > INT_MAX - 8) {
    return false;
  }

  std::vector<uint8_t> out(plaintext.size() + 8);
  if (AES_wrap_key(&aes, /*iv=*/nullptr, out.data(), plaintext.data(),
                   plaintext.size()) != static_cast<int>(out.size())) {
    LOG_ERROR("AES-KW failed\n");
    return false;
  }

  return write_reply({Span<const uint8_t>(out)});
}

static bool AESKeyWrapOpen(const Span<const uint8_t> args[],
                           ReplyCallback write_reply) {
  Span<const uint8_t> key = args[1];
  Span<const uint8_t> ciphertext = args[2];

  AES_KEY aes;
  if (!AESKeyWrapSetup(&aes, /*decrypt=*/true, key, ciphertext) ||
      ciphertext.size() < 8 || ciphertext.size() > INT_MAX) {
    return false;
  }

  std::vector<uint8_t> out(ciphertext.size() - 8);
  uint8_t success_flag[1] = {0};
  if (AES_unwrap_key(&aes, /*iv=*/nullptr, out.data(), ciphertext.data(),
                     ciphertext.size()) != static_cast<int>(out.size())) {
    return write_reply(
        {Span<const uint8_t>(success_flag), Span<const uint8_t>()});
  }

  success_flag[0] = 1;
  return write_reply(
      {Span<const uint8_t>(success_flag), Span<const uint8_t>(out)});
}

static bool AESPaddedKeyWrapSeal(const Span<const uint8_t> args[],
                                 ReplyCallback write_reply) {
  Span<const uint8_t> key = args[1];
  Span<const uint8_t> plaintext = args[2];

  AES_KEY aes;
  if (!AESPaddedKeyWrapSetup(&aes, /*decrypt=*/false, key) ||
      plaintext.size() + 15 < 15) {
    return false;
  }

  std::vector<uint8_t> out(plaintext.size() + 15);
  size_t out_len;
  if (!AES_wrap_key_padded(&aes, out.data(), &out_len, out.size(),
                           plaintext.data(), plaintext.size())) {
    LOG_ERROR("AES-KWP failed\n");
    return false;
  }

  out.resize(out_len);
  return write_reply({Span<const uint8_t>(out)});
}

static bool AESPaddedKeyWrapOpen(const Span<const uint8_t> args[],
                                 ReplyCallback write_reply) {
  Span<const uint8_t> key = args[1];
  Span<const uint8_t> ciphertext = args[2];

  AES_KEY aes;
  if (!AESPaddedKeyWrapSetup(&aes, /*decrypt=*/true, key) ||
      ciphertext.size() % 8) {
    return false;
  }

  std::vector<uint8_t> out(ciphertext.size());
  size_t out_len;
  uint8_t success_flag[1] = {0};
  if (!AES_unwrap_key_padded(&aes, out.data(), &out_len, out.size(),
                             ciphertext.data(), ciphertext.size())) {
    return write_reply(
        {Span<const uint8_t>(success_flag), Span<const uint8_t>()});
  }

  success_flag[0] = 1;
  out.resize(out_len);
  return write_reply(
      {Span<const uint8_t>(success_flag), Span<const uint8_t>(out)});
}

template <bool Encrypt>
static bool TDES(const Span<const uint8_t> args[], ReplyCallback write_reply) {
  const EVP_CIPHER *cipher = EVP_des_ede3();

  if (args[0].size() != 24) {
    LOG_ERROR("Bad key length %u for 3DES.\n",
              static_cast<unsigned>(args[0].size()));
    return false;
  }
  bssl::ScopedEVP_CIPHER_CTX ctx;
  if (!EVP_CipherInit_ex(ctx.get(), cipher, nullptr, args[0].data(), nullptr,
                         Encrypt ? 1 : 0) ||
      !EVP_CIPHER_CTX_set_padding(ctx.get(), 0)) {
    return false;
  }

  if (args[1].size() % 8) {
    LOG_ERROR("Bad input length %u for 3DES.\n",
              static_cast<unsigned>(args[1].size()));
    return false;
  }
  std::vector<uint8_t> result(args[1].begin(), args[1].end());

  const uint32_t iterations = GetIterations(args[2]);
  std::vector<uint8_t> prev_result, prev_prev_result;

  for (uint32_t j = 0; j < iterations; j++) {
    if (j == iterations - 1) {
      prev_result = result;
    } else if (iterations >= 2 && j == iterations - 2) {
      prev_prev_result = result;
    }

    int out_len;
    if (!EVP_CipherUpdate(ctx.get(), result.data(), &out_len, result.data(),
                          result.size()) ||
        out_len != static_cast<int>(result.size())) {
      return false;
    }
  }

  return write_reply({Span<const uint8_t>(result),
                      Span<const uint8_t>(prev_result),
                      Span<const uint8_t>(prev_prev_result)});
}

template <bool Encrypt>
static bool TDES_CBC(const Span<const uint8_t> args[],
                     ReplyCallback write_reply) {
  const EVP_CIPHER *cipher = EVP_des_ede3_cbc();

  if (args[0].size() != 24) {
    LOG_ERROR("Bad key length %u for 3DES.\n",
              static_cast<unsigned>(args[0].size()));
    return false;
  }

  if (args[1].size() % 8 || args[1].size() == 0) {
    LOG_ERROR("Bad input length %u for 3DES.\n",
              static_cast<unsigned>(args[1].size()));
    return false;
  }
  std::vector<uint8_t> input(args[1].begin(), args[1].end());

  if (args[2].size() != EVP_CIPHER_iv_length(cipher)) {
    LOG_ERROR("Bad IV length %u for 3DES.\n",
              static_cast<unsigned>(args[2].size()));
    return false;
  }
  std::vector<uint8_t> iv(args[2].begin(), args[2].end());
  const uint32_t iterations = GetIterations(args[3]);

  std::vector<uint8_t> result(input.size());
  std::vector<uint8_t> prev_result, prev_prev_result;
  bssl::ScopedEVP_CIPHER_CTX ctx;
  if (!EVP_CipherInit_ex(ctx.get(), cipher, nullptr, args[0].data(), iv.data(),
                         Encrypt ? 1 : 0) ||
      !EVP_CIPHER_CTX_set_padding(ctx.get(), 0)) {
    return false;
  }

  for (uint32_t j = 0; j < iterations; j++) {
    prev_prev_result = prev_result;
    prev_result = result;

    int out_len, out_len2;
    if (!EVP_CipherInit_ex(ctx.get(), nullptr, nullptr, nullptr, iv.data(),
                           -1) ||
        !EVP_CipherUpdate(ctx.get(), result.data(), &out_len, input.data(),
                          input.size()) ||
        !EVP_CipherFinal_ex(ctx.get(), result.data() + out_len, &out_len2) ||
        (out_len + out_len2) != static_cast<int>(result.size())) {
      return false;
    }

    if (Encrypt) {
      if (j == 0) {
        input = iv;
      } else {
        input = prev_result;
      }
      iv = result;
    } else {
      iv = input;
      input = result;
    }
  }

  return write_reply({Span<const uint8_t>(result),
                      Span<const uint8_t>(prev_result),
                      Span<const uint8_t>(prev_prev_result)});
}

template <const EVP_MD *HashFunc()>
static bool HMAC(const Span<const uint8_t> args[], ReplyCallback write_reply) {
  const EVP_MD *const md = HashFunc();

  // Approved HMAC computation
  uint8_t digest[EVP_MAX_MD_SIZE];
  unsigned digest_len;
  if (::HMAC(md, args[1].data(), args[1].size(), args[0].data(), args[0].size(),
             digest, &digest_len) == nullptr) {
    return false;
  }

  // HMAC computation with precomputed keys
  // The purpose of this call is to test |HMAC_set_precomputed_key_export| and
  // |HMAC_get_precomputed_key|, which are called by |HMAC_with_precompute|.
  uint8_t digest_with_precompute[EVP_MAX_MD_SIZE];
  unsigned digest_with_precompute_len;
  if (::HMAC_with_precompute(md, args[1].data(), args[1].size(), args[0].data(),
                             args[0].size(), digest_with_precompute,
                             &digest_with_precompute_len) == nullptr) {
    return false;
  }

  // The two HMAC computations must yield exactly the same results
  if (digest_len != digest_with_precompute_len ||
      memcmp(digest, digest_with_precompute, digest_len) != 0) {
    return false;
  }

  return write_reply({Span<const uint8_t>(digest, digest_len)});
}

template <bool WithReseed>
static bool DRBG(const Span<const uint8_t> args[], ReplyCallback write_reply) {
  const auto out_len_bytes = args[0];
  const auto entropy = args[1];
  const auto personalisation = args[2];

  Span<const uint8_t> reseed_additional_data, reseed_entropy, additional_data1,
      additional_data2, nonce;
  if (!WithReseed) {
    additional_data1 = args[3];
    additional_data2 = args[4];
    nonce = args[5];
  } else {
    reseed_additional_data = args[3];
    reseed_entropy = args[4];
    additional_data1 = args[5];
    additional_data2 = args[6];
    nonce = args[7];
  }

  uint32_t out_len;
  if (out_len_bytes.size() != sizeof(out_len) ||
      entropy.size() != CTR_DRBG_ENTROPY_LEN ||
      (!reseed_entropy.empty() &&
       reseed_entropy.size() != CTR_DRBG_ENTROPY_LEN) ||
      // nonces are not supported
      nonce.size() != 0) {
    return false;
  }
  memcpy(&out_len, out_len_bytes.data(), sizeof(out_len));
  if (out_len > (1 << 24)) {
    return false;
  }
  std::vector<uint8_t> out(out_len);

  CTR_DRBG_STATE drbg;
  if (!CTR_DRBG_init(&drbg, entropy.data(), personalisation.data(),
                     personalisation.size()) ||
      (!reseed_entropy.empty() &&
       !CTR_DRBG_reseed(&drbg, reseed_entropy.data(),
                        reseed_additional_data.data(),
                        reseed_additional_data.size())) ||
      !CTR_DRBG_generate(&drbg, out.data(), out_len, additional_data1.data(),
                         additional_data1.size()) ||
      !CTR_DRBG_generate(&drbg, out.data(), out_len, additional_data2.data(),
                         additional_data2.size())) {
    return false;
  }

  return write_reply({Span<const uint8_t>(out)});
}

static bool StringEq(Span<const uint8_t> a, const char *b) {
  const size_t len = strlen(b);
  return a.size() == len && memcmp(a.data(), b, len) == 0;
}

static bssl::UniquePtr<EC_KEY> ECKeyFromName(Span<const uint8_t> name) {
  int nid;
  if (StringEq(name, "P-224")) {
    nid = NID_secp224r1;
  } else if (StringEq(name, "P-256")) {
    nid = NID_X9_62_prime256v1;
  } else if (StringEq(name, "P-384")) {
    nid = NID_secp384r1;
  } else if (StringEq(name, "P-521")) {
    nid = NID_secp521r1;
  } else {
    return nullptr;
  }

  return bssl::UniquePtr<EC_KEY>(EC_KEY_new_by_curve_name(nid));
}

static std::vector<uint8_t> BIGNUMBytes(const BIGNUM *bn) {
  const size_t len = BN_num_bytes(bn);
  std::vector<uint8_t> ret(len);
  BN_bn2bin(bn, ret.data());
  return ret;
}

static std::pair<std::vector<uint8_t>, std::vector<uint8_t>> GetPublicKeyBytes(
    const EC_KEY *key) {
  bssl::UniquePtr<BIGNUM> x(BN_new());
  bssl::UniquePtr<BIGNUM> y(BN_new());
  if (!EC_POINT_get_affine_coordinates_GFp(EC_KEY_get0_group(key),
                                           EC_KEY_get0_public_key(key), x.get(),
                                           y.get(), /*ctx=*/nullptr)) {
    abort();
  }

  std::vector<uint8_t> x_bytes = BIGNUMBytes(x.get());
  std::vector<uint8_t> y_bytes = BIGNUMBytes(y.get());

  return std::make_pair(std::move(x_bytes), std::move(y_bytes));
}

static bool ECDSAKeyGen(const Span<const uint8_t> args[],
                        ReplyCallback write_reply) {
  bssl::UniquePtr<EC_KEY> key = ECKeyFromName(args[0]);
  if (!key || !EC_KEY_generate_key_fips(key.get())) {
    return false;
  }

  const auto pub_key = GetPublicKeyBytes(key.get());
  std::vector<uint8_t> d_bytes =
      BIGNUMBytes(EC_KEY_get0_private_key(key.get()));

  return write_reply({Span<const uint8_t>(d_bytes),
                      Span<const uint8_t>(pub_key.first),
                      Span<const uint8_t>(pub_key.second)});
}

static bssl::UniquePtr<BIGNUM> BytesToBIGNUM(Span<const uint8_t> bytes) {
  bssl::UniquePtr<BIGNUM> bn(BN_new());
  BN_bin2bn(bytes.data(), bytes.size(), bn.get());
  return bn;
}

static bool ECDSAKeyVer(const Span<const uint8_t> args[],
                        ReplyCallback write_reply) {
  bssl::UniquePtr<EC_KEY> key = ECKeyFromName(args[0]);
  if (!key) {
    return false;
  }

  bssl::UniquePtr<BIGNUM> x(BytesToBIGNUM(args[1]));
  bssl::UniquePtr<BIGNUM> y(BytesToBIGNUM(args[2]));

  bssl::UniquePtr<EC_POINT> point(EC_POINT_new(EC_KEY_get0_group(key.get())));
  uint8_t reply[1];
  if (!EC_POINT_set_affine_coordinates_GFp(EC_KEY_get0_group(key.get()),
                                           point.get(), x.get(), y.get(),
                                           /*ctx=*/nullptr) ||
      !EC_KEY_set_public_key(key.get(), point.get()) ||
      !EC_KEY_check_fips(key.get())) {
    reply[0] = 0;
  } else {
    reply[0] = 1;
  }

  return write_reply({Span<const uint8_t>(reply)});
}

static const EVP_MD *HashFromName(Span<const uint8_t> name) {
  if (StringEq(name, "SHA-1")) {
    return EVP_sha1();
  } else if (StringEq(name, "SHA2-224")) {
    return EVP_sha224();
  } else if (StringEq(name, "SHA2-256")) {
    return EVP_sha256();
  } else if (StringEq(name, "SHA2-384")) {
    return EVP_sha384();
  } else if (StringEq(name, "SHA2-512")) {
    return EVP_sha512();
  } else if (StringEq(name, "SHA2-512/224")) {
    return EVP_sha512_224();
  } else if (StringEq(name, "SHA2-512/256")) {
    return EVP_sha512_256();
  } else if (StringEq(name, "SHA3-224")) {
    return EVP_sha3_224();
  } else if (StringEq(name, "SHA3-256")) {
    return EVP_sha3_256();
  } else if (StringEq(name, "SHA3-384")) {
    return EVP_sha3_384();
  } else if (StringEq(name, "SHA3-512")) {
    return EVP_sha3_512();
  } else if (StringEq(name, "SHAKE-128")) {
    return EVP_shake128();
  } else if (StringEq(name, "SHAKE-256")) {
    return EVP_shake256();
  } else {
    return nullptr;
  }
}

static bool ECDSASigGen(const Span<const uint8_t> args[],
                        ReplyCallback write_reply) {
  bssl::UniquePtr<EC_KEY> key = ECKeyFromName(args[0]);
  bssl::UniquePtr<BIGNUM> d = BytesToBIGNUM(args[1]);
  const EVP_MD *hash = HashFromName(args[2]);
  auto msg = args[3];
  if (!key || !hash || !EC_KEY_set_private_key(key.get(), d.get())) {
    return false;
  }
  bssl::ScopedEVP_MD_CTX ctx;
  EVP_PKEY_CTX *pctx;
  bssl::UniquePtr<EVP_PKEY> evp_pkey(EVP_PKEY_new());
  if (!evp_pkey || !EVP_PKEY_set1_EC_KEY(evp_pkey.get(), key.get())) {
    return false;
  }
  std::vector<uint8_t> sig_der;
  size_t len;
  if (!EVP_DigestSignInit(ctx.get(), &pctx, hash, nullptr, evp_pkey.get()) ||
      !EVP_DigestSign(ctx.get(), nullptr, &len, msg.data(), msg.size())) {
    return false;
  }
  sig_der.resize(len);
  if (!EVP_DigestSign(ctx.get(), sig_der.data(), &len, msg.data(),
                      msg.size())) {
    return false;
  }
  bssl::UniquePtr<ECDSA_SIG> sig(ECDSA_SIG_from_bytes(sig_der.data(), len));
  if (!sig) {
    return false;
  }

  std::vector<uint8_t> r_bytes(BIGNUMBytes(sig->r));
  std::vector<uint8_t> s_bytes(BIGNUMBytes(sig->s));

  return write_reply(
      {Span<const uint8_t>(r_bytes), Span<const uint8_t>(s_bytes)});
}

static bool ECDSASigVer(const Span<const uint8_t> args[],
                        ReplyCallback write_reply) {
  bssl::UniquePtr<EC_KEY> key = ECKeyFromName(args[0]);
  const EVP_MD *hash = HashFromName(args[1]);
  auto msg = args[2];
  bssl::UniquePtr<BIGNUM> x(BytesToBIGNUM(args[3]));
  bssl::UniquePtr<BIGNUM> y(BytesToBIGNUM(args[4]));
  bssl::UniquePtr<BIGNUM> r(BytesToBIGNUM(args[5]));
  bssl::UniquePtr<BIGNUM> s(BytesToBIGNUM(args[6]));
  ECDSA_SIG sig;
  sig.r = r.get();
  sig.s = s.get();
  uint8_t *der;
  size_t der_len;
  if (!key || !hash || !ECDSA_SIG_to_bytes(&der, &der_len, &sig)) {
    return false;
  }
  // Let |delete_der| manage the release of |der|.
  bssl::UniquePtr<uint8_t> delete_der(der);
  bssl::UniquePtr<EC_POINT> point(EC_POINT_new(EC_KEY_get0_group(key.get())));
  if (!EC_POINT_set_affine_coordinates_GFp(EC_KEY_get0_group(key.get()),
                                           point.get(), x.get(), y.get(),
                                           /*ctx=*/nullptr) ||
      !EC_KEY_set_public_key(key.get(), point.get()) ||
      !EC_KEY_check_fips(key.get())) {
    return false;
  }
  bssl::ScopedEVP_MD_CTX ctx;
  EVP_PKEY_CTX *pctx;
  bssl::UniquePtr<EVP_PKEY> evp_pkey(EVP_PKEY_new());
  if (!evp_pkey || !EVP_PKEY_set1_EC_KEY(evp_pkey.get(), key.get())) {
    return false;
  }
  uint8_t reply[1];
  if (!EVP_DigestVerifyInit(ctx.get(), &pctx, hash, nullptr, evp_pkey.get()) ||
      !EVP_DigestVerify(ctx.get(), der, der_len, msg.data(), msg.size())) {
    reply[0] = 0;
  } else {
    reply[0] = 1;
  }
  ERR_clear_error();

  return write_reply({Span<const uint8_t>(reply)});
}

static bool CMAC_AES(const Span<const uint8_t> args[],
                     ReplyCallback write_reply) {
  uint8_t mac[16];
  if (!AES_CMAC(mac, args[1].data(), args[1].size(), args[2].data(),
                args[2].size())) {
    return false;
  }

  uint32_t mac_len;
  if (args[0].size() != sizeof(mac_len)) {
    return false;
  }
  memcpy(&mac_len, args[0].data(), sizeof(mac_len));
  if (mac_len > sizeof(mac)) {
    return false;
  }

  return write_reply({Span<const uint8_t>(mac, mac_len)});
}

static bool CMAC_AESVerify(const Span<const uint8_t> args[],
                           ReplyCallback write_reply) {
  // This function is just for testing since libcrypto doesn't do the
  // verification itself. The regcap doesn't advertise "ver" support.
  uint8_t mac[16];
  if (!AES_CMAC(mac, args[0].data(), args[0].size(), args[1].data(),
                args[1].size()) ||
      args[2].size() > sizeof(mac)) {
    return false;
  }

  const uint8_t ok = (OPENSSL_memcmp(mac, args[2].data(), args[2].size()) == 0);
  return write_reply({Span<const uint8_t>(&ok, sizeof(ok))});
}

static std::map<unsigned, bssl::UniquePtr<EVP_PKEY>> &CachedRSAEVPKeys() {
  static std::map<unsigned, bssl::UniquePtr<EVP_PKEY>> keys;
  return keys;
}

static EVP_PKEY *AddRSAKeyToCache(bssl::UniquePtr<RSA> &rsa, unsigned bits) {
  bssl::UniquePtr<EVP_PKEY> evp_pkey(EVP_PKEY_new());
  if (!evp_pkey || !EVP_PKEY_set1_RSA(evp_pkey.get(), rsa.get())) {
    return nullptr;
  }

  EVP_PKEY *const ret = evp_pkey.get();
  CachedRSAEVPKeys().emplace(static_cast<unsigned>(bits), std::move(evp_pkey));
  return ret;
}

static EVP_PKEY *GetRSAKey(unsigned bits) {
  auto it = CachedRSAEVPKeys().find(bits);
  if (it != CachedRSAEVPKeys().end()) {
    return it->second.get();
  }

  bssl::UniquePtr<RSA> rsa(RSA_new());
  if (!RSA_generate_key_fips(rsa.get(), bits, nullptr)) {
    abort();
  }

  return AddRSAKeyToCache(rsa, bits);
}

static bool RSAKeyGen(const Span<const uint8_t> args[],
                      ReplyCallback write_reply) {
  uint32_t bits;
  if (args[0].size() != sizeof(bits)) {
    return false;
  }
  memcpy(&bits, args[0].data(), sizeof(bits));

  bssl::UniquePtr<RSA> rsa(RSA_new());
  if (!RSA_generate_key_fips(rsa.get(), bits, nullptr)) {
    LOG_ERROR("RSA_generate_key_fips failed for modulus length %u.\n", bits);
    return false;
  }

  const BIGNUM *n, *e, *d, *p, *q;
  RSA_get0_key(rsa.get(), &n, &e, &d);
  RSA_get0_factors(rsa.get(), &p, &q);

  if (!write_reply({BIGNUMBytes(e), BIGNUMBytes(p), BIGNUMBytes(q),
                    BIGNUMBytes(n), BIGNUMBytes(d)})) {
    return false;
  }

  if (AddRSAKeyToCache(rsa, bits) == nullptr) {
    return false;
  }
  return true;
}

template <const EVP_MD *(MDFunc)(), bool UsePSS>
static bool RSASigGen(const Span<const uint8_t> args[],
                      ReplyCallback write_reply) {
  uint32_t bits;
  if (args[0].size() != sizeof(bits)) {
    return false;
  }
  memcpy(&bits, args[0].data(), sizeof(bits));
  const Span<const uint8_t> msg = args[1];
  EVP_PKEY *const evp_pkey = GetRSAKey(bits);
  if (evp_pkey == nullptr) {
    return false;
  }
  RSA *const rsa = EVP_PKEY_get0_RSA(evp_pkey);
  if (rsa == nullptr) {
    return false;
  }
  const EVP_MD *const md = MDFunc();
  std::vector<uint8_t> sig;
  size_t sig_len;
  bssl::ScopedEVP_MD_CTX ctx;
  EVP_PKEY_CTX *pctx;
  int padding = UsePSS ? RSA_PKCS1_PSS_PADDING : RSA_PKCS1_PADDING;
  if (!EVP_DigestSignInit(ctx.get(), &pctx, md, nullptr, evp_pkey) ||
      !EVP_PKEY_CTX_set_rsa_padding(pctx, padding) ||
      (UsePSS &&
       !EVP_PKEY_CTX_set_rsa_pss_saltlen(pctx, RSA_PSS_SALTLEN_DIGEST)) ||
      !EVP_DigestSign(ctx.get(), nullptr, &sig_len, msg.data(), msg.size())) {
    return false;
  }
  sig.resize(sig_len);
  if (!EVP_DigestSign(ctx.get(), sig.data(), &sig_len, msg.data(),
                      msg.size())) {
    return false;
  }

  return write_reply(
      {BIGNUMBytes(RSA_get0_n(rsa)), BIGNUMBytes(RSA_get0_e(rsa)), sig});
}

template <const EVP_MD *(MDFunc)(), bool UsePSS>
static bool RSASigVer(const Span<const uint8_t> args[],
                      ReplyCallback write_reply) {
  const Span<const uint8_t> n_bytes = args[0];
  const Span<const uint8_t> e_bytes = args[1];
  const Span<const uint8_t> msg = args[2];
  const Span<const uint8_t> sig = args[3];

  BIGNUM *n = BN_new();
  BIGNUM *e = BN_new();
  bssl::UniquePtr<RSA> key(RSA_new());
  if (!BN_bin2bn(n_bytes.data(), n_bytes.size(), n) ||
      !BN_bin2bn(e_bytes.data(), e_bytes.size(), e) ||
      !RSA_set0_key(key.get(), n, e, /*d=*/nullptr)) {
    return false;
  }

  const EVP_MD *const md = MDFunc();
  bssl::ScopedEVP_MD_CTX ctx;
  EVP_PKEY_CTX *pctx;
  bssl::UniquePtr<EVP_PKEY> evp_pkey(EVP_PKEY_new());
  if (!evp_pkey || !EVP_PKEY_set1_RSA(evp_pkey.get(), key.get())) {
    return false;
  }
  uint8_t ok;
  int padding = UsePSS ? RSA_PKCS1_PSS_PADDING : RSA_PKCS1_PADDING;
  if (!EVP_DigestVerifyInit(ctx.get(), &pctx, md, nullptr, evp_pkey.get()) ||
      !EVP_PKEY_CTX_set_rsa_padding(pctx, padding) ||
      (UsePSS &&
       !EVP_PKEY_CTX_set_rsa_pss_saltlen(pctx, RSA_PSS_SALTLEN_DIGEST)) ||
      !EVP_DigestVerify(ctx.get(), sig.data(), sig.size(), msg.data(),
                        msg.size())) {
    ok = 0;
  } else {
    ok = 1;
  }
  ERR_clear_error();

  return write_reply({Span<const uint8_t>(&ok, 1)});
}

template <const EVP_MD *(MDFunc)()>
static bool TLSKDF(const Span<const uint8_t> args[],
                   ReplyCallback write_reply) {
  const Span<const uint8_t> out_len_bytes = args[0];
  const Span<const uint8_t> secret = args[1];
  const Span<const uint8_t> label = args[2];
  const Span<const uint8_t> seed1 = args[3];
  const Span<const uint8_t> seed2 = args[4];
  const EVP_MD *md = MDFunc();

  uint32_t out_len;
  if (out_len_bytes.size() != sizeof(out_len)) {
    return 0;
  }
  memcpy(&out_len, out_len_bytes.data(), sizeof(out_len));

  std::vector<uint8_t> out(static_cast<size_t>(out_len));
  if (!CRYPTO_tls1_prf(md, out.data(), out.size(), secret.data(), secret.size(),
                       reinterpret_cast<const char *>(label.data()),
                       label.size(), seed1.data(), seed1.size(), seed2.data(),
                       seed2.size())) {
    return 0;
  }

  return write_reply({out});
}

template <int Nid>
static bool ECDH(const Span<const uint8_t> args[], ReplyCallback write_reply) {
  bssl::UniquePtr<BIGNUM> their_x(BytesToBIGNUM(args[0]));
  bssl::UniquePtr<BIGNUM> their_y(BytesToBIGNUM(args[1]));
  const Span<const uint8_t> private_key = args[2];

  bssl::UniquePtr<EC_KEY> ec_key(EC_KEY_new_by_curve_name(Nid));
  bssl::UniquePtr<BN_CTX> ctx(BN_CTX_new());

  const EC_GROUP *const group = EC_KEY_get0_group(ec_key.get());
  bssl::UniquePtr<EC_POINT> their_point(EC_POINT_new(group));
  if (!EC_POINT_set_affine_coordinates_GFp(
          group, their_point.get(), their_x.get(), their_y.get(), ctx.get())) {
    LOG_ERROR("Invalid peer point for ECDH.\n");
    return false;
  }

  if (!private_key.empty()) {
    bssl::UniquePtr<BIGNUM> our_k(BytesToBIGNUM(private_key));
    if (!EC_KEY_set_private_key(ec_key.get(), our_k.get())) {
      LOG_ERROR("EC_KEY_set_private_key failed.\n");
      return false;
    }

    bssl::UniquePtr<EC_POINT> our_pub(EC_POINT_new(group));
    if (!EC_POINT_mul(group, our_pub.get(), our_k.get(), nullptr, nullptr,
                      ctx.get()) ||
        !EC_KEY_set_public_key(ec_key.get(), our_pub.get())) {
      LOG_ERROR("Calculating public key failed.\n");
      return false;
    }
  } else if (!EC_KEY_generate_key_fips(ec_key.get())) {
    LOG_ERROR("EC_KEY_generate_key_fips failed.\n");
    return false;
  }

  // The output buffer is one larger than |EC_MAX_BYTES| so that truncation
  // can be detected.
  std::vector<uint8_t> output(EC_MAX_BYTES + 1);
  const int out_len =
      ECDH_compute_key(output.data(), output.size(), their_point.get(),
                       ec_key.get(), /*kdf=*/nullptr);
  if (out_len < 0) {
    LOG_ERROR("ECDH_compute_key failed.\n");
    return false;
  } else if (static_cast<size_t>(out_len) == output.size()) {
    LOG_ERROR("ECDH_compute_key output may have been truncated.\n");
    return false;
  }
  output.resize(static_cast<size_t>(out_len));

  const EC_POINT *pub = EC_KEY_get0_public_key(ec_key.get());
  bssl::UniquePtr<BIGNUM> x(BN_new());
  bssl::UniquePtr<BIGNUM> y(BN_new());
  if (!EC_POINT_get_affine_coordinates_GFp(group, pub, x.get(), y.get(),
                                           ctx.get())) {
    LOG_ERROR("EC_POINT_get_affine_coordinates_GFp failed.\n");
    return false;
  }

  return write_reply({BIGNUMBytes(x.get()), BIGNUMBytes(y.get()), output});
}

static bool FFDH(const Span<const uint8_t> args[], ReplyCallback write_reply) {
  bssl::UniquePtr<BIGNUM> p(BytesToBIGNUM(args[0]));
  bssl::UniquePtr<BIGNUM> q(BytesToBIGNUM(args[1]));
  bssl::UniquePtr<BIGNUM> g(BytesToBIGNUM(args[2]));
  bssl::UniquePtr<BIGNUM> their_pub(BytesToBIGNUM(args[3]));
  const Span<const uint8_t> private_key_span = args[4];
  const Span<const uint8_t> public_key_span = args[5];

  bssl::UniquePtr<DH> dh(DH_new());
  if (!DH_set0_pqg(dh.get(), p.get(), q.get(), g.get())) {
    LOG_ERROR("DH_set0_pqg failed.\n");
    return 0;
  }

  // DH_set0_pqg took ownership of these values.
  p.release();
  q.release();
  g.release();

  if (!private_key_span.empty()) {
    bssl::UniquePtr<BIGNUM> private_key(BytesToBIGNUM(private_key_span));
    bssl::UniquePtr<BIGNUM> public_key(BytesToBIGNUM(public_key_span));

    if (!DH_set0_key(dh.get(), public_key.get(), private_key.get())) {
      LOG_ERROR("DH_set0_key failed.\n");
      return 0;
    }

    // DH_set0_key took ownership of these values.
    public_key.release();
    private_key.release();
  } else if (!DH_generate_key(dh.get())) {
    LOG_ERROR("DH_generate_key failed.\n");
    return false;
  }

  std::vector<uint8_t> z(DH_size(dh.get()));
  if (DH_compute_key_padded(z.data(), their_pub.get(), dh.get()) !=
      static_cast<int>(z.size())) {
    LOG_ERROR("DH_compute_key_hashed failed.\n");
    return false;
  }

  return write_reply({BIGNUMBytes(DH_get0_pub_key(dh.get())), z});
}

static bool PBKDF(const Span<const uint8_t> args[], ReplyCallback write_reply) {
  const Span<const uint8_t> password = args[0];
  const Span<const uint8_t> salt = args[1];
  const Span<const uint8_t> iterations = args[2];
  const Span<const uint8_t> hmac_name = args[3];
  const Span<const uint8_t> key_len = args[4];

  // Read bit data into useable variables
  unsigned int iterations_uint;
  memcpy(&iterations_uint, iterations.data(), sizeof(iterations_uint));
  unsigned int key_len_uint;
  memcpy(&key_len_uint, key_len.data(), sizeof(key_len_uint));

  key_len_uint = key_len_uint / 8;

  // Get the SHA algorithm we want from the name provided to us
  const EVP_MD *hmac_alg = HashFromName(hmac_name);

  std::vector<uint8_t> out_key(key_len_uint);
  if (!PKCS5_PBKDF2_HMAC(reinterpret_cast<const char *>(password.data()),
                         password.size(), salt.data(), salt.size(),
                         iterations_uint, hmac_alg, key_len_uint,
                         out_key.data())) {
    return false;
  }

  return write_reply({Span<const uint8_t>(out_key)});
}

template <const EVP_MD *(MDFunc)()>
static bool HKDF(const Span<const uint8_t> args[], ReplyCallback write_reply) {
  const Span<const uint8_t> key = args[0];
  const Span<const uint8_t> salt = args[1];
  const Span<const uint8_t> info = args[2];
  const Span<const uint8_t> out_bytes = args[3];
  const EVP_MD *md = MDFunc();

  unsigned int out_bytes_uint;
  memcpy(&out_bytes_uint, out_bytes.data(), sizeof(out_bytes_uint));


  std::vector<uint8_t> out_key(out_bytes_uint);
  if (!::HKDF(out_key.data(), out_bytes_uint, md, key.data(), key.size(),
              salt.data(), salt.size(), info.data(), info.size())) {
    return false;
  }

  return write_reply({Span<const uint8_t>(out_key)});
}

template <const EVP_MD *(MDFunc)()>
static bool SSKDF_DIGEST(const Span<const uint8_t> args[],
                         ReplyCallback write_reply) {
  const Span<const uint8_t> key = args[0];
  const Span<const uint8_t> info = args[1];
  const Span<const uint8_t> out_bytes = args[2];
  const EVP_MD *md = MDFunc();

  uint32_t out_bytes_uint32;
  memcpy(&out_bytes_uint32, out_bytes.data(), sizeof(out_bytes_uint32));

  std::vector<uint8_t> out_key(out_bytes_uint32);
  if (!::SSKDF_digest(out_key.data(), out_bytes_uint32, md, key.data(),
                      key.size(), info.data(), info.size())) {
    return false;
  }

  return write_reply({Span<const uint8_t>(out_key)});
}

template <const EVP_MD *(MDFunc)()>
static bool SSKDF_HMAC(const Span<const uint8_t> args[],
                       ReplyCallback write_reply) {
  const Span<const uint8_t> key = args[0];
  const Span<const uint8_t> salt = args[1];
  const Span<const uint8_t> info = args[2];
  const Span<const uint8_t> out_bytes = args[3];
  const EVP_MD *md = MDFunc();

  uint32_t out_bytes_uint32;
  memcpy(&out_bytes_uint32, out_bytes.data(), sizeof(out_bytes_uint32));

  std::vector<uint8_t> out_key(out_bytes_uint32);
  if (!::SSKDF_hmac(out_key.data(), out_bytes_uint32, md, key.data(),
                    key.size(), info.data(), info.size(), salt.data(),
                    salt.size())) {
    return false;
  }

  return write_reply({Span<const uint8_t>(out_key)});
}

template <const EVP_MD *(MDFunc)(), char type_val>
static bool SSHKDF(const Span<const uint8_t> args[],
                   ReplyCallback write_reply) {
  const Span<const uint8_t> key = args[0];
  const Span<const uint8_t> hash = args[1];
  const Span<const uint8_t> session_id = args[2];
  const Span<const uint8_t> out_bytes = args[3];
  const EVP_MD *md = MDFunc();


  unsigned int out_bytes_uint;
  memcpy(&out_bytes_uint, out_bytes.data(), sizeof(out_bytes_uint));

  std::vector<uint8_t> out(out_bytes_uint);
  if (!::SSHKDF(md, key.data(), key.size(), hash.data(), hash.size(),
                session_id.data(), session_id.size(), type_val, out.data(),
                out_bytes_uint)) {
    return false;
  }

  return write_reply({Span<const uint8_t>(out)});
}

template <const EVP_MD *(MDFunc)()>
static bool HKDF_expand(const Span<const uint8_t> args[],
                        ReplyCallback write_reply) {
  const Span<const uint8_t> out_bytes = args[0];
  const Span<const uint8_t> key_in = args[1];
  const Span<const uint8_t> fixed_data = args[2];
  const EVP_MD *md = MDFunc();

  unsigned int out_bytes_uint;
  memcpy(&out_bytes_uint, out_bytes.data(), sizeof(out_bytes_uint));

  std::vector<uint8_t> out(out_bytes_uint);
  if (!::HKDF_expand(out.data(), out_bytes_uint, md, key_in.data(),
                     key_in.size(), fixed_data.data(), fixed_data.size())) {
    return false;
  }

  return write_reply({Span<const uint8_t>(out)});
}

template <const EVP_MD *(MDFunc)()>
static bool KBKDF_CTR_HMAC(const Span<const uint8_t> args[],
                           ReplyCallback write_reply) {
  const Span<const uint8_t> out_bytes = args[0];
  const Span<const uint8_t> key_in = args[1];
  const Span<const uint8_t> fixed_data = args[2];
  const EVP_MD *md = MDFunc();

  unsigned int out_bytes_uint;
  memcpy(&out_bytes_uint, out_bytes.data(), sizeof(out_bytes_uint));

  std::vector<uint8_t> out(out_bytes_uint);
  if (!::KBKDF_ctr_hmac(out.data(), out_bytes_uint, md, key_in.data(),
                        key_in.size(), fixed_data.data(), fixed_data.size())) {
    return false;
  }

  return write_reply({Span<const uint8_t>(out)});
}

template <int nid>
static bool ML_KEM_KEYGEN(const Span<const uint8_t> args[],
                          ReplyCallback write_reply) {
  const Span<const uint8_t> d = args[0];
  const Span<const uint8_t> z = args[1];

  std::vector<uint8_t> seed(d.size() + z.size());
  std::memcpy(seed.data(), d.data(), d.size());
  std::memcpy(seed.data() + d.size(), z.data(), z.size());

  EVP_PKEY *raw = NULL;
  size_t seed_len = 0;

  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new_id(EVP_PKEY_KEM, nullptr));
  if (!EVP_PKEY_CTX_kem_set_params(ctx.get(), nid) ||
      !EVP_PKEY_keygen_init(ctx.get()) ||
      !EVP_PKEY_keygen_deterministic(ctx.get(), NULL, NULL, &seed_len) ||
      seed_len != seed.size() ||
      !EVP_PKEY_keygen_deterministic(ctx.get(), &raw, seed.data(), &seed_len)) {
    return false;
  }
  bssl::UniquePtr<EVP_PKEY> pkey(raw);

  size_t decaps_key_size = 0;
  size_t encaps_key_size = 0;

  if (!EVP_PKEY_get_raw_private_key(pkey.get(), nullptr, &decaps_key_size) ||
      !EVP_PKEY_get_raw_public_key(pkey.get(), nullptr, &encaps_key_size)) {
    return false;
  }

  std::vector<uint8_t> decaps_key(decaps_key_size);
  std::vector<uint8_t> encaps_key(encaps_key_size);

  if (!EVP_PKEY_get_raw_private_key(pkey.get(), decaps_key.data(),
                                    &decaps_key_size) ||
      !EVP_PKEY_get_raw_public_key(pkey.get(), encaps_key.data(),
                                   &encaps_key_size)) {
    return false;
  }

  return write_reply({Span<const uint8_t>(encaps_key.data(), encaps_key_size),
                      Span<const uint8_t>(decaps_key.data(), decaps_key_size)});
}

template <int nid>
static bool ML_KEM_ENCAP(const Span<const uint8_t> args[],
                         ReplyCallback write_reply) {
  const Span<const uint8_t> ek = args[0];
  const Span<const uint8_t> m = args[1];

  bssl::UniquePtr<EVP_PKEY> pkey(
      EVP_PKEY_kem_new_raw_public_key(nid, ek.data(), ek.size()));
  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new(pkey.get(), nullptr));

  size_t ciphertext_len = 0;
  size_t shared_secret_len = 0;
  size_t seed_len = 0;
  if (!EVP_PKEY_encapsulate_deterministic(ctx.get(), nullptr, &ciphertext_len,
                                          nullptr, &shared_secret_len, nullptr,
                                          &seed_len) ||
      seed_len != m.size()) {
    return false;
  }

  std::vector<uint8_t> ciphertext(ciphertext_len);
  std::vector<uint8_t> shared_secret(shared_secret_len);

  if (!EVP_PKEY_encapsulate_deterministic(
          ctx.get(), ciphertext.data(), &ciphertext_len, shared_secret.data(),
          &shared_secret_len, m.data(), &seed_len)) {
    return false;
  }

  return write_reply(
      {Span<const uint8_t>(ciphertext.data(), ciphertext_len),
       Span<const uint8_t>(shared_secret.data(), shared_secret_len)});
}

template <int nid>
static bool ML_KEM_DECAP(const Span<const uint8_t> args[],
                         ReplyCallback write_reply) {
  const Span<const uint8_t> dk = args[0];
  const Span<const uint8_t> c = args[1];

  bssl::UniquePtr<EVP_PKEY> pkey(
      EVP_PKEY_kem_new_raw_secret_key(nid, dk.data(), dk.size()));
  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new(pkey.get(), nullptr));

  size_t shared_secret_len = 0;
  if (!EVP_PKEY_decapsulate(ctx.get(), nullptr, &shared_secret_len, c.data(),
                            c.size())) {
    return false;
  }

  std::vector<uint8_t> shared_secret(shared_secret_len);

  if (!EVP_PKEY_decapsulate(ctx.get(), shared_secret.data(), &shared_secret_len,
                            c.data(), c.size())) {
    return false;
  }

  return write_reply(
      {Span<const uint8_t>(shared_secret.data(), shared_secret_len)});
}

static bool ED25519KeyGen(const Span<const uint8_t> args[],
                          ReplyCallback write_reply) {
  std::vector<uint8_t> private_key(ED25519_PRIVATE_KEY_LEN);
  std::vector<uint8_t> public_key(ED25519_PUBLIC_KEY_LEN);
  ::ED25519_keypair(public_key.data(), private_key.data());
  const Span<uint8_t> seed(private_key.data(), ED25519_PRIVATE_KEY_SEED_LEN);
  return write_reply({seed, Span<const uint8_t>(public_key)});
}

static bool ED25519KeyVer(const Span<const uint8_t> args[],
                          ReplyCallback write_reply) {
  const Span<const uint8_t> public_key = args[0];

  uint8_t reply[1] = {0};
  if (::ED25519_check_public_key(public_key.data())) {
    reply[0] = 1;
  } else {
    ERR_clear_error();
  }

  return write_reply({Span<const uint8_t>(reply)});
}

static bool ED25519SigGen(const Span<const uint8_t> args[],
                          ReplyCallback write_reply) {
  const Span<const uint8_t> seed = args[0];
  const Span<const uint8_t> message = args[1];

  std::vector<uint8_t> private_key(ED25519_PRIVATE_KEY_LEN);
  std::vector<uint8_t> public_key(ED25519_PUBLIC_KEY_LEN);
  std::vector<uint8_t> signature(ED25519_SIGNATURE_LEN);

  ::ED25519_keypair_from_seed(public_key.data(), private_key.data(),
                              seed.data());

  if (!::ED25519_sign(signature.data(), message.data(), message.size(),
                      private_key.data())) {
    return false;
  }

  return write_reply({Span<const uint8_t>(signature)});
}

static bool ED25519SigVer(const Span<const uint8_t> args[],
                          ReplyCallback write_reply) {
  const Span<const uint8_t> message = args[0];
  const Span<const uint8_t> public_key = args[1];
  const Span<const uint8_t> signature = args[2];

  uint8_t reply[1] = {0};
  if (::ED25519_verify(message.data(), message.size(), signature.data(),
                       public_key.data())) {
    reply[0] = 1;
  } else {
    ERR_clear_error();
  }

  return write_reply({Span<const uint8_t>(reply)});
}

static bool ED25519phSigGen(const Span<const uint8_t> args[],
                            ReplyCallback write_reply) {
  const Span<const uint8_t> seed = args[0];
  const Span<const uint8_t> message = args[1];
  const Span<const uint8_t> context = args[2];

  std::vector<uint8_t> private_key(ED25519_PRIVATE_KEY_LEN);
  std::vector<uint8_t> public_key(ED25519_PUBLIC_KEY_LEN);
  std::vector<uint8_t> signature(ED25519_SIGNATURE_LEN);

  ::ED25519_keypair_from_seed(public_key.data(), private_key.data(),
                              seed.data());

  if (!::ED25519ph_sign(signature.data(), message.data(), message.size(),
                        private_key.data(), context.data(), context.size())) {
    return false;
  }

  return write_reply({Span<const uint8_t>(signature)});
}

static bool ED25519phSigVer(const Span<const uint8_t> args[],
                            ReplyCallback write_reply) {
  const Span<const uint8_t> message = args[0];
  const Span<const uint8_t> public_key = args[1];
  const Span<const uint8_t> signature = args[2];
  const Span<const uint8_t> context = args[3];

  uint8_t reply[1] = {0};
  if (::ED25519ph_verify(message.data(), message.size(), signature.data(),
                         public_key.data(), context.data(), context.size())) {
    reply[0] = 1;
  } else {
    ERR_clear_error();
  }

  return write_reply({Span<const uint8_t>(reply)});
}

template <int nid>
static bool ML_DSA_KEYGEN(const Span<const uint8_t> args[],
                          ReplyCallback write_reply) {
  const Span<const uint8_t> seed = args[0];

  //init params of the correct size based on provided nid
  ml_dsa_params params;
  if (nid == NID_MLDSA44) {
    ml_dsa_44_params_init(&params);
  }
  else if (nid == NID_MLDSA65) {
    ml_dsa_65_params_init(&params);
  }
  else if (nid == NID_MLDSA87) {
    ml_dsa_87_params_init(&params);
  }

  // create public and private key buffers
  std::vector<uint8_t> public_key(params.public_key_bytes);
  std::vector<uint8_t> private_key(params.secret_key_bytes);

  // generate the keys
  if (nid == NID_MLDSA44) {
    if (!ml_dsa_44_keypair_internal(public_key.data(), private_key.data(), seed.data())) {
      return false;
    }
  }
  else if (nid == NID_MLDSA65) {
    if (!ml_dsa_65_keypair_internal(public_key.data(), private_key.data(), seed.data())) {
      return false;
    }
  }
  else if (nid == NID_MLDSA87) {
    if (!ml_dsa_87_keypair_internal(public_key.data(), private_key.data(), seed.data())) {
      return false;
    }
  }
  return write_reply({Span<const uint8_t>(public_key.data(), public_key.size()),
                      Span<const uint8_t>(private_key.data(), private_key.size())});
}

template <int nid>
static bool ML_DSA_SIGGEN(const Span<const uint8_t> args[],
                         ReplyCallback write_reply) {
  const Span<const uint8_t> sk = args[0];
  const Span<const uint8_t> msg = args[1];
  const Span<const uint8_t> mu = args[2];
  const Span<const uint8_t> rnd = args[3];
  const Span<const uint8_t> extmu = args[4];

  ml_dsa_params params;
  if (nid == NID_MLDSA44) {
    ml_dsa_44_params_init(&params);
  }
  else if (nid == NID_MLDSA65) {
    ml_dsa_65_params_init(&params);
  }
  else if (nid == NID_MLDSA87) {
    ml_dsa_87_params_init(&params);
  }

  size_t signature_len = params.bytes;
  std::vector<uint8_t> signature(signature_len);

  // generate the signatures raw sign mode
  if (extmu.data()[0] == 0) {
    if (nid == NID_MLDSA44) {
      if (!ml_dsa_44_sign_internal(sk.data(), signature.data(), &signature_len,
                                   msg.data(), msg.size(), nullptr, 0, rnd.data())) {
        return false;
      }
    }
    else if (nid == NID_MLDSA65) {
      if (!ml_dsa_65_sign_internal(sk.data(), signature.data(), &signature_len,
                                   msg.data(), msg.size(), nullptr, 0, rnd.data())) {
        return false;
      }
    }
    else if (nid == NID_MLDSA87) {
      if (!ml_dsa_87_sign_internal(sk.data(), signature.data(), &signature_len,
                                   msg.data(), msg.size(), nullptr, 0, rnd.data())) {
        return false;
      }
    }
  }
  // generate the signatures digest sign mode (externalmu)
  else {
    if (nid == NID_MLDSA44) {
      if (!ml_dsa_extmu_44_sign_internal(sk.data(), signature.data(), &signature_len,
                                         mu.data(), mu.size(), nullptr, 0, rnd.data())) {
        return false;
      }
    }
    else if (nid == NID_MLDSA65) {
      if (!ml_dsa_extmu_65_sign_internal(sk.data(), signature.data(), &signature_len,
                                         mu.data(), mu.size(), nullptr, 0, rnd.data())) {
        return false;
      }
    }
    else if (nid == NID_MLDSA87) {
      if (!ml_dsa_extmu_87_sign_internal(sk.data(), signature.data(), &signature_len,
                                         mu.data(), mu.size(), nullptr, 0, rnd.data())) {
        return false;
      }
    }
  }

  return write_reply({Span<const uint8_t>(signature)});
}

template <int nid>
static bool ML_DSA_SIGVER(const Span<const uint8_t> args[], ReplyCallback write_reply) {
  const Span<const uint8_t> sig = args[0];
  const Span<const uint8_t> pk = args[1];
  const Span<const uint8_t> msg = args[2];
  const Span<const uint8_t> mu = args[3];
  const Span<const uint8_t> extmu = args[4];

  uint8_t reply[1] = {0};

  // verify the signatures raw sign mode
  if (extmu.data()[0] == 0) {
    if (nid == NID_MLDSA44) {
      if (ml_dsa_44_verify_internal(pk.data(), sig.data(), sig.size(), msg.data(),
                                    msg.size(), nullptr, 0)) {
        reply[0] = 1;
      }
    }
    else if (nid == NID_MLDSA65) {
      if (ml_dsa_65_verify_internal(pk.data(), sig.data(), sig.size(), msg.data(),
                                    msg.size(), nullptr, 0)) {
        reply[0] = 1;
      }
    }
    else if (nid == NID_MLDSA87) {
      if (ml_dsa_87_verify_internal(pk.data(), sig.data(), sig.size(), msg.data(),
                                    msg.size(), nullptr, 0)) {
        reply[0] = 1;
      }
    }
  }
  // verify the signatures digest sign mode (externalmu)
  else{
    if (nid == NID_MLDSA44) {
      if (ml_dsa_extmu_44_verify_internal(pk.data(), sig.data(), sig.size(), mu.data(),
                                          mu.size(), nullptr, 0)) {
        reply[0] = 1;
      }
    }
    else if (nid == NID_MLDSA65) {
      if (ml_dsa_extmu_65_verify_internal(pk.data(), sig.data(), sig.size(), mu.data(),
                                          mu.size(), nullptr, 0)) {
        reply[0] = 1;
      }
    }
    else if (nid == NID_MLDSA87) {
      if (ml_dsa_extmu_87_verify_internal(pk.data(), sig.data(), sig.size(), mu.data(),
                                          mu.size(), nullptr, 0)) {
        reply[0] = 1;
       }
    }
  }
  return write_reply({Span<const uint8_t>(reply)});
}

static struct {
  char name[kMaxNameLength + 1];
  uint8_t num_expected_args;
  bool (*handler)(const Span<const uint8_t> args[], ReplyCallback write_reply);
} kFunctions[] = {
    {"getConfig", 0, GetConfig},
    {"SHA-1", 1, Hash<SHA1, SHA_DIGEST_LENGTH>},
    {"SHA2-224", 1, Hash<SHA224, SHA224_DIGEST_LENGTH>},
    {"SHA2-256", 1, Hash<SHA256, SHA256_DIGEST_LENGTH>},
    {"SHA2-384", 1, Hash<SHA384, SHA384_DIGEST_LENGTH>},
    {"SHA2-512", 1, Hash<SHA512, SHA512_DIGEST_LENGTH>},
    {"SHA2-512/224", 1, Hash<SHA512_224, SHA512_224_DIGEST_LENGTH>},
    {"SHA2-512/256", 1, Hash<SHA512_256, SHA512_256_DIGEST_LENGTH>},
    {"SHA3-224", 1, HashSha3<EVP_sha3_224, SHA224_DIGEST_LENGTH>},
    {"SHA3-256", 1, HashSha3<EVP_sha3_256, SHA256_DIGEST_LENGTH>},
    {"SHA3-384", 1, HashSha3<EVP_sha3_384, SHA384_DIGEST_LENGTH>},
    {"SHA3-512", 1, HashSha3<EVP_sha3_512, SHA512_DIGEST_LENGTH>},
    {"SHAKE-128", 2, HashXof<EVP_shake128>},
    {"SHAKE-256", 2, HashXof<EVP_shake256>},
    {"SHA-1/MCT", 1, HashMCT<SHA1, SHA_DIGEST_LENGTH>},
    {"SHA2-224/MCT", 1, HashMCT<SHA224, SHA224_DIGEST_LENGTH>},
    {"SHA2-256/MCT", 1, HashMCT<SHA256, SHA256_DIGEST_LENGTH>},
    {"SHA2-384/MCT", 1, HashMCT<SHA384, SHA384_DIGEST_LENGTH>},
    {"SHA2-512/MCT", 1, HashMCT<SHA512, SHA512_DIGEST_LENGTH>},
    {"SHA2-512/224/MCT", 1, HashMCT<SHA512_224, SHA512_224_DIGEST_LENGTH>},
    {"SHA2-512/256/MCT", 1, HashMCT<SHA512_256, SHA512_256_DIGEST_LENGTH>},
    {"SHA3-224/MCT", 1, HashMCTSha3<EVP_sha3_224, SHA224_DIGEST_LENGTH>},
    {"SHA3-256/MCT", 1, HashMCTSha3<EVP_sha3_256, SHA256_DIGEST_LENGTH>},
    {"SHA3-384/MCT", 1, HashMCTSha3<EVP_sha3_384, SHA384_DIGEST_LENGTH>},
    {"SHA3-512/MCT", 1, HashMCTSha3<EVP_sha3_512, SHA512_DIGEST_LENGTH>},
    {"SHAKE-128/MCT", 4, HashMCTXof<EVP_shake128>},
    {"SHAKE-256/MCT", 4, HashMCTXof<EVP_shake256>},
    {"SHA-1/LDT", 2, HashLDT<SHA1, SHA_DIGEST_LENGTH>},
    {"SHA2-224/LDT", 2, HashLDT<SHA224, SHA224_DIGEST_LENGTH>},
    {"SHA2-256/LDT", 2, HashLDT<SHA256, SHA256_DIGEST_LENGTH>},
    {"SHA2-384/LDT", 2, HashLDT<SHA384, SHA384_DIGEST_LENGTH>},
    {"SHA2-512/LDT", 2, HashLDT<SHA512, SHA512_DIGEST_LENGTH>},
    {"SHA2-512/224/LDT", 2, HashLDT<SHA512_224, SHA512_224_DIGEST_LENGTH>},
    {"SHA2-512/256/LDT", 2, HashLDT<SHA512_256, SHA512_256_DIGEST_LENGTH>},
    {"SHA3-224/LDT", 2, HashLDTSha3<EVP_sha3_224, SHA224_DIGEST_LENGTH>},
    {"SHA3-256/LDT", 2, HashLDTSha3<EVP_sha3_256, SHA256_DIGEST_LENGTH>},
    {"SHA3-384/LDT", 2, HashLDTSha3<EVP_sha3_384, SHA384_DIGEST_LENGTH>},
    {"SHA3-512/LDT", 2, HashLDTSha3<EVP_sha3_512, SHA512_DIGEST_LENGTH>},
    {"AES/encrypt", 3, AES<AES_set_encrypt_key, AES_encrypt>},
    {"AES/decrypt", 3, AES<AES_set_decrypt_key, AES_decrypt>},
    {"AES-XTS/encrypt", 3, AES_XTS<true>},
    {"AES-XTS/decrypt", 3, AES_XTS<false>},
    {"AES-CBC/encrypt", 4, AES_CBC<AES_set_encrypt_key, AES_ENCRYPT>},
    {"AES-CBC/decrypt", 4, AES_CBC<AES_set_decrypt_key, AES_DECRYPT>},
    {"AES-CTR/encrypt", 4, AES_CTR},
    {"AES-CTR/decrypt", 4, AES_CTR},
    {"AES-GCM/seal", 5, AEADSeal<AESGCMSetup>},
    {"AES-GCM/open", 5, AEADOpen<AESGCMSetup>},
    {"AES-KW/seal", 5, AESKeyWrapSeal},
    {"AES-KW/open", 5, AESKeyWrapOpen},
    {"AES-KWP/seal", 5, AESPaddedKeyWrapSeal},
    {"AES-KWP/open", 5, AESPaddedKeyWrapOpen},
    {"AES-CCM/seal", 5, AEADSeal<AESCCMSetup>},
    {"AES-CCM/open", 5, AEADOpen<AESCCMSetup>},
    {"3DES-ECB/encrypt", 3, TDES<true>},
    {"3DES-ECB/decrypt", 3, TDES<false>},
    {"3DES-CBC/encrypt", 4, TDES_CBC<true>},
    {"3DES-CBC/decrypt", 4, TDES_CBC<false>},
    {"HMAC-SHA-1", 2, HMAC<EVP_sha1>},
    {"HMAC-SHA2-224", 2, HMAC<EVP_sha224>},
    {"HMAC-SHA2-256", 2, HMAC<EVP_sha256>},
    {"HMAC-SHA2-384", 2, HMAC<EVP_sha384>},
    {"HMAC-SHA2-512", 2, HMAC<EVP_sha512>},
    {"HMAC-SHA2-512/224", 2, HMAC<EVP_sha512_224>},
    {"HMAC-SHA2-512/256", 2, HMAC<EVP_sha512_256>},
    {"ctrDRBG/AES-256", 6, DRBG<false>},
    {"ctrDRBG-reseed/AES-256", 8, DRBG<true>},
    {"ECDSA/keyGen", 1, ECDSAKeyGen},
    {"ECDSA/keyVer", 3, ECDSAKeyVer},
    {"ECDSA/sigGen", 4, ECDSASigGen},
    {"ECDSA/sigVer", 7, ECDSASigVer},
    {"CMAC-AES", 3, CMAC_AES},
    {"CMAC-AES/verify", 3, CMAC_AESVerify},
    {"RSA/keyGen", 1, RSAKeyGen},
    {"RSA/sigGen/SHA3-224/pkcs1v1.5", 2, RSASigGen<EVP_sha3_224, false>},
    {"RSA/sigGen/SHA3-256/pkcs1v1.5", 2, RSASigGen<EVP_sha3_256, false>},
    {"RSA/sigGen/SHA3-384/pkcs1v1.5", 2, RSASigGen<EVP_sha3_384, false>},
    {"RSA/sigGen/SHA3-512/pkcs1v1.5", 2, RSASigGen<EVP_sha3_512, false>},
    {"RSA/sigGen/SHA2-224/pkcs1v1.5", 2, RSASigGen<EVP_sha224, false>},
    {"RSA/sigGen/SHA2-256/pkcs1v1.5", 2, RSASigGen<EVP_sha256, false>},
    {"RSA/sigGen/SHA2-384/pkcs1v1.5", 2, RSASigGen<EVP_sha384, false>},
    {"RSA/sigGen/SHA2-512/pkcs1v1.5", 2, RSASigGen<EVP_sha512, false>},
    {"RSA/sigGen/SHA2-512/224/pkcs1v1.5", 2, RSASigGen<EVP_sha512_224, false>},
    {"RSA/sigGen/SHA2-512/256/pkcs1v1.5", 2, RSASigGen<EVP_sha512_256, false>},
    {"RSA/sigGen/SHA-1/pkcs1v1.5", 2, RSASigGen<EVP_sha1, false>},
    {"RSA/sigGen/SHA3-224/pss", 2, RSASigGen<EVP_sha3_224, true>},
    {"RSA/sigGen/SHA3-256/pss", 2, RSASigGen<EVP_sha3_256, true>},
    {"RSA/sigGen/SHA3-384/pss", 2, RSASigGen<EVP_sha3_384, true>},
    {"RSA/sigGen/SHA3-512/pss", 2, RSASigGen<EVP_sha3_512, true>},
    {"RSA/sigGen/SHA2-224/pss", 2, RSASigGen<EVP_sha224, true>},
    {"RSA/sigGen/SHA2-256/pss", 2, RSASigGen<EVP_sha256, true>},
    {"RSA/sigGen/SHA2-384/pss", 2, RSASigGen<EVP_sha384, true>},
    {"RSA/sigGen/SHA2-512/pss", 2, RSASigGen<EVP_sha512, true>},
    {"RSA/sigGen/SHA2-512/224/pss", 2, RSASigGen<EVP_sha512_224, true>},
    {"RSA/sigGen/SHA2-512/256/pss", 2, RSASigGen<EVP_sha512_256, true>},
    {"RSA/sigGen/SHA-1/pss", 2, RSASigGen<EVP_sha1, true>},
    {"RSA/sigGen/SHAKE-128/pss", 2, RSASigGen<EVP_shake128, true>},
    {"RSA/sigGen/SHAKE-256/pss", 2, RSASigGen<EVP_shake256, true>},
    {"RSA/sigVer/SHA3-224/pkcs1v1.5", 4, RSASigVer<EVP_sha3_224, false>},
    {"RSA/sigVer/SHA3-256/pkcs1v1.5", 4, RSASigVer<EVP_sha3_256, false>},
    {"RSA/sigVer/SHA3-384/pkcs1v1.5", 4, RSASigVer<EVP_sha3_384, false>},
    {"RSA/sigVer/SHA3-512/pkcs1v1.5", 4, RSASigVer<EVP_sha3_512, false>},
    {"RSA/sigVer/SHA2-224/pkcs1v1.5", 4, RSASigVer<EVP_sha224, false>},
    {"RSA/sigVer/SHA2-256/pkcs1v1.5", 4, RSASigVer<EVP_sha256, false>},
    {"RSA/sigVer/SHA2-384/pkcs1v1.5", 4, RSASigVer<EVP_sha384, false>},
    {"RSA/sigVer/SHA2-512/pkcs1v1.5", 4, RSASigVer<EVP_sha512, false>},
    {"RSA/sigVer/SHA2-512/224/pkcs1v1.5", 4, RSASigVer<EVP_sha512_224, false>},
    {"RSA/sigVer/SHA2-512/256/pkcs1v1.5", 4, RSASigVer<EVP_sha512_256, false>},
    {"RSA/sigVer/SHA-1/pkcs1v1.5", 4, RSASigVer<EVP_sha1, false>},
    {"RSA/sigVer/SHA3-224/pss", 4, RSASigVer<EVP_sha3_224, true>},
    {"RSA/sigVer/SHA3-256/pss", 4, RSASigVer<EVP_sha3_256, true>},
    {"RSA/sigVer/SHA3-384/pss", 4, RSASigVer<EVP_sha3_384, true>},
    {"RSA/sigVer/SHA3-512/pss", 4, RSASigVer<EVP_sha3_512, true>},
    {"RSA/sigVer/SHA2-224/pss", 4, RSASigVer<EVP_sha224, true>},
    {"RSA/sigVer/SHA2-256/pss", 4, RSASigVer<EVP_sha256, true>},
    {"RSA/sigVer/SHA2-384/pss", 4, RSASigVer<EVP_sha384, true>},
    {"RSA/sigVer/SHA2-512/pss", 4, RSASigVer<EVP_sha512, true>},
    {"RSA/sigVer/SHA2-512/224/pss", 4, RSASigVer<EVP_sha512_224, true>},
    {"RSA/sigVer/SHA2-512/256/pss", 4, RSASigVer<EVP_sha512_256, true>},
    {"RSA/sigVer/SHA-1/pss", 4, RSASigVer<EVP_sha1, true>},
    {"RSA/sigVer/SHAKE-128/pss", 4, RSASigVer<EVP_shake128, true>},
    {"RSA/sigVer/SHAKE-256/pss", 4, RSASigVer<EVP_shake256, true>},
    {"TLSKDF/1.0/SHA-1", 5, TLSKDF<EVP_md5_sha1>},
    {"TLSKDF/1.2/SHA2-256", 5, TLSKDF<EVP_sha256>},
    {"TLSKDF/1.2/SHA2-384", 5, TLSKDF<EVP_sha384>},
    {"TLSKDF/1.2/SHA2-512", 5, TLSKDF<EVP_sha512>},
    {"ECDH/P-224", 3, ECDH<NID_secp224r1>},
    {"ECDH/P-256", 3, ECDH<NID_X9_62_prime256v1>},
    {"ECDH/P-384", 3, ECDH<NID_secp384r1>},
    {"ECDH/P-521", 3, ECDH<NID_secp521r1>},
    {"FFDH", 6, FFDH},
    {"PBKDF", 5, PBKDF},
    {"KDA/HKDF/SHA-1", 4, HKDF<EVP_sha1>},
    {"KDA/HKDF/SHA2-224", 4, HKDF<EVP_sha224>},
    {"KDA/HKDF/SHA2-256", 4, HKDF<EVP_sha256>},
    {"KDA/HKDF/SHA2-384", 4, HKDF<EVP_sha384>},
    {"KDA/HKDF/SHA2-512", 4, HKDF<EVP_sha512>},
    {"KDA/HKDF/SHA2-512/224", 4, HKDF<EVP_sha512_224>},
    {"KDA/HKDF/SHA2-512/256", 4, HKDF<EVP_sha512_256>},
    {"KDA/OneStep/SHA-1", 3, SSKDF_DIGEST<EVP_sha1>},
    {"KDA/OneStep/SHA2-224", 3, SSKDF_DIGEST<EVP_sha224>},
    {"KDA/OneStep/SHA2-256", 3, SSKDF_DIGEST<EVP_sha256>},
    {"KDA/OneStep/SHA2-384", 3, SSKDF_DIGEST<EVP_sha384>},
    {"KDA/OneStep/SHA2-512", 3, SSKDF_DIGEST<EVP_sha512>},
    {"KDA/OneStep/SHA2-512/224", 3, SSKDF_DIGEST<EVP_sha512_224>},
    {"KDA/OneStep/SHA2-512/256", 3, SSKDF_DIGEST<EVP_sha512_256>},
    {"KDA/OneStep/SHA3-224", 3, SSKDF_DIGEST<EVP_sha3_224>},
    {"KDA/OneStep/SHA3-256", 3, SSKDF_DIGEST<EVP_sha3_256>},
    {"KDA/OneStep/SHA3-384", 3, SSKDF_DIGEST<EVP_sha3_384>},
    {"KDA/OneStep/SHA3-512", 3, SSKDF_DIGEST<EVP_sha3_512>},
    {"KDA/OneStep/HMAC-SHA-1", 4, SSKDF_HMAC<EVP_sha1>},
    {"KDA/OneStep/HMAC-SHA2-224", 4, SSKDF_HMAC<EVP_sha224>},
    {"KDA/OneStep/HMAC-SHA2-256", 4, SSKDF_HMAC<EVP_sha256>},
    {"KDA/OneStep/HMAC-SHA2-384", 4, SSKDF_HMAC<EVP_sha384>},
    {"KDA/OneStep/HMAC-SHA2-512", 4, SSKDF_HMAC<EVP_sha512>},
    {"KDA/OneStep/HMAC-SHA2-512/224", 4, SSKDF_HMAC<EVP_sha512_224>},
    {"KDA/OneStep/HMAC-SHA2-512/256", 4, SSKDF_HMAC<EVP_sha512_256>},
    {"SSHKDF/SHA-1/ivCli", 4,
     SSHKDF<EVP_sha1, EVP_KDF_SSHKDF_TYPE_INITIAL_IV_CLI_TO_SRV>},
    {"SSHKDF/SHA2-224/ivCli", 4,
     SSHKDF<EVP_sha224, EVP_KDF_SSHKDF_TYPE_INITIAL_IV_CLI_TO_SRV>},
    {"SSHKDF/SHA2-256/ivCli", 4,
     SSHKDF<EVP_sha256, EVP_KDF_SSHKDF_TYPE_INITIAL_IV_CLI_TO_SRV>},
    {"SSHKDF/SHA2-384/ivCli", 4,
     SSHKDF<EVP_sha384, EVP_KDF_SSHKDF_TYPE_INITIAL_IV_CLI_TO_SRV>},
    {"SSHKDF/SHA2-512/ivCli", 4,
     SSHKDF<EVP_sha512, EVP_KDF_SSHKDF_TYPE_INITIAL_IV_CLI_TO_SRV>},
    {"SSHKDF/SHA-1/ivServ", 4,
     SSHKDF<EVP_sha1, EVP_KDF_SSHKDF_TYPE_INITIAL_IV_SRV_TO_CLI>},
    {"SSHKDF/SHA2-224/ivServ", 4,
     SSHKDF<EVP_sha224, EVP_KDF_SSHKDF_TYPE_INITIAL_IV_SRV_TO_CLI>},
    {"SSHKDF/SHA2-256/ivServ", 4,
     SSHKDF<EVP_sha256, EVP_KDF_SSHKDF_TYPE_INITIAL_IV_SRV_TO_CLI>},
    {"SSHKDF/SHA2-384/ivServ", 4,
     SSHKDF<EVP_sha384, EVP_KDF_SSHKDF_TYPE_INITIAL_IV_SRV_TO_CLI>},
    {"SSHKDF/SHA2-512/ivServ", 4,
     SSHKDF<EVP_sha512, EVP_KDF_SSHKDF_TYPE_INITIAL_IV_SRV_TO_CLI>},
    {"SSHKDF/SHA-1/encryptCli", 4,
     SSHKDF<EVP_sha1, EVP_KDF_SSHKDF_TYPE_ENCRYPTION_KEY_CLI_TO_SRV>},
    {"SSHKDF/SHA2-224/encryptCli", 4,
     SSHKDF<EVP_sha224, EVP_KDF_SSHKDF_TYPE_ENCRYPTION_KEY_CLI_TO_SRV>},
    {"SSHKDF/SHA2-256/encryptCli", 4,
     SSHKDF<EVP_sha256, EVP_KDF_SSHKDF_TYPE_ENCRYPTION_KEY_CLI_TO_SRV>},
    {"SSHKDF/SHA2-384/encryptCli", 4,
     SSHKDF<EVP_sha384, EVP_KDF_SSHKDF_TYPE_ENCRYPTION_KEY_CLI_TO_SRV>},
    {"SSHKDF/SHA2-512/encryptCli", 4,
     SSHKDF<EVP_sha512, EVP_KDF_SSHKDF_TYPE_ENCRYPTION_KEY_CLI_TO_SRV>},
    {"SSHKDF/SHA-1/encryptServ", 4,
     SSHKDF<EVP_sha1, EVP_KDF_SSHKDF_TYPE_ENCRYPTION_KEY_SRV_TO_CLI>},
    {"SSHKDF/SHA2-224/encryptServ", 4,
     SSHKDF<EVP_sha224, EVP_KDF_SSHKDF_TYPE_ENCRYPTION_KEY_SRV_TO_CLI>},
    {"SSHKDF/SHA2-256/encryptServ", 4,
     SSHKDF<EVP_sha256, EVP_KDF_SSHKDF_TYPE_ENCRYPTION_KEY_SRV_TO_CLI>},
    {"SSHKDF/SHA2-384/encryptServ", 4,
     SSHKDF<EVP_sha384, EVP_KDF_SSHKDF_TYPE_ENCRYPTION_KEY_SRV_TO_CLI>},
    {"SSHKDF/SHA2-512/encryptServ", 4,
     SSHKDF<EVP_sha512, EVP_KDF_SSHKDF_TYPE_ENCRYPTION_KEY_SRV_TO_CLI>},
    {"SSHKDF/SHA-1/integCli", 4,
     SSHKDF<EVP_sha1, EVP_KDF_SSHKDF_TYPE_INTEGRITY_KEY_CLI_TO_SRV>},
    {"SSHKDF/SHA2-224/integCli", 4,
     SSHKDF<EVP_sha224, EVP_KDF_SSHKDF_TYPE_INTEGRITY_KEY_CLI_TO_SRV>},
    {"SSHKDF/SHA2-256/integCli", 4,
     SSHKDF<EVP_sha256, EVP_KDF_SSHKDF_TYPE_INTEGRITY_KEY_CLI_TO_SRV>},
    {"SSHKDF/SHA2-384/integCli", 4,
     SSHKDF<EVP_sha384, EVP_KDF_SSHKDF_TYPE_INTEGRITY_KEY_CLI_TO_SRV>},
    {"SSHKDF/SHA2-512/integCli", 4,
     SSHKDF<EVP_sha512, EVP_KDF_SSHKDF_TYPE_INTEGRITY_KEY_CLI_TO_SRV>},
    {"SSHKDF/SHA-1/integServ", 4,
     SSHKDF<EVP_sha1, EVP_KDF_SSHKDF_TYPE_INTEGRITY_KEY_SRV_TO_CLI>},
    {"SSHKDF/SHA2-224/integServ", 4,
     SSHKDF<EVP_sha224, EVP_KDF_SSHKDF_TYPE_INTEGRITY_KEY_SRV_TO_CLI>},
    {"SSHKDF/SHA2-256/integServ", 4,
     SSHKDF<EVP_sha256, EVP_KDF_SSHKDF_TYPE_INTEGRITY_KEY_SRV_TO_CLI>},
    {"SSHKDF/SHA2-384/integServ", 4,
     SSHKDF<EVP_sha384, EVP_KDF_SSHKDF_TYPE_INTEGRITY_KEY_SRV_TO_CLI>},
    {"SSHKDF/SHA2-512/integServ", 4,
     SSHKDF<EVP_sha512, EVP_KDF_SSHKDF_TYPE_INTEGRITY_KEY_SRV_TO_CLI>},
    {"KDF/Feedback/HMAC-SHA-1", 3, HKDF_expand<EVP_sha1>},
    {"KDF/Feedback/HMAC-SHA2-224", 3, HKDF_expand<EVP_sha224>},
    {"KDF/Feedback/HMAC-SHA2-256", 3, HKDF_expand<EVP_sha256>},
    {"KDF/Feedback/HMAC-SHA2-384", 3, HKDF_expand<EVP_sha384>},
    {"KDF/Feedback/HMAC-SHA2-512", 3, HKDF_expand<EVP_sha512>},
    {"KDF/Feedback/HMAC-SHA2-512/224", 3, HKDF_expand<EVP_sha512_224>},
    {"KDF/Feedback/HMAC-SHA2-512/256", 3, HKDF_expand<EVP_sha512_256>},
    {"KDF/Counter/HMAC-SHA-1", 3, KBKDF_CTR_HMAC<EVP_sha1>},
    {"KDF/Counter/HMAC-SHA2-224", 3, KBKDF_CTR_HMAC<EVP_sha224>},
    {"KDF/Counter/HMAC-SHA2-256", 3, KBKDF_CTR_HMAC<EVP_sha256>},
    {"KDF/Counter/HMAC-SHA2-384", 3, KBKDF_CTR_HMAC<EVP_sha384>},
    {"KDF/Counter/HMAC-SHA2-512", 3, KBKDF_CTR_HMAC<EVP_sha512>},
    {"KDF/Counter/HMAC-SHA2-512/224", 3, KBKDF_CTR_HMAC<EVP_sha512_224>},
    {"KDF/Counter/HMAC-SHA2-512/256", 3, KBKDF_CTR_HMAC<EVP_sha512_256>},
    {"ML-KEM/ML-KEM-512/keyGen", 2, ML_KEM_KEYGEN<NID_MLKEM512>},
    {"ML-KEM/ML-KEM-768/keyGen", 2, ML_KEM_KEYGEN<NID_MLKEM768>},
    {"ML-KEM/ML-KEM-1024/keyGen", 2, ML_KEM_KEYGEN<NID_MLKEM1024>},
    {"ML-KEM/ML-KEM-512/encap", 2, ML_KEM_ENCAP<NID_MLKEM512>},
    {"ML-KEM/ML-KEM-768/encap", 2, ML_KEM_ENCAP<NID_MLKEM768>},
    {"ML-KEM/ML-KEM-1024/encap", 2, ML_KEM_ENCAP<NID_MLKEM1024>},
    {"ML-KEM/ML-KEM-512/decap", 2, ML_KEM_DECAP<NID_MLKEM512>},
    {"ML-KEM/ML-KEM-768/decap", 2, ML_KEM_DECAP<NID_MLKEM768>},
    {"ML-KEM/ML-KEM-1024/decap", 2, ML_KEM_DECAP<NID_MLKEM1024>},
    {"EDDSA/ED-25519/keyGen", 0, ED25519KeyGen},
    {"EDDSA/ED-25519/keyVer", 1, ED25519KeyVer},
    {"EDDSA/ED-25519/sigGen", 2, ED25519SigGen},
    {"EDDSA/ED-25519/sigGen/preHash", 3, ED25519phSigGen},
    {"EDDSA/ED-25519/sigVer", 3, ED25519SigVer},
    {"EDDSA/ED-25519/sigVer/preHash", 4, ED25519phSigVer},
    {"ML-DSA/ML-DSA-44/keyGen", 1, ML_DSA_KEYGEN<NID_MLDSA44>},
    {"ML-DSA/ML-DSA-65/keyGen", 1, ML_DSA_KEYGEN<NID_MLDSA65>},
    {"ML-DSA/ML-DSA-87/keyGen", 1, ML_DSA_KEYGEN<NID_MLDSA87>},
    {"ML-DSA/ML-DSA-44/sigGen", 5, ML_DSA_SIGGEN<NID_MLDSA44>},
    {"ML-DSA/ML-DSA-65/sigGen", 5, ML_DSA_SIGGEN<NID_MLDSA65>},
    {"ML-DSA/ML-DSA-87/sigGen", 5, ML_DSA_SIGGEN<NID_MLDSA87>},
    {"ML-DSA/ML-DSA-44/sigVer", 5, ML_DSA_SIGVER<NID_MLDSA44>},
    {"ML-DSA/ML-DSA-65/sigVer", 5, ML_DSA_SIGVER<NID_MLDSA65>},
    {"ML-DSA/ML-DSA-87/sigVer", 5, ML_DSA_SIGVER<NID_MLDSA87>}};

Handler FindHandler(Span<const Span<const uint8_t>> args) {
  const bssl::Span<const uint8_t> algorithm = args[0];
  for (const auto &func : kFunctions) {
    if (algorithm.size() == strlen(func.name) &&
        memcmp(algorithm.data(), func.name, algorithm.size()) == 0) {
      if (args.size() - 1 != func.num_expected_args) {
        LOG_ERROR("\'%s\' operation received %zu arguments but expected %u.\n",
                  func.name, args.size() - 1, func.num_expected_args);
        return nullptr;
      }

      return func.handler;
    }
  }

  const std::string name(reinterpret_cast<const char *>(algorithm.data()),
                         algorithm.size());
  LOG_ERROR("Unknown operation: %s\n", name.c_str());
  return nullptr;
}

}  // namespace acvp
}  // namespace bssl
