// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <string.h>

#include <openssl/chacha.h>
#include <openssl/cipher.h>
#include <openssl/nid.h>

#include "../internal.h"
#include "../fipsmodule/cipher/internal.h"


// Raw ChaCha20 stream cipher exposed through the EVP_CIPHER interface, matching
// OpenSSL's |EVP_chacha20|. BoringSSL only exposes ChaCha20 via the AEAD
// (|EVP_aead_chacha20_poly1305|) and the one-shot |CRYPTO_chacha_20| primitive,
// so this wrapper adapts the primitive to the streaming EVP contract.
//
// The 16-byte IV is interpreted as OpenSSL does: a 32-bit little-endian block
// counter followed by a 96-bit nonce, i.e. iv = counter(4, LE) || nonce(12).
// |CRYPTO_chacha_20| always starts at a block boundary, so the context buffers
// the unused tail of the current 64-byte keystream block across calls.

struct chacha20_ctx {
  uint8_t key[32];
  uint8_t nonce[12];
  uint32_t counter;
  uint8_t buf[64];
  unsigned buf_offset;
};

static int chacha20_init_key(EVP_CIPHER_CTX *ctx, const uint8_t *key,
                             const uint8_t *iv, int enc) {
  struct chacha20_ctx *c = (struct chacha20_ctx *)ctx->cipher_data;
  if (key != NULL) {
    OPENSSL_memcpy(c->key, key, sizeof(c->key));
  }
  if (iv != NULL) {
    c->counter = CRYPTO_load_u32_le(iv);
    OPENSSL_memcpy(c->nonce, iv + 4, sizeof(c->nonce));
    c->buf_offset = 0;
  }
  return 1;
}

static int chacha20_cipher(EVP_CIPHER_CTX *ctx, uint8_t *out, const uint8_t *in,
                           size_t in_len) {
  struct chacha20_ctx *c = (struct chacha20_ctx *)ctx->cipher_data;

  // Consume any keystream left over in the current block from a prior call.
  if (c->buf_offset != 0) {
    while (in_len > 0 && c->buf_offset < sizeof(c->buf)) {
      *out++ = *in++ ^ c->buf[c->buf_offset++];
      in_len--;
    }
    if (c->buf_offset == sizeof(c->buf)) {
      c->buf_offset = 0;
    }
  }

  // Encrypt whole blocks in bulk; |CRYPTO_chacha_20| advances the counter
  // internally, so advance our copy by the number of blocks consumed.
  if (in_len >= sizeof(c->buf)) {
    size_t blocks = in_len / sizeof(c->buf);
    size_t bulk = blocks * sizeof(c->buf);
    CRYPTO_chacha_20(out, in, bulk, c->key, c->nonce, c->counter);
    c->counter += (uint32_t)blocks;
    out += bulk;
    in += bulk;
    in_len -= bulk;
  }

  // Final partial block: generate one keystream block and buffer the remainder.
  if (in_len > 0) {
    OPENSSL_memset(c->buf, 0, sizeof(c->buf));
    CRYPTO_chacha_20(c->buf, c->buf, sizeof(c->buf), c->key, c->nonce,
                     c->counter);
    c->counter++;
    for (size_t i = 0; i < in_len; i++) {
      out[i] = in[i] ^ c->buf[i];
    }
    c->buf_offset = (unsigned)in_len;
  }

  return 1;
}

static const EVP_CIPHER chacha20 = {
    .nid = NID_chacha20,
    .block_size = 1,
    .key_len = 32,
    .iv_len = 16,
    .ctx_size = sizeof(struct chacha20_ctx),
    .flags = EVP_CIPH_ALWAYS_CALL_INIT,
    .init = chacha20_init_key,
    .cipher = chacha20_cipher,
};

const EVP_CIPHER *EVP_chacha20(void) { return &chacha20; }
