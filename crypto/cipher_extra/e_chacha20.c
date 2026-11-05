// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <string.h>

#include <openssl/chacha.h>
#include <openssl/cipher.h>
#include <openssl/mem.h>
#include <openssl/nid.h>

#include "../internal.h"
#include "../fipsmodule/cipher/internal.h"


// Raw ChaCha20 stream cipher exposed through the EVP_CIPHER interface, matching
// OpenSSL's |EVP_chacha20|. BoringSSL only exposes ChaCha20 via the AEAD
// (|EVP_aead_chacha20_poly1305|) and the one-shot |CRYPTO_chacha_20| primitive,
// so this wrapper adapts the primitive to the streaming EVP contract.
//
// The 16-byte IV is interpreted as OpenSSL does: a 64-bit little-endian block
// counter followed by a 64-bit nonce, i.e. iv = counter(8, LE) || nonce(8).
// |CRYPTO_chacha_20| always starts at a block boundary, so the context buffers
// the unused tail of the current 64-byte keystream block across calls.

struct chacha20_ctx {
  uint8_t key[32];
  uint8_t nonce[8];
  uint64_t counter;
  uint8_t buf[64];
  unsigned buf_offset;
};

static void chacha20_get_nonce(uint8_t nonce[12],
                               const struct chacha20_ctx *c) {
  CRYPTO_store_u32_le(nonce, (uint32_t)(c->counter >> 32));
  OPENSSL_memcpy(nonce + 4, c->nonce, sizeof(c->nonce));
}

static int chacha20_init_key(EVP_CIPHER_CTX *ctx, const uint8_t *key,
                             const uint8_t *iv, int enc) {
  struct chacha20_ctx *c = (struct chacha20_ctx *)ctx->cipher_data;
  if (key != NULL) {
    OPENSSL_memcpy(c->key, key, sizeof(c->key));
  }
  if (iv != NULL) {
    c->counter = CRYPTO_load_u64_le(iv);
    OPENSSL_memcpy(c->nonce, iv + 8, sizeof(c->nonce));
  }
  // Any (re-)initialization discards buffered keystream, as OpenSSL does. The
  // counter still points at the partially used block, so it is regenerated
  // under the current key. Wipe the buffer so keystream from a previous key
  // does not linger in memory.
  OPENSSL_cleanse(c->buf, sizeof(c->buf));
  c->buf_offset = 0;
  return 1;
}

static int chacha20_ctrl(EVP_CIPHER_CTX *ctx, int type, int arg, void *ptr) {
  if (type == EVP_CTRL_INIT) {
    // |cipher_data| is not zero-initialized; start from an all-zero IV state.
    OPENSSL_memset(ctx->cipher_data, 0, sizeof(struct chacha20_ctx));
    return 1;
  }
  return -1;
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
      c->counter++;
    }
  }

  // Encrypt whole blocks in bulk; |CRYPTO_chacha_20| advances only its
  // 32-bit counter, so split calls at rollover and advance our 64-bit copy.
  if (in_len >= sizeof(c->buf)) {
    size_t blocks = in_len / sizeof(c->buf);
    while (blocks > 0) {
      const uint64_t blocks_until_rollover =
          (UINT64_C(1) << 32) - (uint32_t)c->counter;
      size_t todo_blocks = blocks;
      if ((uint64_t)todo_blocks > blocks_until_rollover) {
        todo_blocks = (size_t)blocks_until_rollover;
      }
      const size_t todo = todo_blocks * sizeof(c->buf);
      uint8_t nonce[12];
      chacha20_get_nonce(nonce, c);
      CRYPTO_chacha_20(out, in, todo, c->key, nonce, (uint32_t)c->counter);
      c->counter += (uint64_t)todo_blocks;
      blocks -= todo_blocks;
      out += todo;
      in += todo;
      in_len -= todo;
    }
  }

  // Final partial block: generate one keystream block and buffer the remainder.
  // |counter| advances only once the buffered block is fully consumed.
  if (in_len > 0) {
    OPENSSL_memset(c->buf, 0, sizeof(c->buf));
    uint8_t nonce[12];
    chacha20_get_nonce(nonce, c);
    CRYPTO_chacha_20(c->buf, c->buf, sizeof(c->buf), c->key, nonce,
                     (uint32_t)c->counter);
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
    .flags = EVP_CIPH_ALWAYS_CALL_INIT | EVP_CIPH_CTRL_INIT,
    .init = chacha20_init_key,
    .cipher = chacha20_cipher,
    .ctrl = chacha20_ctrl,
};

const EVP_CIPHER *EVP_chacha20(void) { return &chacha20; }
