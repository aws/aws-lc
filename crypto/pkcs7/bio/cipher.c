// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/buffer.h>
#include <openssl/crypto.h>
#include <openssl/evp.h>
#include <openssl/mem.h>
#include <openssl/pkcs7.h>
#include <stdio.h>
#include "../../fipsmodule/cipher/internal.h"
#include "../internal.h"

static int enc_write(BIO *h, const char *buf, int num);
static int enc_read(BIO *h, char *buf, int size);
static long enc_ctrl(BIO *h, int cmd, long arg1, void *arg2);
static int enc_new(BIO *h);
static int enc_free(BIO *data);
#define ENC_BLOCK_SIZE (1024 * 4)

typedef struct enc_struct {
  uint8_t eof;     // > 0 when finished
  uint8_t flushed;  // > 0 when buffered data has been flushed
  uint8_t ok;       // cipher status
  int buf_off;      // start idx of buffered data
  int buf_len;      // length of buffered data
  EVP_CIPHER_CTX *cipher;
  uint8_t buf[ENC_BLOCK_SIZE];  // plaintext for read, ciphertext for writes
} BIO_ENC_CTX;

static const BIO_METHOD methods_enc = {
    BIO_TYPE_CIPHER,
    "cipher",
    enc_write,
    enc_read,
    NULL,  // enc_puts
    NULL,  // enc_gets
    enc_ctrl,
    enc_new,
    enc_free,
    NULL,  // enc_callback_ctrl
};

const BIO_METHOD *BIO_f_cipher(void) { return &methods_enc; }

static int enc_new(BIO *b) {
  BIO_ENC_CTX *ctx;
  GUARD_PTR(b);

  if ((ctx = OPENSSL_zalloc(sizeof(*ctx))) == NULL) {
    return 0;
  }

  ctx->cipher = EVP_CIPHER_CTX_new();
  if (ctx->cipher == NULL) {
    OPENSSL_free(ctx);
    return 0;
  }
  ctx->eof = 0;
  ctx->flushed = 0;
  ctx->ok = 1;
  ctx->buf_off = 0;
  ctx->buf_len = 0;
  BIO_set_data(b, ctx);
  BIO_set_init(b, 1);

  return 1;
}

static int enc_free(BIO *b) {
  BIO_ENC_CTX *ctx;
  GUARD_PTR(b);

  ctx = BIO_get_data(b);
  if (ctx == NULL) {
    return 0;
  }

  EVP_CIPHER_CTX_free(ctx->cipher);
  OPENSSL_free(ctx);
  BIO_set_data(b, NULL);
  BIO_set_init(b, 0);

  return 1;
}

static int enc_read(BIO *b, char *out, int outl) {
  GUARD_PTR(b);
  GUARD_PTR(out);
  BIO_ENC_CTX *ctx = BIO_get_data(b);
  if (ctx == NULL) {
    return 0;
  }
  BIO *next = BIO_next(b);
  if (next == NULL) {
    return 0;
  }

  int bytes_processed = 0;
  int remaining = outl;
  const int cipher_block_size = EVP_CIPHER_CTX_block_size(ctx->cipher);
  while (remaining > 0) {
    if (ctx->buf_len > 0) {
      int bytes_decrypted;
      int to_decrypt = remaining > ctx->buf_len ? ctx->buf_len : remaining;
      uint8_t *out_pos = ((uint8_t *)out) + bytes_processed;
      // |EVP_DecryptUpdate| may write up to cipher_block_size-1 more bytes than
      // requested, so return early if we cannot accommodate that with current
      // |remaining| byte count.
      if ((to_decrypt > (remaining - cipher_block_size + 1)) ||
          !EVP_DecryptUpdate(ctx->cipher, out_pos, &bytes_decrypted,
                             &ctx->buf[ctx->buf_off], to_decrypt)) {
        BIO_copy_next_retry(b);
        return bytes_processed;
      };
      // Update buffer info and counters with number of bytes processed from our
      // buffer.
      ctx->buf_len -= to_decrypt;
      ctx->buf_off += to_decrypt;
      bytes_processed += to_decrypt;
      remaining -= to_decrypt;
      continue;
    }
    assert(ctx->buf_len == 0);
    int to_read = remaining > ENC_BLOCK_SIZE ? ENC_BLOCK_SIZE : remaining;
    int outcome = BIO_read(next, &ctx->buf[0], to_read);
    if (outcome == 0 && BIO_eof(next)) {
      ctx->buf_off = 0;
      ctx->buf_len = 0;
      ctx->eof = 1;
      ctx->ok = EVP_CipherFinal_ex(ctx->cipher, ctx->buf, &ctx->buf_len);
      return bytes_processed;
    } else if (outcome <= 0) {
      BIO_copy_next_retry(b);
      return bytes_processed;
    }
    ctx->buf_off = 0;
    ctx->buf_len = outcome;
  }
  return bytes_processed;
}

static int enc_flush(BIO *b, BIO *next, BIO_ENC_CTX *ctx, int do_final) {
  GUARD_PTR(b);
  GUARD_PTR(next);
  GUARD_PTR(ctx);
  while (ctx->buf_len > 0) {
    int outcome = BIO_write(next, &ctx->buf[ctx->buf_off], ctx->buf_len);
    if (outcome <= 0) {
      BIO_copy_next_retry(b);
      return outcome;
    }
    ctx->buf_off += outcome;
    ctx->buf_len -= outcome;
  }
  ctx->buf_off = 0;
  ctx->buf_len = 0;
  if (do_final && !ctx->flushed) {
    ctx->flushed = 1;
    ctx->ok = EVP_CipherFinal_ex(ctx->cipher, ctx->buf, &ctx->buf_len);
    return ctx->ok;
  }
  return 1;
}

static int enc_write(BIO *b, const char *in, int inl) {
  GUARD_PTR(b);
  GUARD_PTR(in);
  int ret = 0;
  BIO_ENC_CTX *ctx = BIO_get_data(b);
  if (ctx == NULL) {
    return 0;
  }
  BIO *next = BIO_next(b);
  if (next == NULL) {
    return 0;
  }

  if ((ret = enc_flush(b, next, ctx, /*do_final*/ 0)) <= 0) {
    return ret;
  }

  assert(ctx->buf_off == ctx->buf_len && ctx->buf_len == 0);
  int bytes_processed = 0;
  int remaining = inl;
  while (remaining > 0) {
    if (ctx->buf_len == 0) {
      ctx->buf_off = 0;
      int to_encrypt = remaining > ENC_BLOCK_SIZE ? ENC_BLOCK_SIZE : remaining;
      if (!EVP_EncryptUpdate(ctx->cipher, &ctx->buf[0], &ctx->buf_len,
                             (uint8_t *)in, to_encrypt)) {
        ret = bytes_processed;
        goto out;
      };
      bytes_processed += ctx->buf_len;
      remaining -= ctx->buf_len;
    }
    int outcome = BIO_write(next, &ctx->buf[ctx->buf_off], ctx->buf_len);
    if (outcome <= 0) {
      ret = bytes_processed;
      goto out;
    }
    ctx->buf_off += outcome;
    ctx->buf_len -= outcome;
  }
out:
  if (ret <= 0) {
    BIO_copy_next_retry(b);
  }
  return bytes_processed;
}

static long enc_ctrl(BIO *b, int cmd, long num, void *ptr) {
  GUARD_PTR(b);
  BIO_ENC_CTX *ctx;
  long ret = 1;
  BIO *next;

  ctx = BIO_get_data(b);
  next = BIO_next(b);
  if (ctx == NULL) {
    return 0;
  }

  switch (cmd) {
    case BIO_CTRL_RESET:
      ctx->eof = 0;
      ctx->flushed = 0;
      ctx->ok = 1;
      ctx->buf_off = 0;
      ctx->buf_len = 0;
      OPENSSL_cleanse(ctx->buf, sizeof(ctx->buf));
      if (!EVP_CipherInit_ex(ctx->cipher, NULL, NULL, NULL, NULL,
                             EVP_CIPHER_CTX_encrypting(ctx->cipher))) {
        return 0;
      }
      ret = BIO_ctrl(next, cmd, num, ptr);
      break;
    case BIO_CTRL_EOF:
      if (ctx->eof) {
        ret = 1;
      } else {
        ret = BIO_ctrl(next, cmd, num, ptr);
      }
      break;
    case BIO_CTRL_WPENDING:
    case BIO_CTRL_PENDING:
      // Calculate number of bytes left to process if we have anything buffered,
      // else consult underlying BIO.
      ret = ctx->buf_len - ctx->buf_off;
      if (ret <= 0) {
        ret = BIO_ctrl(next, cmd, num, ptr);
      }
      break;
    case BIO_CTRL_FLUSH:
      ret = enc_flush(b, next, ctx, /*do_final*/ 1);
      if (ret <= 0) {
        break;
      }
      // Finally flush the underlying BIO
      ret = BIO_ctrl(next, cmd, num, ptr);
      BIO_copy_next_retry(b);
      break;
    case BIO_C_GET_CIPHER_STATUS:
      ret = (long)ctx->ok;
      break;
    // OpenSSL implements these, but because we don't need them and cipher BIO
    // is internal, we can fail loudly if they're called. If this case is hit,
    // it likely means you're making a change that will require implementing
    // these.
    case BIO_CTRL_DUP:
    case BIO_CTRL_GET_CALLBACK:
    case BIO_CTRL_SET_CALLBACK:
    case BIO_C_DO_STATE_MACHINE:
    case BIO_C_GET_CIPHER_CTX:
      OPENSSL_PUT_ERROR(PKCS7, ERR_R_BIO_LIB);
      return 0;
    default:
      ret = BIO_ctrl(next, cmd, num, ptr);
      break;
  }
  return ret;
}

int BIO_set_cipher(BIO *b, const EVP_CIPHER *c, const unsigned char *key,
                   const unsigned char *iv, int enc) {
  GUARD_PTR(b);
  GUARD_PTR(c);
  BIO_ENC_CTX *ctx;

  ctx = BIO_get_data(b);
  if (ctx == NULL) {
    return 0;
  }

  // We only support a modern subset of available EVP_CIPHERs. Other ciphers
  // (e.g. DES) and cipher modes (e.g. CBC, CCM) had issues with block alignment
  // and padding during testing, so they're forbidden for now.
  const EVP_CIPHER *kSupportedCiphers[] = {
      EVP_aes_128_ctr(),       EVP_aes_128_gcm(), EVP_aes_128_ofb(),
      EVP_aes_256_ctr(),       EVP_aes_256_gcm(), EVP_aes_256_ofb(),
      EVP_chacha20_poly1305(),
  };
  int supported = 0;
  for (size_t i = 0; i < sizeof(kSupportedCiphers) / sizeof(EVP_CIPHER *);
       i++) {
    if (c == kSupportedCiphers[i]) {
      supported = 1;
      break;
    }
  }
  if (!supported) {
    OPENSSL_PUT_ERROR(PKCS7, ERR_R_BIO_LIB);
    return 0;
  }

  BIO_set_init(b, 1);

  if (!EVP_CipherInit_ex(ctx->cipher, c, NULL, key, iv, enc)) {
    return 0;
  }

  return 1;
}
