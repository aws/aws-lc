// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <errno.h>
#include <openssl/buffer.h>
#include <openssl/crypto.h>
#include <openssl/evp.h>
#include <openssl/mem.h>
#include <openssl/pkcs7.h>
#include <stdio.h>
#include "../crypto/bio/internal.h"
#include "../fipsmodule/cipher/internal.h"
#include "../internal.h"
#include "./internal.h"

static int enc_write(BIO *h, const char *buf, int num);
static int enc_read(BIO *h, char *buf, int size);
static long enc_ctrl(BIO *h, int cmd, long arg1, void *arg2);
static int enc_new(BIO *h);
static int enc_free(BIO *data);
#define ENC_BLOCK_SIZE (1024 * 4)
#define ENC_MIN_CHUNK (256)
#define BUF_OFFSET (ENC_MIN_CHUNK + EVP_MAX_BLOCK_LENGTH)

typedef struct enc_struct {
  int buf_off;  // start idx of buffered data
  int buf_len;  // length of buffered data
  int cont;     // <= 0 when finished
  int flushed;  // >0 when buffered data has been flushed
  int ok;       // decryption status
  EVP_CIPHER_CTX *cipher;
  // start and end pointers for data read from underlying BIO
  unsigned char *read_start, *read_end;
  // buf is larger than ENC_BLOCK_SIZE because EVP_DecryptUpdate can return
  // up to a block more data than is presented to it
  unsigned char buf[BUF_OFFSET + ENC_BLOCK_SIZE];
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

static int enc_new(BIO *bi) {
  BIO_ENC_CTX *ctx;

  if ((ctx = OPENSSL_zalloc(sizeof(*ctx))) == NULL) {
    return 0;
  }

  ctx->cipher = EVP_CIPHER_CTX_new();
  if (ctx->cipher == NULL) {
    OPENSSL_free(ctx);
    return 0;
  }
  ctx->cont = 1;
  ctx->ok = 1;
  ctx->read_end = ctx->read_start = &(ctx->buf[BUF_OFFSET]);
  BIO_set_data(bi, ctx);
  BIO_set_init(bi, 1);

  return 1;
}

static int enc_free(BIO *a) {
  BIO_ENC_CTX *b;

  if (a == NULL) {
    return 0;
  }

  b = BIO_get_data(a);
  if (b == NULL) {
    return 0;
  }

  EVP_CIPHER_CTX_free(b->cipher);
  OPENSSL_cleanse(b, sizeof(BIO_ENC_CTX));
  OPENSSL_free(b);
  BIO_set_data(a, NULL);
  BIO_set_init(a, 0);

  return 1;
}

static int enc_read(BIO *b, char *out, int outl) {
  int ret = 0, bytes_read, blocksize;
  BIO_ENC_CTX *ctx;
  BIO *next;

  if (out == NULL) {
    return 0;
  }
  ctx = BIO_get_data(b);

  next = BIO_next(b);
  if ((ctx == NULL) || (next == NULL)) {
    return 0;
  }

  // First check if there are bytes decoded/encoded
  if (ctx->buf_len > 0) {
    bytes_read = ctx->buf_len - ctx->buf_off;
    if (bytes_read > outl) {
      bytes_read = outl;
    }
    OPENSSL_memcpy(out, &(ctx->buf[ctx->buf_off]), bytes_read);
    ret = bytes_read;
    out += bytes_read;
    outl -= bytes_read;
    ctx->buf_off += bytes_read;
    if (ctx->buf_len == ctx->buf_off) {
      ctx->buf_len = 0;
      ctx->buf_off = 0;
    }
  }

  blocksize = EVP_CIPHER_CTX_block_size(ctx->cipher);

  if (blocksize == 0) {
    return 0;
  }

  // blocksize of 1 indicates stream cipher
  if (blocksize == 1) {
    blocksize = 0;
  }

  // At this point, we have room of outl bytes and an empty buffer, so we
  // should read in some more.
  int remaining = outl;
  while (remaining > 0) {
    if (ctx->cont <= 0) {
      break;
    }

    if (ctx->read_start == ctx->read_end) {  // time to read more data
      ctx->read_end = ctx->read_start = &(ctx->buf[BUF_OFFSET]);
      bytes_read = BIO_read(next, ctx->read_start, ENC_BLOCK_SIZE);
      if (bytes_read > 0) {
        ctx->read_end += bytes_read;
      }
    } else {
      bytes_read = ctx->read_end - ctx->read_start;
    }

    if (bytes_read <= 0) {
      // Should be continue next time we are called?
      if (!BIO_should_retry(next)) {
        ctx->cont = 0;
        bytes_read = EVP_CipherFinal_ex(ctx->cipher, ctx->buf, &(ctx->buf_len));
        ctx->ok = bytes_read;
        ctx->buf_off = 0;
      } else {
        ret = (ret == 0) ? bytes_read : ret;
        break;
      }
    } else {
      if (remaining > ENC_MIN_CHUNK) {
        // Depending on flags block cipher decrypt can write
        // one extra block and then back off, i.e. output buffer
        // has to accommodate extra block...
        int buf_len;
        int plaintext_end = remaining - blocksize;
        int read_size = bytes_read > plaintext_end ? plaintext_end : bytes_read;
        if (!EVP_CipherUpdate(ctx->cipher, (unsigned char *)out, &buf_len,
                              ctx->read_start, read_size)) {
          BIO_clear_retry_flags(b);
          return 0;
        }
        ret += buf_len;
        out += buf_len;
        remaining -= buf_len;

        if ((bytes_read -= plaintext_end) <= 0) {
          ctx->read_start = ctx->read_end;
          continue;
        }
        ctx->read_start += plaintext_end;
      }
      if (bytes_read > ENC_MIN_CHUNK) {
        bytes_read = ENC_MIN_CHUNK;
      }
      if (!EVP_CipherUpdate(ctx->cipher, ctx->buf, &ctx->buf_len,
                            ctx->read_start, bytes_read)) {
        BIO_clear_retry_flags(b);
        ctx->ok = 0;
        return 0;
      }
      ctx->read_start += bytes_read;
      ctx->cont = 1;
      // Note: it is possible for EVP_CipherUpdate to decrypt zero
      // bytes because this is or looks like the final block: if this
      // happens we should retry and either read more data or decrypt
      // the final block
      if (ctx->buf_len == 0) {
        continue;
      }
    }

    if (ctx->buf_len <= remaining) {
      bytes_read = ctx->buf_len;
    } else {
      bytes_read = remaining;
    }
    if (bytes_read <= 0) {
      break;
    }
    OPENSSL_memcpy(out, ctx->buf, bytes_read);
    ret += bytes_read;
    ctx->buf_off = bytes_read;
    remaining -= bytes_read;
    out += bytes_read;
  }

  BIO_clear_retry_flags(b);
  BIO_copy_next_retry(b);
  // OpenSSL sometimes returns ctx->cont here. We don't, as its value doesn't
  // pertain to the number of bytes written.
  return ret;
}

static int enc_write(BIO *b, const char *in, int inl) {
  int ret = 0;
  BIO_ENC_CTX *ctx;
  BIO *next;

  ctx = BIO_get_data(b);
  next = BIO_next(b);
  // We need a context and a |next| BIO to write to
  if ((ctx == NULL) || (next == NULL)) {
    return 0;
  }

  ret = inl;

  BIO_clear_retry_flags(b);
  int bytes_remaining = ctx->buf_len - ctx->buf_off;
  while (bytes_remaining > 0) {
    int bytes_written =
        BIO_write(next, &(ctx->buf[ctx->buf_off]), bytes_remaining);
    if (bytes_written <= 0) {
      BIO_copy_next_retry(b);
      return bytes_written;
    }
    ctx->buf_off += bytes_written;
    bytes_remaining -= bytes_written;
  }
  // at this point all pending data has been written
  if ((in == NULL) || (inl <= 0)) {
    return 0;
  }

  ctx->buf_off = 0;
  int remaining = inl;
  while (remaining > 0) {
    int to_write = (remaining > ENC_BLOCK_SIZE) ? ENC_BLOCK_SIZE : remaining;
    if (!EVP_CipherUpdate(ctx->cipher, ctx->buf, &ctx->buf_len,
                          (const unsigned char *)in, to_write)) {
      BIO_clear_retry_flags(b);
      ctx->ok = 0;
      return 0;
    }
    remaining -= to_write;
    in += to_write;

    ctx->buf_off = 0;
    to_write = ctx->buf_len;
    while (to_write > 0) {
      int written = BIO_write(next, &(ctx->buf[ctx->buf_off]), to_write);
      if (written <= 0) {
        BIO_copy_next_retry(b);
        return (ret == remaining) ? written : ret - remaining;
      }
      to_write -= written;
      ctx->buf_off += written;
    }
    ctx->buf_len = 0;
    ctx->buf_off = 0;
  }
  BIO_copy_next_retry(b);
  return ret;
}

static long enc_ctrl(BIO *b, int cmd, long num, void *ptr) {
  BIO_ENC_CTX *ctx;
  long ret = 1;
  BIO *next;
  int pend;

  ctx = BIO_get_data(b);
  next = BIO_next(b);
  if (ctx == NULL) {
    return 0;
  }

  switch (cmd) {
    case BIO_CTRL_RESET:
      ctx->ok = 1;
      ctx->flushed = 0;
      if (!EVP_CipherInit_ex(ctx->cipher, NULL, NULL, NULL, NULL,
                             EVP_CIPHER_CTX_encrypting(ctx->cipher)))
        return 0;
      ret = BIO_ctrl(next, cmd, num, ptr);
      break;
    case BIO_CTRL_EOF:  // More to read
      if (ctx->cont <= 0) {
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
      // do a final write
    again:
      while (ctx->buf_len != ctx->buf_off) {
        pend = ctx->buf_len - ctx->buf_off;
        int written = enc_write(b, NULL, 0);
        // |written| should never be > 0 here because we didn't ask to write any
        // new data. We stop if we get an error or we failed to make any
        // progress writing pending data.
        if (written < 0 || (ctx->buf_len - ctx->buf_off) == pend) {
          return written;
        }
      }

      if (!ctx->flushed) {
        ctx->flushed = 1;
        ctx->buf_off = 0;
        ret = EVP_CipherFinal_ex(ctx->cipher, (unsigned char *)ctx->buf,
                                 &(ctx->buf_len));
        ctx->ok = (int)ret;
        if (ret <= 0) {
          break;
        }

        // push out the bytes
        goto again;
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
