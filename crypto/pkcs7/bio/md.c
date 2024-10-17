// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <errno.h>
#include <openssl/buffer.h>
#include <openssl/evp.h>
#include <openssl/pkcs7.h>
#include "../../internal.h"
#include "../crypto/bio/internal.h"
#include "../internal.h"

// |md_write| and |md_read| both contribute to the digest, |md_gets| returns
// digest contents
static int md_write(BIO *h, char const *buf, int num);
static int md_read(BIO *h, char *buf, int size);
static int md_gets(BIO *h, char *str, int size);
static long md_ctrl(BIO *h, int cmd, long arg1, void *arg2);
static int md_new(BIO *h);
static int md_free(BIO *data);


static const BIO_METHOD methods_md = {
    BIO_TYPE_MD, "message digest", md_write, md_read, /*puts*/ NULL,
    md_gets,     md_ctrl,          md_new,   md_free, /*callback_ctrl*/ NULL,
};
const BIO_METHOD *BIO_f_md(void) { return &methods_md; }

static int md_new(BIO *b) {
  GUARD_PTR(b);
  EVP_MD_CTX *ctx;

  ctx = EVP_MD_CTX_new();
  if (ctx == NULL) {
    return 0;
  }

  BIO_set_data(b, ctx);

  return 1;
}

static int md_free(BIO *b) {
  GUARD_PTR(b);
  EVP_MD_CTX_free(BIO_get_data(b));
  BIO_set_data(b, NULL);
  BIO_set_init(b, 0);

  return 1;
}

static int md_read(BIO *b, char *out, int outl) {
  GUARD_PTR(b);
  GUARD_PTR(out);
  int ret = 0;
  EVP_MD_CTX *ctx;
  BIO *next;

  ctx = BIO_get_data(b);
  next = BIO_next(b);

  if ((ctx == NULL) || (next == NULL) || outl <= 0) {
    return 0;
  }

  ret = BIO_read(next, out, outl);
  if (BIO_get_init(b)) {
    if (ret > 0) {
      if (EVP_DigestUpdate(ctx, (unsigned char *)out, ret) <= 0) {
        return -1;
      }
    }
  }
  BIO_clear_retry_flags(b);
  BIO_copy_next_retry(b);
  return ret;
}

static int md_write(BIO *b, const char *in, int inl) {
  GUARD_PTR(b);
  GUARD_PTR(in);
  int ret = 0;
  EVP_MD_CTX *ctx;
  BIO *next;

  if (inl <= 0) {
    return 0;
  }

  ctx = BIO_get_data(b);
  next = BIO_next(b);
  if ((ctx != NULL) && (next != NULL)) {
    ret = BIO_write(next, in, inl);
  }

  if (BIO_get_init(b)) {
    if (ret > 0) {
      if (!EVP_DigestUpdate(ctx, (const unsigned char *)in, ret)) {
        BIO_clear_retry_flags(b);
        return 0;
      }
    }
  }
  if (next != NULL) {
    BIO_clear_retry_flags(b);
    BIO_copy_next_retry(b);
  }
  return ret;
}

static long md_ctrl(BIO *b, int cmd, long num, void *ptr) {
  GUARD_PTR(b);
  EVP_MD_CTX *ctx, **pctx;
  EVP_MD *md;
  long ret = 1;
  BIO *next;

  ctx = BIO_get_data(b);
  next = BIO_next(b);

  switch (cmd) {
    case BIO_CTRL_RESET:
      if (BIO_get_init(b)) {
        ret = EVP_DigestInit_ex(ctx, EVP_MD_CTX_md(ctx), NULL);
      } else {
        ret = 0;
      }
      if (ret > 0) {
        ret = BIO_ctrl(next, cmd, num, ptr);
      }
      break;
    case BIO_C_GET_MD_CTX:
      pctx = ptr;
      *pctx = ctx;
      break;
    case BIO_C_SET_MD:
      md = ptr;
      ret = EVP_DigestInit_ex(ctx, md, NULL);
      if (ret > 0) {
        BIO_set_init(b, 1);
      }
      break;
    // OpenSSL implements these, but because we don't need them and cipher BIO
    // is internal, we can fail loudly if they're called. If this case is hit,
    // it likely means you're making a change that will require implementing
    // these.
    case BIO_C_GET_MD:
    case BIO_C_SET_MD_CTX:
    case BIO_C_DO_STATE_MACHINE:
    case BIO_CTRL_DUP:
    case BIO_CTRL_GET_CALLBACK:
    case BIO_CTRL_SET_CALLBACK:
      OPENSSL_PUT_ERROR(PKCS7, ERR_R_BIO_LIB);
      return 0;
    default:
      ret = BIO_ctrl(next, cmd, num, ptr);
      break;
  }
  return ret;
}

static int md_gets(BIO *b, char *buf, int size) {
  GUARD_PTR(b);
  GUARD_PTR(buf);
  EVP_MD_CTX *ctx;
  unsigned int ret;

  ctx = BIO_get_data(b);

  if (((size_t)size) < EVP_MD_CTX_size(ctx)) {
    return 0;
  }

  if (EVP_DigestFinal_ex(ctx, (unsigned char *)buf, &ret) <= 0) {
    return -1;
  }

  return ret;
}
