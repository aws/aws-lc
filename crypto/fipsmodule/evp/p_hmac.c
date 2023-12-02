/* Written by Dr Stephen N Henson (steve@openssl.org) for the OpenSSL
 * project 2007.
 */
/* ====================================================================
 * Copyright (c) 2007 The OpenSSL Project.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 *
 * 3. All advertising materials mentioning features or use of this
 *    software must display the following acknowledgment:
 *    "This product includes software developed by the OpenSSL Project
 *    for use in the OpenSSL Toolkit. (http://www.OpenSSL.org/)"
 *
 * 4. The names "OpenSSL Toolkit" and "OpenSSL Project" must not be used to
 *    endorse or promote products derived from this software without
 *    prior written permission. For written permission, please contact
 *    licensing@OpenSSL.org.
 *
 * 5. Products derived from this software may not be called "OpenSSL"
 *    nor may "OpenSSL" appear in their names without prior written
 *    permission of the OpenSSL Project.
 *
 * 6. Redistributions of any form whatsoever must retain the following
 *    acknowledgment:
 *    "This product includes software developed by the OpenSSL Project
 *    for use in the OpenSSL Toolkit (http://www.OpenSSL.org/)"
 *
 * THIS SOFTWARE IS PROVIDED BY THE OpenSSL PROJECT ``AS IS'' AND ANY
 * EXPRESSED OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE OpenSSL PROJECT OR
 * ITS CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 * ====================================================================
 *
 * This product includes cryptographic software written by Eric Young
 * (eay@cryptsoft.com).  This product includes software written by Tim
 * Hudson (tjh@cryptsoft.com). */

#include <openssl/evp.h>

#include <openssl/asn1.h>
#include <openssl/err.h>
#include <openssl/hmac.h>
#include <openssl/mem.h>
#include <openssl/obj.h>

#include "../digest/internal.h"
#include "internal.h"


typedef struct {
  const EVP_MD *md; /* MD for HMAC use */
  uint8_t *key;
  size_t key_len;
  HMAC_CTX ctx;
} HMAC_PKEY_CTX;

static int hmac_init(EVP_PKEY_CTX *ctx) {
  HMAC_PKEY_CTX *hctx;
  hctx = OPENSSL_malloc(sizeof(HMAC_PKEY_CTX));
  if (hctx == NULL) {
    return 0;
  }
  OPENSSL_memset(hctx, 0, sizeof(HMAC_PKEY_CTX));
  HMAC_CTX_init(&hctx->ctx);
  ctx->data = hctx;
  return 1;
}

static int hmac_copy(EVP_PKEY_CTX *dst, EVP_PKEY_CTX *src) {
  HMAC_PKEY_CTX *sctx, *dctx;
  if (!hmac_init(dst)) {
    return 0;
  }
  sctx = src->data;
  dctx = dst->data;
  dctx->md = sctx->md;
  HMAC_CTX_init(&dctx->ctx);
  if (!HMAC_CTX_copy_ex(&dctx->ctx, &sctx->ctx)) {
    return 0;
  }
  dctx->key = OPENSSL_memdup(sctx->key, sctx->key_len);
  dctx->key_len = sctx->key_len;
  return 1;
}

static void hmac_cleanup(EVP_PKEY_CTX *ctx) {
  HMAC_PKEY_CTX *hctx = ctx->data;
  if (hctx == NULL) {
    return;
  }
  HMAC_CTX_cleanup(&hctx->ctx);
  // if (hctx->key != NULL) {
  //   OPENSSL_free(hctx->key);
  // }
  OPENSSL_free(hctx);
}

static int hmac_keygen(EVP_PKEY_CTX *ctx, EVP_PKEY *pkey) {
  HMAC_PKEY_CTX *hctx = ctx->data;
  CBS *key = OPENSSL_malloc(sizeof(CBS));
  if (key == NULL) {
    return 0;
  }
  CBS_init(key, hctx->key, hctx->key_len);

  // |EVP_PKEY_new_mac_key| allocates a temporary |EVP_PKEY_CTX| and frees it
  // along with |ctx->data| (which contains the original key data).
  // We allocate and copy the key data over to a new |CBS| |key| and assign it
  // to |pkey|, so that it is available in later operations.
  return EVP_PKEY_assign(pkey, EVP_PKEY_HMAC, key);
}

static void hmac_update(EVP_MD_CTX *ctx, const void *data, size_t count) {
  HMAC_PKEY_CTX *hctx = ctx->pctx->data;
  HMAC_Update(&hctx->ctx, data, count);
}

static int hmac_init_set_up(EVP_PKEY_CTX *ctx, EVP_MD_CTX *mctx) {
  // |mctx| gets repurposed as a hook to call |HMAC_Update|. |mctx->update| is
  // normally copied from |mctx->digest->update|, but |EVP_PKEY_HMAC| has its
  // own definition. We suppress the automatic setting of |mctx->update| and the
  // rest of its initialization here.
  mctx->flags |= EVP_MD_CTX_FLAG_NO_INIT_FOR_HMAC;
  mctx->update = hmac_update;
  return 1;
}

static int hmac_final(EVP_PKEY_CTX *ctx, uint8_t *sig, size_t *siglen,
                      EVP_MD_CTX *mctx) {
  unsigned int hlen;
  HMAC_PKEY_CTX *hctx = ctx->data;
  size_t md_size = EVP_MD_CTX_size(mctx);

  if (sig == NULL) {
    *siglen = md_size;
    return 1;
  } else if (*siglen < md_size) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
    return 0;
  }

  if (!HMAC_Final(&hctx->ctx, sig, &hlen)) {
    return 0;
  }
  *siglen = (size_t)hlen;
  return 1;
}

static int hmac_ctrl(EVP_PKEY_CTX *ctx, int type, int p1, void *p2) {
  HMAC_PKEY_CTX *hctx = ctx->data;

  switch (type) {
    case EVP_PKEY_CTRL_HMAC_SET_MAC_KEY: {
      const CBS *key = p2;
      if (!CBS_stow(key, &hctx->key, &hctx->key_len)) {
        return 0;
      }
      return 1;
    }
    case EVP_PKEY_CTRL_MD:
      hctx->md = p2;
      break;

    case EVP_PKEY_CTRL_HMAC_DIGESTINIT: {
      // |HMAC_PKEY_CTX| is newly allocated by |EVP_DigestSignInit| at this
      // point. The actual key data is stored in |ctx->pkey| as a |CBS| pointer.
      const CBS *key = ctx->pkey->pkey.ptr;
      if (!HMAC_Init_ex(&hctx->ctx, CBS_data(key), CBS_len(key), hctx->md,
                        ctx->engine)) {
        return 0;
      }
      return 1;
    }
    default:
      OPENSSL_PUT_ERROR(EVP, EVP_R_COMMAND_NOT_SUPPORTED);
      return 0;
  }
  return 1;
}

DEFINE_METHOD_FUNCTION(EVP_PKEY_METHOD, EVP_PKEY_hmac_pkey_meth) {
  out->pkey_id = EVP_PKEY_HMAC;
  out->init = hmac_init;
  out->copy = hmac_copy;
  out->cleanup = hmac_cleanup;
  out->keygen = hmac_keygen;  /* keygen */
  out->sign_init = NULL;      /* sign_init */
  out->sign = NULL;           /* sign */
  out->sign_message = NULL;   /* sign_message */
  out->verify_init = NULL;    /* verify_init */
  out->verify = NULL;         /* verify */
  out->verify_message = NULL; /* verify_message */
  out->verify_recover = NULL; /* verify_recover */
  out->encrypt = NULL;        /* encrypt */
  out->decrypt = NULL;        /* decrypt */
  out->derive = NULL;         /* derive */
  out->paramgen = NULL;       /* paramgen */
  out->ctrl = hmac_ctrl;
  out->hmac_init_set_up = hmac_init_set_up;
  out->hmac_final = hmac_final;
}
