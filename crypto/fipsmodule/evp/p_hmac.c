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


#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/mem.h>

#include "../../evp_extra/internal.h"
#include "internal.h"

static int hmac_init(EVP_PKEY_CTX *ctx) {
  HMAC_PKEY_CTX *hctx;
  hctx = OPENSSL_zalloc(sizeof(HMAC_PKEY_CTX));
  if (hctx == NULL) {
    return 0;
  }
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
  if (!HMAC_CTX_copy_ex(&dctx->ctx, &sctx->ctx)) {
    OPENSSL_free(dctx);
    return 0;
  }
  return 1;
}

static void hmac_cleanup(EVP_PKEY_CTX *ctx) {
  HMAC_PKEY_CTX *hctx = ctx->data;
  OPENSSL_free(hctx);
}

static int hmac_ctrl(EVP_PKEY_CTX *ctx, int type, int p1, void *p2) {
  HMAC_PKEY_CTX *hctx = ctx->data;
  switch (type) {
    case EVP_PKEY_CTRL_MD:
      hctx->md = p2;
      break;
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
  out->keygen = NULL;
  out->sign_init = NULL;
  out->sign = NULL;
  out->sign_message = NULL;
  out->verify_init = NULL;
  out->verify = NULL;
  out->verify_message = NULL;
  out->verify_recover = NULL;
  out->encrypt = NULL;
  out->decrypt = NULL;
  out->derive = NULL;
  out->paramgen = NULL;
  out->ctrl = hmac_ctrl;
}

int used_for_hmac(EVP_MD_CTX *ctx) {
  return ctx->flags == EVP_MD_CTX_HMAC && ctx->pctx != NULL;
}

HMAC_KEY *HMAC_KEY_new(void) {
  HMAC_KEY *key = OPENSSL_zalloc(sizeof(HMAC_KEY));
  if (key == NULL) {
    return NULL;
  }
  return key;
}
