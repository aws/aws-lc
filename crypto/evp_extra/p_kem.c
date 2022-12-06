// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/evp.h>

#include <openssl/err.h>
#include <openssl/mem.h>

#include "../fipsmodule/evp/internal.h"
#include "../fipsmodule/delocate.h"
#include "../kem/internal.h"
#include "../internal.h"
#include "internal.h"

typedef struct {
  const KEM *kem;
} KEM_PKEY_CTX;

static int pkey_kem_init(EVP_PKEY_CTX *ctx) {
  KEM_PKEY_CTX *dctx;
  dctx = OPENSSL_malloc(sizeof(KEM_PKEY_CTX));
  if (dctx == NULL) {
    return 0;
  }
  OPENSSL_memset(dctx, 0, sizeof(KEM_PKEY_CTX));

  ctx->data = dctx;

  return 1;
}

static int pkey_kem_copy(EVP_PKEY_CTX *dst, EVP_PKEY_CTX *src) {
  KEM_PKEY_CTX *dctx, *sctx;
  if (!pkey_kem_init(dst)) {
    return 0;
  }
  sctx = src->data;
  dctx = dst->data;

  dctx->kem = sctx->kem;

  return 1;
}

static void pkey_kem_cleanup(EVP_PKEY_CTX *ctx) {
  OPENSSL_free(ctx->data);
}

static int pkey_kem_paramgen(EVP_PKEY_CTX *ctx, EVP_PKEY *pkey) {
  KEM_PKEY_CTX *dctx = ctx->data;
  if (dctx->kem == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
    return 0;
  }
  KEM_KEY *key = KEM_KEY_new();
  if (key == NULL ||
      !KEM_KEY_init(key, dctx->kem)) {
    KEM_KEY_free(key);
    return 0;
  }

  EVP_PKEY_assign(pkey, EVP_PKEY_KEM, key);
  return 1;
}

static int pkey_kem_keygen(EVP_PKEY_CTX *ctx, EVP_PKEY *pkey) {
  KEM_PKEY_CTX *dctx = ctx->data;
  const KEM *kem = dctx->kem;
  if (kem == NULL) {
    if (ctx->pkey == NULL) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
      return 0;
    }
    kem = KEM_KEY_get0_kem((KEM_KEY*)ctx->pkey->pkey.ptr);
  }

  KEM_KEY *key = KEM_KEY_new();
  if (key == NULL ||
      !KEM_KEY_init(key, kem) ||
      !kem->method->keygen(key->public_key, key->secret_key) ||
      !EVP_PKEY_assign(pkey, EVP_PKEY_KEM, key)) {
    KEM_KEY_free(key);
    return 0;
  }

  key->has_secret_key = 1;

  return 1;
}

static int pkey_kem_encapsulate(EVP_PKEY_CTX *ctx,
                                uint8_t *ciphertext,
                                size_t  *ciphertext_len,
                                uint8_t *shared_secret,
                                size_t  *shared_secret_len) {
  KEM_PKEY_CTX *dctx = ctx->data;
  const KEM *kem = dctx->kem;
  if (kem == NULL) {
    if (ctx->pkey == NULL) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
      return 0;
    }
    kem = KEM_KEY_get0_kem((KEM_KEY*)ctx->pkey->pkey.ptr);
  }

  // Caller is getting parameter values.
  if (ciphertext == NULL) {
    *ciphertext_len = kem->ciphertext_len;
    *shared_secret_len = kem->shared_secret_len;
    return 1;
  }

  // The output buffers need to be large enough.
  if (*ciphertext_len < kem->ciphertext_len ||
      *shared_secret_len < kem->shared_secret_len) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
      return 0;
  }

  // Check that the context is properly configured.
  if (ctx->pkey == NULL ||
      ctx->pkey->pkey.ptr == NULL ||
      ctx->pkey->type != EVP_PKEY_KEM) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATON_NOT_INITIALIZED);
      return 0;
  }

  KEM_KEY *key = ctx->pkey->pkey.kem;
  if (!kem->method->encaps(ciphertext, shared_secret, key->public_key)) {
    return 0;
  }

  // The size of the ciphertext and the shared secret
  // that has been writen to the output buffers.
  *ciphertext_len = kem->ciphertext_len;
  *shared_secret_len = kem->shared_secret_len;

  return 1;
}

static int pkey_kem_decapsulate(EVP_PKEY_CTX *ctx,
                                uint8_t *shared_secret,
                                size_t  *shared_secret_len,
                                const uint8_t *ciphertext,
                                size_t ciphertext_len) {
  KEM_PKEY_CTX *dctx = ctx->data;
  const KEM *kem = dctx->kem;
  if (kem == NULL) {
    if (ctx->pkey == NULL) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
      return 0;
    }
    kem = KEM_KEY_get0_kem((KEM_KEY*)ctx->pkey->pkey.ptr);
  }

  // Caller is getting parameter values.
  if (shared_secret == NULL) {
    *shared_secret_len = kem->shared_secret_len;
    return 1;
  }

  // The input and output buffers need to be large enough.
  if (ciphertext_len < kem->ciphertext_len ||
      *shared_secret_len < kem->shared_secret_len) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
      return 0;
  }

  // Check that the context is properly configured.
  if (ctx->pkey == NULL ||
      ctx->pkey->pkey.ptr == NULL ||
      ctx->pkey->type != EVP_PKEY_KEM) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATON_NOT_INITIALIZED);
      return 0;
  }

  KEM_KEY *key = ctx->pkey->pkey.kem;
  if (!key->has_secret_key) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NO_KEY_SET);
    return 0;
  }

  if (!kem->method->decaps(shared_secret, ciphertext, key->secret_key)) {
    return 0;
  }

  // The size of the shared secret that has been writen to the output buffer.
  *shared_secret_len = kem->shared_secret_len;

  return 1;
}

const EVP_PKEY_METHOD kem_pkey_meth = {
    EVP_PKEY_KEM,
    pkey_kem_init,
    pkey_kem_copy,
    pkey_kem_cleanup,
    pkey_kem_keygen,
    NULL,
    NULL,
    NULL,
    NULL,
    NULL,
    NULL,
    NULL,
    NULL,
    NULL,
    NULL,
    pkey_kem_paramgen,
    NULL,
    pkey_kem_encapsulate,
    pkey_kem_decapsulate,
};


int EVP_PKEY_CTX_set_kem_params_kem_nid(EVP_PKEY_CTX *ctx, int nid) {
  const KEM *kem = KEM_find_kem_by_nid(nid);
  if (kem == NULL) {
    return 0;
  }
  // TODO(awslc): should we handle the case when ctx already has an EVP_PKEY
  // with its own type/nid.

  KEM_PKEY_CTX *dctx = ctx->data;
  dctx->kem = kem;

  return 1;
}
