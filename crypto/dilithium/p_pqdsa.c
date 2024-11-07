// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/evp.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include "../crypto/internal.h"
#include "../fipsmodule/evp/internal.h"
#include "../evp_extra/internal.h"
#include "ml_dsa.h"
#include "internal.h"

// PQDSA PKEY functions

typedef struct {
  const PQDSA *pqdsa;
} PQDSA_PKEY_CTX;

static int pkey_pqdsa_init(EVP_PKEY_CTX *ctx) {
  PQDSA_PKEY_CTX *dctx;
  dctx = OPENSSL_zalloc(sizeof(PQDSA_PKEY_CTX));
  if (dctx == NULL) {
    return 0;
  }

  ctx->data = dctx;

  return 1;
}

static void pkey_pqdsa_cleanup(EVP_PKEY_CTX *ctx) {
  OPENSSL_free(ctx->data);
}

static int pkey_pqdsa_keygen(EVP_PKEY_CTX *ctx, EVP_PKEY *pkey) {
  GUARD_PTR(ctx);
  PQDSA_PKEY_CTX *dctx = ctx->data;
  GUARD_PTR(dctx);
  const PQDSA *pqdsa = dctx->pqdsa;
  if (pqdsa == NULL) {
    if (ctx->pkey == NULL) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
      return 0;
    }
    pqdsa = PQDSA_KEY_get0_dsa(ctx->pkey->pkey.pqdsa_key);
  }

  PQDSA_KEY *key = PQDSA_KEY_new();
  if (key == NULL ||
      !PQDSA_KEY_init(key, pqdsa) ||
      !pqdsa->method->keygen(key->public_key, key->secret_key) ||
      !EVP_PKEY_assign_PQDSA_KEY(pkey, key)) {
    PQDSA_KEY_free(key);
    return 0;
      }
  return 1;
}

static int pkey_pqdsa_sign_signature(EVP_PKEY_CTX *ctx, uint8_t *sig,
                                     size_t *siglen, const uint8_t *tbs,
                                     size_t tbslen) {
  PQDSA_PKEY_CTX *dctx = ctx->data;
  const PQDSA *pqdsa = dctx->pqdsa;
  if (pqdsa == NULL) {
    if (ctx->pkey == NULL) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
      return 0;
    }
    pqdsa = PQDSA_KEY_get0_dsa(ctx->pkey->pkey.pqdsa_key);
  }

  // Caller is getting parameter values.
  if (sig == NULL) {
    if (pqdsa != NULL) {
      *siglen = pqdsa->signature_len;
      return 1;
    }
  }

  if (*siglen != pqdsa->signature_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
    return 0;
  }

  // Check that the context is properly configured.
  if (ctx->pkey == NULL ||
      ctx->pkey->pkey.pqdsa_key == NULL ||
      ctx->pkey->type != EVP_PKEY_PQDSA) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATON_NOT_INITIALIZED);
    return 0;
  }

  PQDSA_KEY *key = ctx->pkey->pkey.pqdsa_key;
  if (!key->secret_key) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NO_KEY_SET);
    return 0;
  }

  if (pqdsa->method->sign(key->secret_key, sig, siglen, tbs, tbslen, NULL, 0) != 0) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_INTERNAL_ERROR);
    return 0;
  }
  return 1;
}

static int pkey_pqdsa_verify_signature(EVP_PKEY_CTX *ctx, const uint8_t *sig,
                                       size_t siglen, const uint8_t *tbs,
                                       size_t tbslen) {
  PQDSA_PKEY_CTX *dctx = ctx->data;
  const PQDSA *pqdsa = dctx->pqdsa;

  if (pqdsa == NULL) {
    if (ctx->pkey == NULL) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
      return 0;
    }

    pqdsa = PQDSA_KEY_get0_dsa(ctx->pkey->pkey.pqdsa_key);
  }
  // Check that the context is properly configured.
  if (ctx->pkey == NULL ||
    ctx->pkey->pkey.pqdsa_key == NULL ||
    ctx->pkey->type != EVP_PKEY_PQDSA) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATON_NOT_INITIALIZED);
    return 0;
  }

  PQDSA_KEY *key = ctx->pkey->pkey.pqdsa_key;

  if (siglen != pqdsa->signature_len ||
      pqdsa->method->verify(key->public_key, sig, siglen, tbs, tbslen, NULL, 0) != 0) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_SIGNATURE);
    return 0;
  }

  return 1;
}

// This function sets pqdsa parameters defined by |nid| in |pkey|.
// If |pkey| already has a public key set, this public key is preserved.
int EVP_PKEY_pqdsa_set_params(EVP_PKEY *pkey, int nid) {
  const PQDSA *pqdsa = PQDSA_find_dsa_by_nid(nid);

  if (pqdsa == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_UNSUPPORTED_ALGORITHM);
    return 0;
  }

  // if the public key has already been set either by EVP_parse_public_key or
  // some other method that returns a PKEY without setting params, then
  // we preserve that PKEY and just populate the params
  if (pkey->pkey.pqdsa_key != NULL) {
    pkey->pkey.pqdsa_key->pqdsa = pqdsa;
    return 1;
  }

  evp_pkey_set_method(pkey, &pqdsa_asn1_meth);

  PQDSA_KEY *key = PQDSA_KEY_new();
  if (key == NULL) {
    // PQDSA_KEY_new sets the appropriate error.
    return 0;
  }

  key->pqdsa = pqdsa;
  pkey->pkey.pqdsa_key = key;

  return 1;
}

// Takes an EVP_PKEY_CTX object |ctx| and sets pqdsa parameters defined
// by |nid|
int EVP_PKEY_CTX_pqdsa_set_params(EVP_PKEY_CTX *ctx, int nid) {
  if (ctx == NULL || ctx->data == NULL) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_PASSED_NULL_PARAMETER);
    return 0;
  }

  // It's not allowed to change context parameters if
  // a PKEY is already associated with the context.
  if (ctx->pkey != NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_OPERATION);
    return 0;
  }

  const PQDSA *pqdsa = PQDSA_find_dsa_by_nid(nid);
  if (pqdsa == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_UNSUPPORTED_ALGORITHM);
    return 0;
  }

  PQDSA_PKEY_CTX *dctx = ctx->data;
  dctx->pqdsa = pqdsa;

  return 1;
}

const EVP_PKEY_METHOD pqdsa_pkey_meth = {
  EVP_PKEY_PQDSA,
  pkey_pqdsa_init /* init */,
  NULL /* copy */,
  pkey_pqdsa_cleanup /* cleanup */,
  pkey_pqdsa_keygen,
  NULL /* sign_init */,
  NULL /* sign */,
  pkey_pqdsa_sign_signature,
  NULL /* verify_init */,
  NULL /* verify */,
  pkey_pqdsa_verify_signature,
  NULL /* verify_recover */,
  NULL /* encrypt */,
  NULL /* decrypt */,
  NULL /* derive */,
  NULL /* paramgen */,
  NULL /* ctrl */,
  NULL /* ctrl_str */,
  NULL /* keygen deterministic */,
  NULL /* encapsulate deterministic */,
  NULL /* encapsulate */,
  NULL /* decapsulate */,
};
