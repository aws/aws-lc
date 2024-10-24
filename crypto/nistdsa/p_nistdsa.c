// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/evp.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include "../crypto/internal.h"
#include "../evp_extra/internal.h"
#include "../fipsmodule/delocate.h"
#include "../fipsmodule/evp/internal.h"
#include "../ml_dsa/ml_dsa.h"
#include "internal.h"

typedef struct {
  const NISTDSA *nistdsa;
} NISTDSA_PKEY_CTX;

static void pkey_nistdsa_cleanup(EVP_PKEY_CTX *ctx) {
  OPENSSL_free(ctx->data);
}

static int pkey_nistdsa_init(EVP_PKEY_CTX *ctx) {
  NISTDSA_PKEY_CTX *dctx;
  dctx = OPENSSL_zalloc(sizeof(NISTDSA_PKEY_CTX));
  if (dctx == NULL) {
    return 0;
  }

  ctx->data = dctx;

  return 1;
}

static int pkey_nistdsa_keygen(EVP_PKEY_CTX *ctx, EVP_PKEY *pkey) {
  GUARD_PTR(ctx);
  NISTDSA_PKEY_CTX *dctx = ctx->data;
  GUARD_PTR(dctx);
  const NISTDSA *nistdsa = dctx->nistdsa;
  if (nistdsa == NULL) {
    if (ctx->pkey == NULL) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
      return 0;
    }
    nistdsa = NISTDSA_KEY_get0_sig(ctx->pkey->pkey.nistdsa_key);
  }

  NISTDSA_KEY *key = NISTDSA_KEY_new();
  if (key == NULL ||
      !NISTDSA_KEY_init(key, nistdsa) ||
      !nistdsa->method->keygen(key->public_key, key->secret_key) ||
      !EVP_PKEY_set_type(pkey, EVP_PKEY_NISTDSA)) {
    NISTDSA_KEY_free(key);
    return 0;
      }

  pkey->pkey.nistdsa_key = key;
  return 1;
}

static int pkey_nistdsa_sign_message(EVP_PKEY_CTX *ctx, uint8_t *sig,
                                        size_t *siglen, const uint8_t *tbs,
                                        size_t tbslen) {
  NISTDSA_PKEY_CTX *dctx = ctx->data;
  const NISTDSA *nistdsa = dctx->nistdsa;
  if (nistdsa == NULL) {
    if (ctx->pkey == NULL) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
      return 0;
    }
    nistdsa = NISTDSA_KEY_get0_sig(ctx->pkey->pkey.nistdsa_key);
  }

  // Caller is getting parameter values.
  if (sig == NULL) {
    *siglen = nistdsa->signature_len;
    return 1;
  }

  if (*siglen < nistdsa->signature_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
    return 0;
  }

  // Check that the context is properly configured.
  if (ctx->pkey == NULL ||
      ctx->pkey->pkey.nistdsa_key == NULL ||
      ctx->pkey->type != EVP_PKEY_NISTDSA) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATON_NOT_INITIALIZED);
    return 0;
      }

  NISTDSA_KEY *key = ctx->pkey->pkey.nistdsa_key;
  if (!key->secret_key) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NOT_A_PRIVATE_KEY);
    return 0;
  }

  if (nistdsa->method->sign(sig, siglen, tbs, tbslen, NULL, 0, key->secret_key) != 0) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_INTERNAL_ERROR);
    return 0;
  }
  return 1;
}

static int pkey_nistdsa_verify_message(EVP_PKEY_CTX *ctx, const uint8_t *sig,
                                          size_t siglen, const uint8_t *tbs,
                                          size_t tbslen) {
  NISTDSA_PKEY_CTX *dctx = ctx->data;
  const NISTDSA *nistdsa = dctx->nistdsa;

  if (nistdsa == NULL) {
    if (ctx->pkey == NULL) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
      return 0;
    }

    nistdsa = NISTDSA_KEY_get0_sig(ctx->pkey->pkey.nistdsa_key);
  }
  // Check that the context is properly configured.
  if (ctx->pkey == NULL ||
    ctx->pkey->pkey.nistdsa_key == NULL ||
    ctx->pkey->type != EVP_PKEY_NISTDSA) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATON_NOT_INITIALIZED);
    return 0;
    }

  NISTDSA_KEY *key = ctx->pkey->pkey.nistdsa_key;

  if (siglen != nistdsa->signature_len ||
      nistdsa->method->verify(tbs, tbslen, sig, siglen, NULL, 0, key->public_key) != 0) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_SIGNATURE);
    return 0;
      }

  return 1;
}

const EVP_PKEY_METHOD nistdsa_pkey_meth = {
  EVP_PKEY_NISTDSA,
  pkey_nistdsa_init /* init */,
  NULL /* copy */,
  pkey_nistdsa_cleanup /* cleanup */,
  pkey_nistdsa_keygen,
  NULL /* sign_init */,
  NULL /* sign */,
  pkey_nistdsa_sign_message,
  NULL /* verify_init */,
  NULL /* verify */,
  pkey_nistdsa_verify_message,
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

// Additional NISTDSA specific EVP functions.

// This function sets nistdsa parameters defined by |nid| in |pkey|.
// If |pkey| already has a public key set, this public key is preserved.
int EVP_PKEY_nistdsa_set_params(EVP_PKEY *pkey, int nid) {
  const NISTDSA *nistdsa = SIG_find_dsa_by_nid(nid);

  if (nistdsa == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_UNSUPPORTED_ALGORITHM);
    return 0;
  }

  // if the public key has already been set either by EVP_parse_public_key or
  // some other method that returns a PKEY without setting params, then
  // we preserve that PKEY and just populate the params
  if (pkey->pkey.nistdsa_key != NULL) {
    pkey->pkey.nistdsa_key->nistdsa = nistdsa;
    return 1;
  }

  evp_pkey_set_method(pkey, &nistdsa_asn1_meth);

  NISTDSA_KEY *key = NISTDSA_KEY_new();
  if (key == NULL) {
    // NISTDSA_KEYnew sets the appropriate error.
    return 0;
  }

  key->nistdsa = nistdsa;
  pkey->pkey.nistdsa_key = key;

  return 1;
}

// Takes an EVP_PKEY_CTX object |ctx| and sets nistdsa parameters defined
// by |nid|
int EVP_PKEY_CTX_nistdsa_set_params(EVP_PKEY_CTX *ctx, int nid) {
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

  const NISTDSA *nistdsa = SIG_find_dsa_by_nid(nid);
  if (nistdsa == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_UNSUPPORTED_ALGORITHM);
    return 0;
  }

  NISTDSA_PKEY_CTX *dctx = ctx->data;
  dctx->nistdsa = nistdsa;

  return 1;
}
