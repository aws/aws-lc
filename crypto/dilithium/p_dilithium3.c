// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/evp.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include "../crypto/internal.h"
#include "../fipsmodule/evp/internal.h"
#include "../evp_extra/internal.h"
#include "sig_dilithium.h"

static int pkey_dilithium3_keygen(EVP_PKEY_CTX *ctx, EVP_PKEY *pkey) {
  DILITHIUM3_KEY *key = OPENSSL_malloc(sizeof(DILITHIUM3_KEY));
  if (key == NULL) {
    goto err;
  }
  key->pub = OPENSSL_malloc(DILITHIUM3_PUBLIC_KEY_BYTES);
  if (key->pub == NULL) {
    goto err;
  }
  key->priv = OPENSSL_malloc(DILITHIUM3_PRIVATE_KEY_BYTES);
  if (key->priv == NULL) {
    goto err;
  }

  if (pkey == NULL || ctx == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_MISSING_PARAMETERS);
    goto err;
  }

  if (!EVP_PKEY_set_type(pkey, EVP_PKEY_DILITHIUM3)) {
    goto err;
  }

  if (DILITHIUM3_keypair(key->pub, key->priv) != 0) {
    goto err;
  }

  OPENSSL_free(pkey->pkey.ptr);
  pkey->pkey.ptr = key;
  return 1;

err:
  if (key != NULL) {
    OPENSSL_free(key->pub);
    OPENSSL_free(key->priv);
  }
  OPENSSL_free(key);
  return 0;

}

static int pkey_dilithium3_sign_message(EVP_PKEY_CTX *ctx, uint8_t *sig,
                                        size_t *siglen, const uint8_t *tbs,
                                        size_t tbslen) {
  if (ctx == NULL || ctx->pkey->pkey.ptr == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_MISSING_PARAMETERS);
    return 0;
  }

  DILITHIUM3_KEY *key = ctx->pkey->pkey.ptr;

  if (!key->priv) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NOT_A_PRIVATE_KEY);
    return 0;
  }
  // Caller is getting parameter values.
  if (sig == NULL) {
    *siglen = DILITHIUM3_SIGNATURE_BYTES;
    return 1;
  }

  if (*siglen < DILITHIUM3_SIGNATURE_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
    return 0;
  }

  if (DILITHIUM3_sign(sig, siglen, tbs, tbslen, key->priv) != 0) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_INTERNAL_ERROR);
    return 0;
  }
  return 1;
}

static int pkey_dilithium3_verify_message(EVP_PKEY_CTX *ctx, const uint8_t *sig,
                                          size_t siglen, const uint8_t *tbs,
                                          size_t tbslen) {
  if (ctx == NULL || ctx->pkey->pkey.ptr == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_MISSING_PARAMETERS);
    return 0;
  }

  DILITHIUM3_KEY *key = ctx->pkey->pkey.ptr;

  if (siglen != DILITHIUM3_SIGNATURE_BYTES ||
      DILITHIUM3_verify(tbs, tbslen, sig, siglen, key->pub) != 0) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_SIGNATURE);
    return 0;
  }
  return 1;
}

const EVP_PKEY_METHOD dilithium3_pkey_meth = {
    EVP_PKEY_DILITHIUM3,
    NULL /* init */,
    NULL /* copy */,
    NULL /* cleanup */,
    pkey_dilithium3_keygen,
    NULL /* sign_init */,
    NULL /* sign */,
    pkey_dilithium3_sign_message,
    NULL /* verify_init */,
    NULL /* verify */,
    pkey_dilithium3_verify_message,
    NULL /* verify_recover */,
    NULL /* encrypt */,
    NULL /* decrypt */,
    NULL /* derive */,
    NULL /* paramgen */,
    NULL /* ctrl */,
    NULL /* keygen deterministic */,
    NULL /* encapsulate deterministic */,
    NULL /* encapsulate */,
    NULL /* decapsulate */,
};
