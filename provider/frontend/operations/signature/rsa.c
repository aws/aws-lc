// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// Front side: the RSA signature's dispatch slots, PKCS#1 v1.5 and PSS, over
// keydata from either RSA key manager.

#include <openssl/core_dispatch.h>
#include <openssl/core_names.h>
#include <openssl/params.h>
#include <openssl/rsa.h>

#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "boundary.h"
#include "boundary/operations/rsa.h"
#include "boundary/utils.h"
#include "frontend/operations/rsa.h"
#include "frontend/operations/signature/signature.h"
#include "frontend/provider.h"
#include "frontend/utils.h"

#define AWSLC_PROV_RSA_SIG_NAME "RSA"
// Room for the longest AlgorithmIdentifier, RSASSA-PSS with every field set.
#define AWSLC_PROV_RSA_SIG_ALGORITHM_ID_SIZE 128

typedef struct {
  AWSLC_PROV_CTX *provctx;
  // This context's own reference, kept for a re-init that names no key.
  void *rsa;
  int pss;
  int restricted;
  AWSLC_PROV_RSA_SIG_OPERATION operation;
  // NULL until an init.
  void *backend;
  int fips_approved;
} AWSLC_PROV_RSA_SIG_CTX;

static const struct {
  int openssl;
  const char *name;
  AWSLC_PROV_RSA_PADDING padding;
} awslc_prov_rsa_sig_paddings[] = {
    {RSA_PKCS1_PADDING, OSSL_PKEY_RSA_PAD_MODE_PKCSV15,
     AWSLC_PROV_RSA_PADDING_PKCS1},
    {RSA_NO_PADDING, OSSL_PKEY_RSA_PAD_MODE_NONE, AWSLC_PROV_RSA_PADDING_NONE},
    {RSA_PKCS1_PSS_PADDING, OSSL_PKEY_RSA_PAD_MODE_PSS,
     AWSLC_PROV_RSA_PADDING_PSS},
};

static const struct {
  int openssl;
  const char *name;
  int saltlen;
} awslc_prov_rsa_sig_saltlens[] = {
    {RSA_PSS_SALTLEN_DIGEST, OSSL_PKEY_RSA_PSS_SALT_LEN_DIGEST,
     AWSLC_PROV_RSA_PSS_SALTLEN_DIGEST},
    {RSA_PSS_SALTLEN_AUTO, OSSL_PKEY_RSA_PSS_SALT_LEN_AUTO,
     AWSLC_PROV_RSA_PSS_SALTLEN_AUTO},
    {RSA_PSS_SALTLEN_MAX, OSSL_PKEY_RSA_PSS_SALT_LEN_MAX,
     AWSLC_PROV_RSA_PSS_SALTLEN_MAX},
    {RSA_PSS_SALTLEN_AUTO_DIGEST_MAX,
     OSSL_PKEY_RSA_PSS_SALT_LEN_AUTO_DIGEST_MAX,
     AWSLC_PROV_RSA_PSS_SALTLEN_AUTO_DIGEST_MAX},
};

#define AWSLC_PROV_COUNT(array) (sizeof(array) / sizeof((array)[0]))

static const OSSL_PARAM awslc_prov_rsa_sig_settable[] = {
    OSSL_PARAM_utf8_string(OSSL_SIGNATURE_PARAM_DIGEST, NULL, 0),
    OSSL_PARAM_utf8_string(OSSL_SIGNATURE_PARAM_PAD_MODE, NULL, 0),
    OSSL_PARAM_utf8_string(OSSL_SIGNATURE_PARAM_MGF1_DIGEST, NULL, 0),
    OSSL_PARAM_utf8_string(OSSL_SIGNATURE_PARAM_PSS_SALTLEN, NULL, 0),
    OSSL_PARAM_END};

// A digest operation's digest is fixed at init.
static const OSSL_PARAM awslc_prov_rsa_sig_settable_no_digest[] = {
    OSSL_PARAM_utf8_string(OSSL_SIGNATURE_PARAM_PAD_MODE, NULL, 0),
    OSSL_PARAM_utf8_string(OSSL_SIGNATURE_PARAM_MGF1_DIGEST, NULL, 0),
    OSSL_PARAM_utf8_string(OSSL_SIGNATURE_PARAM_PSS_SALTLEN, NULL, 0),
    OSSL_PARAM_END};

static const OSSL_PARAM awslc_prov_rsa_sig_gettable[] = {
    OSSL_PARAM_octet_string(OSSL_SIGNATURE_PARAM_ALGORITHM_ID, NULL, 0),
    OSSL_PARAM_utf8_string(OSSL_SIGNATURE_PARAM_PAD_MODE, NULL, 0),
    OSSL_PARAM_utf8_string(OSSL_SIGNATURE_PARAM_DIGEST, NULL, 0),
    OSSL_PARAM_utf8_string(OSSL_SIGNATURE_PARAM_MGF1_DIGEST, NULL, 0),
    OSSL_PARAM_utf8_string(OSSL_SIGNATURE_PARAM_PSS_SALTLEN, NULL, 0),
    OSSL_PARAM_int(OSSL_SIGNATURE_PARAM_FIPS_APPROVED_INDICATOR, NULL),
    OSSL_PARAM_END};

static OSSL_FUNC_signature_newctx_fn awslc_prov_rsa_sig_newctx;
static OSSL_FUNC_signature_freectx_fn awslc_prov_rsa_sig_freectx;
static OSSL_FUNC_signature_dupctx_fn awslc_prov_rsa_sig_dupctx;
static OSSL_FUNC_signature_sign_init_fn awslc_prov_rsa_sig_sign_init;
static OSSL_FUNC_signature_sign_fn awslc_prov_rsa_sig_sign_op;
static OSSL_FUNC_signature_verify_init_fn awslc_prov_rsa_sig_verify_init;
static OSSL_FUNC_signature_verify_fn awslc_prov_rsa_sig_verify_op;
static OSSL_FUNC_signature_verify_recover_init_fn
    awslc_prov_rsa_sig_verify_recover_init;
static OSSL_FUNC_signature_verify_recover_fn
    awslc_prov_rsa_sig_verify_recover_op;
static OSSL_FUNC_signature_digest_sign_init_fn
    awslc_prov_rsa_sig_digest_sign_init;
static OSSL_FUNC_signature_digest_sign_update_fn
    awslc_prov_rsa_sig_digest_update;
static OSSL_FUNC_signature_digest_sign_final_fn
    awslc_prov_rsa_sig_digest_sign_final;
static OSSL_FUNC_signature_digest_verify_init_fn
    awslc_prov_rsa_sig_digest_verify_init;
static OSSL_FUNC_signature_digest_verify_final_fn
    awslc_prov_rsa_sig_digest_verify_final;
static OSSL_FUNC_signature_get_ctx_params_fn awslc_prov_rsa_sig_get_ctx_params;
static OSSL_FUNC_signature_gettable_ctx_params_fn
    awslc_prov_rsa_sig_gettable_ctx_params;
static OSSL_FUNC_signature_set_ctx_params_fn awslc_prov_rsa_sig_set_ctx_params;
static OSSL_FUNC_signature_settable_ctx_params_fn
    awslc_prov_rsa_sig_settable_ctx_params;

static int awslc_prov_rsa_sig_is_digest_op(const AWSLC_PROV_RSA_SIG_CTX *ctx) {
  return ctx->operation == AWSLC_PROV_RSA_SIG_DIGEST_SIGN ||
         ctx->operation == AWSLC_PROV_RSA_SIG_DIGEST_VERIFY;
}

static void *awslc_prov_rsa_sig_newctx(void *provctx, const char *propq) {
  AWSLC_PROV_RSA_SIG_CTX *ctx = NULL;
  AWSLC_PROV_CALL call;

  // The digests are AWS-LC's own, so there is nothing to fetch with |propq|.
  (void)propq;
  awslc_prov_call_begin(&call, provctx);
  ctx = awslc_prov_zalloc(sizeof(*ctx));
  if (!AWSLC_PROV_CALL_END(&call, ctx != NULL, AWSLC_PROV_RSA_SIG_NAME)) {
    return NULL;
  }
  ctx->provctx = (AWSLC_PROV_CTX *)provctx;
  return ctx;
}

static void awslc_prov_rsa_sig_freectx(void *vctx) {
  AWSLC_PROV_RSA_SIG_CTX *ctx = (AWSLC_PROV_RSA_SIG_CTX *)vctx;

  if (ctx == NULL) {
    return;
  }
  awslc_prov_rsa_sig_free(ctx->backend);
  awslc_prov_rsa_free(ctx->rsa);
  awslc_prov_clear_free(ctx, sizeof(*ctx));
}

static void *awslc_prov_rsa_sig_dupctx(void *vctx) {
  const AWSLC_PROV_RSA_SIG_CTX *ctx = (const AWSLC_PROV_RSA_SIG_CTX *)vctx;
  AWSLC_PROV_RSA_SIG_CTX *copy = NULL;
  AWSLC_PROV_CALL call;
  int ok = 0;

  if (ctx == NULL) {
    return NULL;
  }
  awslc_prov_call_begin(&call, ctx->provctx);
  copy = awslc_prov_zalloc(sizeof(*copy));
  if (copy != NULL) {
    *copy = *ctx;
    copy->rsa = NULL;
    copy->backend = NULL;
    if (ctx->rsa == NULL || awslc_prov_rsa_up_ref(ctx->rsa)) {
      copy->rsa = ctx->rsa;
      ok = ctx->backend == NULL ||
           (copy->backend = awslc_prov_rsa_sig_dup(ctx->backend)) != NULL;
    }
  }
  if (!AWSLC_PROV_CALL_END(&call, ok, AWSLC_PROV_RSA_SIG_NAME)) {
    awslc_prov_rsa_sig_freectx(copy);
    return NULL;
  }
  return copy;
}

static int awslc_prov_rsa_sig_get_padding(const OSSL_PARAM *p,
                                          AWSLC_PROV_RSA_PADDING *out) {
  int mode = 0;
  const char *name = NULL;

  if (p->data_type == OSSL_PARAM_INTEGER && OSSL_PARAM_get_int(p, &mode)) {
    for (size_t i = 0; i < AWSLC_PROV_COUNT(awslc_prov_rsa_sig_paddings); i++) {
      if (awslc_prov_rsa_sig_paddings[i].openssl == mode) {
        *out = awslc_prov_rsa_sig_paddings[i].padding;
        return 1;
      }
    }
  } else if (OSSL_PARAM_get_utf8_string_ptr(p, &name)) {
    for (size_t i = 0; i < AWSLC_PROV_COUNT(awslc_prov_rsa_sig_paddings); i++) {
      if (strcmp(awslc_prov_rsa_sig_paddings[i].name, name) == 0) {
        *out = awslc_prov_rsa_sig_paddings[i].padding;
        return 1;
      }
    }
  }
  return 0;
}

static int awslc_prov_rsa_sig_get_saltlen(const OSSL_PARAM *p, int *out) {
  int value = 0;
  const char *text = NULL;

  if (p->data_type == OSSL_PARAM_INTEGER) {
    if (!OSSL_PARAM_get_int(p, &value)) {
      return 0;
    }
  } else if (OSSL_PARAM_get_utf8_string_ptr(p, &text)) {
    char *end = NULL;
    long parsed = 0;

    for (size_t i = 0; i < AWSLC_PROV_COUNT(awslc_prov_rsa_sig_saltlens); i++) {
      if (strcmp(awslc_prov_rsa_sig_saltlens[i].name, text) == 0) {
        *out = awslc_prov_rsa_sig_saltlens[i].saltlen;
        return 1;
      }
    }
    errno = 0;
    parsed = strtol(text, &end, 10);
    if (end == text || *end != '\0' || errno != 0 || parsed < INT_MIN ||
        parsed > INT_MAX) {
      return 0;
    }
    value = (int)parsed;
  } else {
    return 0;
  }
  // libcrypto passes the special lengths as their numbers, such as "-4".
  for (size_t i = 0; i < AWSLC_PROV_COUNT(awslc_prov_rsa_sig_saltlens); i++) {
    if (awslc_prov_rsa_sig_saltlens[i].openssl == value) {
      *out = awslc_prov_rsa_sig_saltlens[i].saltlen;
      return 1;
    }
  }
  if (value < 0) {
    return 0;
  }
  *out = value;
  return 1;
}

static int awslc_prov_rsa_sig_set_ctx_params(void *vctx,
                                             const OSSL_PARAM params[]) {
  AWSLC_PROV_RSA_SIG_CTX *ctx = (AWSLC_PROV_RSA_SIG_CTX *)vctx;
  const OSSL_PARAM *pad_param = NULL;
  const OSSL_PARAM *saltlen_param = NULL;
  AWSLC_PROV_RSA_PADDING padding = AWSLC_PROV_RSA_PADDING_PKCS1;
  const char *digest = NULL;
  const char *mgf1_digest = NULL;
  int saltlen = 0;
  const char *step = NULL;
  AWSLC_PROV_CALL call;
  int ok = 1;

  if (ctx == NULL) {
    return 0;
  }
  if (params == NULL || params[0].key == NULL) {
    return 1;
  }
  if (ctx->backend == NULL) {
    AWSLC_PROV_ERROR_RAISE(ctx->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           AWSLC_PROV_RSA_SIG_NAME);
    return 0;
  }
  pad_param = OSSL_PARAM_locate_const(params, OSSL_SIGNATURE_PARAM_PAD_MODE);
  if (pad_param != NULL &&
      !awslc_prov_rsa_sig_get_padding(pad_param, &padding)) {
    AWSLC_PROV_ERROR_RAISE(ctx->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           OSSL_SIGNATURE_PARAM_PAD_MODE);
    return 0;
  }
  saltlen_param =
      OSSL_PARAM_locate_const(params, OSSL_SIGNATURE_PARAM_PSS_SALTLEN);
  if (saltlen_param != NULL &&
      !awslc_prov_rsa_sig_get_saltlen(saltlen_param, &saltlen)) {
    AWSLC_PROV_ERROR_RAISE(ctx->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           OSSL_SIGNATURE_PARAM_PSS_SALTLEN);
    return 0;
  }
  if (!awslc_prov_param_get_digest(
          ctx->provctx,
          OSSL_PARAM_locate_const(params, OSSL_SIGNATURE_PARAM_DIGEST),
          &digest) ||
      !awslc_prov_param_get_digest(
          ctx->provctx,
          OSSL_PARAM_locate_const(params, OSSL_SIGNATURE_PARAM_MGF1_DIGEST),
          &mgf1_digest)) {
    return 0;
  }

  awslc_prov_call_begin(&call, ctx->provctx);
  if (pad_param != NULL) {
    step = OSSL_SIGNATURE_PARAM_PAD_MODE;
    ok = awslc_prov_rsa_sig_set_padding(ctx->backend, padding);
  }
  if (ok && digest != NULL) {
    step = OSSL_SIGNATURE_PARAM_DIGEST;
    if (awslc_prov_rsa_sig_is_digest_op(ctx)) {
      const char *fixed = awslc_prov_rsa_sig_digest(ctx->backend);

      if (fixed == NULL || strcmp(digest, fixed) != 0) {
        (void)AWSLC_PROV_CALL_END(&call, 1, step);
        AWSLC_PROV_ERROR_RAISE(ctx->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                               step);
        return 0;
      }
    } else {
      ok = awslc_prov_rsa_sig_set_digest(ctx->backend, digest);
    }
  }
  if (ok && mgf1_digest != NULL) {
    step = OSSL_SIGNATURE_PARAM_MGF1_DIGEST;
    ok = awslc_prov_rsa_sig_set_mgf1_digest(ctx->backend, mgf1_digest);
  }
  if (ok && saltlen_param != NULL) {
    step = OSSL_SIGNATURE_PARAM_PSS_SALTLEN;
    ok = awslc_prov_rsa_sig_set_pss_saltlen(ctx->backend, saltlen);
  }
  return AWSLC_PROV_CALL_END(&call, ok, step);
}

static const OSSL_PARAM *awslc_prov_rsa_sig_settable_ctx_params(void *vctx,
                                                                void *provctx) {
  const AWSLC_PROV_RSA_SIG_CTX *ctx = (const AWSLC_PROV_RSA_SIG_CTX *)vctx;

  (void)provctx;
  if (ctx != NULL && ctx->backend != NULL &&
      awslc_prov_rsa_sig_is_digest_op(ctx)) {
    return awslc_prov_rsa_sig_settable_no_digest;
  }
  return awslc_prov_rsa_sig_settable;
}

static int awslc_prov_rsa_sig_set_padding_param(const AWSLC_PROV_CTX *provctx,
                                                OSSL_PARAM *p, int padding) {
  for (size_t i = 0; i < AWSLC_PROV_COUNT(awslc_prov_rsa_sig_paddings); i++) {
    if ((int)awslc_prov_rsa_sig_paddings[i].padding != padding) {
      continue;
    }
    if (p->data_type == OSSL_PARAM_INTEGER
            ? OSSL_PARAM_set_int(p, awslc_prov_rsa_sig_paddings[i].openssl)
            : OSSL_PARAM_set_utf8_string(p,
                                         awslc_prov_rsa_sig_paddings[i].name)) {
      return 1;
    }
    break;
  }
  AWSLC_PROV_ERROR_RAISE(provctx, AWSLC_PROV_R_INVALID_PARAMETER, p->key);
  return 0;
}

static int awslc_prov_rsa_sig_set_saltlen_param(const AWSLC_PROV_CTX *provctx,
                                                OSSL_PARAM *p, int saltlen) {
  // Room for any int in decimal.
  char text[16];
  int value = saltlen;
  const char *name = NULL;
  int ok = 0;

  for (size_t i = 0; i < AWSLC_PROV_COUNT(awslc_prov_rsa_sig_saltlens); i++) {
    if (awslc_prov_rsa_sig_saltlens[i].saltlen == saltlen) {
      value = awslc_prov_rsa_sig_saltlens[i].openssl;
      name = awslc_prov_rsa_sig_saltlens[i].name;
    }
  }
  if (p->data_type == OSSL_PARAM_INTEGER) {
    ok = OSSL_PARAM_set_int(p, value);
  } else {
    if (name == NULL) {
      snprintf(text, sizeof(text), "%d", saltlen);
      name = text;
    }
    ok = OSSL_PARAM_set_utf8_string(p, name);
  }
  if (!ok) {
    AWSLC_PROV_ERROR_RAISE(provctx, AWSLC_PROV_R_INVALID_PARAMETER, p->key);
  }
  return ok;
}

static int awslc_prov_rsa_sig_get_ctx_params(void *vctx, OSSL_PARAM params[]) {
  AWSLC_PROV_RSA_SIG_CTX *ctx = (AWSLC_PROV_RSA_SIG_CTX *)vctx;
  OSSL_PARAM *p = NULL;
  AWSLC_PROV_CALL call;
  int ok = 1;

  if (ctx == NULL) {
    return 0;
  }
  if (!awslc_prov_param_set_int(ctx->provctx, params,
                                OSSL_SIGNATURE_PARAM_FIPS_APPROVED_INDICATOR,
                                ctx->fips_approved)) {
    return 0;
  }
  if (ctx->backend == NULL) {
    return 1;
  }

  awslc_prov_call_begin(&call, ctx->provctx);
  p = OSSL_PARAM_locate(params, OSSL_SIGNATURE_PARAM_ALGORITHM_ID);
  if (p != NULL) {
    unsigned char aid[AWSLC_PROV_RSA_SIG_ALGORITHM_ID_SIZE];
    size_t aid_len = 0;

    if (!awslc_prov_rsa_sig_algorithm_id(ctx->backend, aid, sizeof(aid),
                                         &aid_len)) {
      return AWSLC_PROV_CALL_END(&call, 0, p->key);
    }
    ok = OSSL_PARAM_set_octet_string(p, aid, aid_len);
  }
  if (ok &&
      (p = OSSL_PARAM_locate(params, OSSL_SIGNATURE_PARAM_PAD_MODE)) != NULL) {
    ok = awslc_prov_rsa_sig_set_padding_param(
        ctx->provctx, p, awslc_prov_rsa_sig_padding(ctx->backend));
  }
  if (ok) {
    const char *digest = awslc_prov_rsa_sig_digest(ctx->backend);

    ok = awslc_prov_param_set_utf8_string(ctx->provctx, params,
                                          OSSL_SIGNATURE_PARAM_DIGEST,
                                          digest == NULL ? "" : digest);
  }
  if (ok) {
    const char *mgf1_digest = awslc_prov_rsa_sig_mgf1_digest(ctx->backend);

    ok = awslc_prov_param_set_utf8_string(
        ctx->provctx, params, OSSL_SIGNATURE_PARAM_MGF1_DIGEST,
        mgf1_digest == NULL ? "" : mgf1_digest);
  }
  if (ok && (p = OSSL_PARAM_locate(params, OSSL_SIGNATURE_PARAM_PSS_SALTLEN)) !=
                NULL) {
    ok = awslc_prov_rsa_sig_set_saltlen_param(
        ctx->provctx, p, awslc_prov_rsa_sig_pss_saltlen(ctx->backend));
  }
  // A failed set raised its own error; AWS-LC's queue is only cleared.
  (void)AWSLC_PROV_CALL_END(&call, 1, NULL);
  return ok;
}

static const OSSL_PARAM *awslc_prov_rsa_sig_gettable_ctx_params(void *vctx,
                                                                void *provctx) {
  (void)vctx;
  (void)provctx;
  return awslc_prov_rsa_sig_gettable;
}

// Starts |operation| over |provkey|, or over the key of the previous init when
// |provkey| is NULL.
static int awslc_prov_rsa_sig_init(AWSLC_PROV_RSA_SIG_CTX *ctx, void *provkey,
                                   AWSLC_PROV_RSA_SIG_OPERATION operation,
                                   const char *digest,
                                   const OSSL_PARAM params[]) {
  const AWSLC_PROV_RSA_KEY *key = (const AWSLC_PROV_RSA_KEY *)provkey;
  AWSLC_PROV_CALL call;
  int ok = 0;

  if (ctx == NULL) {
    return 0;
  }
  if ((key == NULL && ctx->rsa == NULL) || (key != NULL && key->rsa == NULL)) {
    AWSLC_PROV_ERROR_RAISE(ctx->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           AWSLC_PROV_RSA_SIG_NAME);
    return 0;
  }
  if (digest == NULL && (operation == AWSLC_PROV_RSA_SIG_DIGEST_SIGN ||
                         operation == AWSLC_PROV_RSA_SIG_DIGEST_VERIFY)) {
    const OSSL_PARAM *p =
        OSSL_PARAM_locate_const(params, OSSL_SIGNATURE_PARAM_DIGEST);

    if (p != NULL && !OSSL_PARAM_get_utf8_string_ptr(p, &digest)) {
      digest = NULL;
    }
  }
  if (digest != NULL && awslc_prov_digest_canonical_name(digest) == NULL) {
    AWSLC_PROV_ERROR_RAISE(ctx->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           OSSL_SIGNATURE_PARAM_DIGEST);
    return 0;
  }

  awslc_prov_call_begin(&call, ctx->provctx);
  awslc_prov_rsa_sig_free(ctx->backend);
  ctx->backend = NULL;
  if (key != NULL) {
    if (!awslc_prov_rsa_up_ref(key->rsa)) {
      return AWSLC_PROV_CALL_END(&call, 0, AWSLC_PROV_RSA_SIG_NAME);
    }
    awslc_prov_rsa_free(ctx->rsa);
    ctx->rsa = key->rsa;
    ctx->pss = key->pss;
    ctx->restricted = key->restricted;
  }
  ctx->operation = operation;
  ctx->backend = awslc_prov_rsa_sig_new(ctx->rsa, ctx->pss, ctx->restricted,
                                        operation, digest);
  ok = ctx->backend != NULL;
  if (!AWSLC_PROV_CALL_END(&call, ok, AWSLC_PROV_RSA_SIG_NAME)) {
    return 0;
  }
  ctx->fips_approved = awslc_prov_ctx_is_fips(ctx->provctx);
  return awslc_prov_rsa_sig_set_ctx_params(ctx, params);
}

static int awslc_prov_rsa_sig_sign_init(void *vctx, void *provkey,
                                        const OSSL_PARAM params[]) {
  return awslc_prov_rsa_sig_init((AWSLC_PROV_RSA_SIG_CTX *)vctx, provkey,
                                 AWSLC_PROV_RSA_SIG_SIGN, NULL, params);
}

static int awslc_prov_rsa_sig_verify_init(void *vctx, void *provkey,
                                          const OSSL_PARAM params[]) {
  return awslc_prov_rsa_sig_init((AWSLC_PROV_RSA_SIG_CTX *)vctx, provkey,
                                 AWSLC_PROV_RSA_SIG_VERIFY, NULL, params);
}

static int awslc_prov_rsa_sig_verify_recover_init(void *vctx, void *provkey,
                                                  const OSSL_PARAM params[]) {
  return awslc_prov_rsa_sig_init((AWSLC_PROV_RSA_SIG_CTX *)vctx, provkey,
                                 AWSLC_PROV_RSA_SIG_VERIFY_RECOVER, NULL,
                                 params);
}

static int awslc_prov_rsa_sig_digest_sign_init(void *vctx, const char *mdname,
                                               void *provkey,
                                               const OSSL_PARAM params[]) {
  return awslc_prov_rsa_sig_init((AWSLC_PROV_RSA_SIG_CTX *)vctx, provkey,
                                 AWSLC_PROV_RSA_SIG_DIGEST_SIGN, mdname,
                                 params);
}

static int awslc_prov_rsa_sig_digest_verify_init(void *vctx, const char *mdname,
                                                 void *provkey,
                                                 const OSSL_PARAM params[]) {
  return awslc_prov_rsa_sig_init((AWSLC_PROV_RSA_SIG_CTX *)vctx, provkey,
                                 AWSLC_PROV_RSA_SIG_DIGEST_VERIFY, mdname,
                                 params);
}

static int awslc_prov_rsa_sig_ready(const AWSLC_PROV_RSA_SIG_CTX *ctx) {
  if (ctx == NULL) {
    return 0;
  }
  if (ctx->backend == NULL) {
    AWSLC_PROV_ERROR_RAISE(ctx->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           AWSLC_PROV_RSA_SIG_NAME);
    return 0;
  }
  return 1;
}

// The caller may publish a produced signature only when this returns 1.
static int awslc_prov_rsa_sig_signed(AWSLC_PROV_RSA_SIG_CTX *ctx,
                                     AWSLC_PROV_CALL *call, int ok,
                                     unsigned char *sig, size_t sigsize,
                                     int approvable) {
  int published = 0;

  if (approvable) {
    published = AWSLC_PROV_CALL_END_CHECK_APPROVED(
        call, ok, AWSLC_PROV_RSA_SIG_NAME,
        AWSLC_PROV_SIGN_OPERATION_DESCRIPTION, &ctx->fips_approved);
  } else {
    published = AWSLC_PROV_CALL_END_UNAPPROVED(
        call, ok, AWSLC_PROV_RSA_SIG_NAME,
        AWSLC_PROV_SIGN_OPERATION_DESCRIPTION, &ctx->fips_approved);
  }
  if (!published) {
    awslc_prov_cleanse(sig, sigsize);
  }
  return published;
}

static int awslc_prov_rsa_sig_sign_op(void *vctx, unsigned char *sig,
                                      size_t *siglen, size_t sigsize,
                                      const unsigned char *tbs, size_t tbslen) {
  AWSLC_PROV_RSA_SIG_CTX *ctx = (AWSLC_PROV_RSA_SIG_CTX *)vctx;
  AWSLC_PROV_CALL call;

  if (!awslc_prov_rsa_sig_ready(ctx)) {
    return 0;
  }
  awslc_prov_call_begin(&call, ctx->provctx);
  int ok =
      awslc_prov_rsa_sig_sign(ctx->backend, sig, siglen, sigsize, tbs, tbslen);
  if (sig == NULL) {
    return AWSLC_PROV_CALL_END(&call, ok, AWSLC_PROV_RSA_SIG_NAME);
  }
  return awslc_prov_rsa_sig_signed(ctx, &call, ok, sig, sigsize, 0);
}

static int awslc_prov_rsa_sig_verify_op(void *vctx, const unsigned char *sig,
                                        size_t siglen, const unsigned char *tbs,
                                        size_t tbslen) {
  AWSLC_PROV_RSA_SIG_CTX *ctx = (AWSLC_PROV_RSA_SIG_CTX *)vctx;
  AWSLC_PROV_CALL call;

  if (!awslc_prov_rsa_sig_ready(ctx)) {
    return 0;
  }
  awslc_prov_call_begin(&call, ctx->provctx);
  int ok = awslc_prov_rsa_sig_verify(ctx->backend, sig, siglen, tbs, tbslen);
  return AWSLC_PROV_CALL_END_UNAPPROVED(&call, ok, AWSLC_PROV_RSA_SIG_NAME,
                                        AWSLC_PROV_VERIFY_OPERATION_DESCRIPTION,
                                        &ctx->fips_approved);
}

static int awslc_prov_rsa_sig_verify_recover_op(void *vctx, unsigned char *rout,
                                                size_t *routlen,
                                                size_t routsize,
                                                const unsigned char *sig,
                                                size_t siglen) {
  AWSLC_PROV_RSA_SIG_CTX *ctx = (AWSLC_PROV_RSA_SIG_CTX *)vctx;
  AWSLC_PROV_CALL call;

  if (!awslc_prov_rsa_sig_ready(ctx)) {
    return 0;
  }
  awslc_prov_call_begin(&call, ctx->provctx);
  int ok = awslc_prov_rsa_sig_verify_recover(ctx->backend, rout, routlen,
                                             routsize, sig, siglen);
  if (rout == NULL) {
    return AWSLC_PROV_CALL_END(&call, ok, AWSLC_PROV_RSA_SIG_NAME);
  }
  if (!AWSLC_PROV_CALL_END_UNAPPROVED(
          &call, ok, AWSLC_PROV_RSA_SIG_NAME,
          AWSLC_PROV_VERIFY_RECOVER_OPERATION_DESCRIPTION,
          &ctx->fips_approved)) {
    awslc_prov_cleanse(rout, routsize);
    return 0;
  }
  return 1;
}

static int awslc_prov_rsa_sig_digest_update(void *vctx,
                                            const unsigned char *data,
                                            size_t datalen) {
  AWSLC_PROV_RSA_SIG_CTX *ctx = (AWSLC_PROV_RSA_SIG_CTX *)vctx;
  AWSLC_PROV_CALL call;

  if (!awslc_prov_rsa_sig_ready(ctx)) {
    return 0;
  }
  if (datalen == 0) {
    return 1;
  }
  awslc_prov_call_begin(&call, ctx->provctx);
  int ok = awslc_prov_rsa_sig_update(ctx->backend, data, datalen);
  return AWSLC_PROV_CALL_END(&call, ok, AWSLC_PROV_RSA_SIG_NAME);
}

static int awslc_prov_rsa_sig_digest_sign_final(void *vctx, unsigned char *sig,
                                                size_t *siglen,
                                                size_t sigsize) {
  AWSLC_PROV_RSA_SIG_CTX *ctx = (AWSLC_PROV_RSA_SIG_CTX *)vctx;
  AWSLC_PROV_CALL call;

  if (!awslc_prov_rsa_sig_ready(ctx)) {
    return 0;
  }
  awslc_prov_call_begin(&call, ctx->provctx);
  int ok = awslc_prov_rsa_sig_sign_final(ctx->backend, sig, siglen, sigsize);
  if (sig == NULL) {
    return AWSLC_PROV_CALL_END(&call, ok, AWSLC_PROV_RSA_SIG_NAME);
  }
  return awslc_prov_rsa_sig_signed(ctx, &call, ok, sig, sigsize, 1);
}

static int awslc_prov_rsa_sig_digest_verify_final(void *vctx,
                                                  const unsigned char *sig,
                                                  size_t siglen) {
  AWSLC_PROV_RSA_SIG_CTX *ctx = (AWSLC_PROV_RSA_SIG_CTX *)vctx;
  AWSLC_PROV_CALL call;

  if (!awslc_prov_rsa_sig_ready(ctx)) {
    return 0;
  }
  awslc_prov_call_begin(&call, ctx->provctx);
  int ok = awslc_prov_rsa_sig_verify_final(ctx->backend, sig, siglen);
  return AWSLC_PROV_CALL_END_CHECK_APPROVED(
      &call, ok, AWSLC_PROV_RSA_SIG_NAME,
      AWSLC_PROV_VERIFY_OPERATION_DESCRIPTION, &ctx->fips_approved);
}

const OSSL_DISPATCH awslc_prov_rsa_signature_functions[] = {
    {OSSL_FUNC_SIGNATURE_NEWCTX, (void (*)(void))awslc_prov_rsa_sig_newctx},
    {OSSL_FUNC_SIGNATURE_SIGN_INIT,
     (void (*)(void))awslc_prov_rsa_sig_sign_init},
    {OSSL_FUNC_SIGNATURE_SIGN, (void (*)(void))awslc_prov_rsa_sig_sign_op},
    {OSSL_FUNC_SIGNATURE_VERIFY_INIT,
     (void (*)(void))awslc_prov_rsa_sig_verify_init},
    {OSSL_FUNC_SIGNATURE_VERIFY, (void (*)(void))awslc_prov_rsa_sig_verify_op},
    {OSSL_FUNC_SIGNATURE_VERIFY_RECOVER_INIT,
     (void (*)(void))awslc_prov_rsa_sig_verify_recover_init},
    {OSSL_FUNC_SIGNATURE_VERIFY_RECOVER,
     (void (*)(void))awslc_prov_rsa_sig_verify_recover_op},
    {OSSL_FUNC_SIGNATURE_DIGEST_SIGN_INIT,
     (void (*)(void))awslc_prov_rsa_sig_digest_sign_init},
    {OSSL_FUNC_SIGNATURE_DIGEST_SIGN_UPDATE,
     (void (*)(void))awslc_prov_rsa_sig_digest_update},
    {OSSL_FUNC_SIGNATURE_DIGEST_SIGN_FINAL,
     (void (*)(void))awslc_prov_rsa_sig_digest_sign_final},
    {OSSL_FUNC_SIGNATURE_DIGEST_VERIFY_INIT,
     (void (*)(void))awslc_prov_rsa_sig_digest_verify_init},
    {OSSL_FUNC_SIGNATURE_DIGEST_VERIFY_UPDATE,
     (void (*)(void))awslc_prov_rsa_sig_digest_update},
    {OSSL_FUNC_SIGNATURE_DIGEST_VERIFY_FINAL,
     (void (*)(void))awslc_prov_rsa_sig_digest_verify_final},
    {OSSL_FUNC_SIGNATURE_FREECTX, (void (*)(void))awslc_prov_rsa_sig_freectx},
    {OSSL_FUNC_SIGNATURE_DUPCTX, (void (*)(void))awslc_prov_rsa_sig_dupctx},
    {OSSL_FUNC_SIGNATURE_GET_CTX_PARAMS,
     (void (*)(void))awslc_prov_rsa_sig_get_ctx_params},
    {OSSL_FUNC_SIGNATURE_GETTABLE_CTX_PARAMS,
     (void (*)(void))awslc_prov_rsa_sig_gettable_ctx_params},
    {OSSL_FUNC_SIGNATURE_SET_CTX_PARAMS,
     (void (*)(void))awslc_prov_rsa_sig_set_ctx_params},
    {OSSL_FUNC_SIGNATURE_SETTABLE_CTX_PARAMS,
     (void (*)(void))awslc_prov_rsa_sig_settable_ctx_params},
    OSSL_DISPATCH_END};
