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
  // An AWS-LC RSA
  void *rsa_key;
  // Copied from the key at init.
  int pss;
  int restricted;
  // An AWSLC_PROV_RSA_SIG
  void *rsa_ctx;
  // Set at init and replaced by AWS-LC's verdict at final. libcrypto runs
  // EVP_DigestSignFinal and EVP_DigestVerifyFinal on a duplicate it then frees
  // unless EVP_MD_CTX_FLAG_FINALISE is set, so without the flag the caller
  // reads the init value.
  int fips_approved;
} AWSLC_PROV_RSA_SIG_CTX;

static const struct {
  int openssl_padding;
  const char *padding_name;
  AWSLC_PROV_RSA_PADDING awslc_padding;
} awslc_prov_rsa_sig_paddings[] = {
    {RSA_PKCS1_PADDING, OSSL_PKEY_RSA_PAD_MODE_PKCSV15,
     AWSLC_PROV_RSA_PADDING_PKCS1},
    {RSA_NO_PADDING, OSSL_PKEY_RSA_PAD_MODE_NONE, AWSLC_PROV_RSA_PADDING_NONE},
    {RSA_PKCS1_PSS_PADDING, OSSL_PKEY_RSA_PAD_MODE_PSS,
     AWSLC_PROV_RSA_PADDING_PSS},
};

static const struct {
  int openssl_saltlen;
  const char *saltlen_name;
  int awslc_saltlen;
} awslc_prov_rsa_sig_saltlen_sentinels[] = {
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

static const OSSL_PARAM awslc_prov_rsa_sig_settable[] = {
    OSSL_PARAM_utf8_string(OSSL_SIGNATURE_PARAM_DIGEST, NULL, 0),
    OSSL_PARAM_utf8_string(OSSL_SIGNATURE_PARAM_PAD_MODE, NULL, 0),
    OSSL_PARAM_utf8_string(OSSL_SIGNATURE_PARAM_MGF1_DIGEST, NULL, 0),
    OSSL_PARAM_utf8_string(OSSL_SIGNATURE_PARAM_PSS_SALTLEN, NULL, 0),
    OSSL_PARAM_END};

// With the digest fixed, it is not settable.
static const OSSL_PARAM awslc_prov_rsa_sig_settable_fixed_digest[] = {
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

// Whether the digest is fixed: a digest operation names it at init.
static int awslc_prov_rsa_sig_digest_fixed(const AWSLC_PROV_RSA_SIG_CTX *ctx) {
  return ctx->rsa_ctx != NULL &&
         awslc_prov_rsa_sig_operation_is_digest(
             awslc_prov_rsa_sig_operation(ctx->rsa_ctx));
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
  awslc_prov_rsa_sig_free(ctx->rsa_ctx);
  awslc_prov_rsa_free(ctx->rsa_key);
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
    copy->rsa_key = NULL;
    copy->rsa_ctx = NULL;
    if (ctx->rsa_key == NULL || awslc_prov_rsa_up_ref(ctx->rsa_key)) {
      copy->rsa_key = ctx->rsa_key;
      copy->rsa_ctx = awslc_prov_rsa_sig_dup(ctx->rsa_ctx);
      ok = ctx->rsa_ctx == NULL || copy->rsa_ctx != NULL;
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
      if (awslc_prov_rsa_sig_paddings[i].openssl_padding == mode) {
        *out = awslc_prov_rsa_sig_paddings[i].awslc_padding;
        return 1;
      }
    }
  } else if (OSSL_PARAM_get_utf8_string_ptr(p, &name)) {
    for (size_t i = 0; i < AWSLC_PROV_COUNT(awslc_prov_rsa_sig_paddings); i++) {
      if (strcmp(awslc_prov_rsa_sig_paddings[i].padding_name, name) == 0) {
        *out = awslc_prov_rsa_sig_paddings[i].awslc_padding;
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

    for (size_t i = 0;
         i < AWSLC_PROV_COUNT(awslc_prov_rsa_sig_saltlen_sentinels); i++) {
      const char *saltlen_name =
          awslc_prov_rsa_sig_saltlen_sentinels[i].saltlen_name;

      if (strcmp(saltlen_name, text) == 0) {
        *out = awslc_prov_rsa_sig_saltlen_sentinels[i].awslc_saltlen;
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
  for (size_t i = 0; i < AWSLC_PROV_COUNT(awslc_prov_rsa_sig_saltlen_sentinels);
       i++) {
    if (awslc_prov_rsa_sig_saltlen_sentinels[i].openssl_saltlen == value) {
      *out = awslc_prov_rsa_sig_saltlen_sentinels[i].awslc_saltlen;
      return 1;
    }
  }
  if (value < 0) {
    return 0;
  }
  *out = value;
  return 1;
}

typedef struct {
  const OSSL_PARAM *pad_param;
  AWSLC_PROV_RSA_PADDING padding;
  const char *digest;
  const char *mgf1_digest;
  const OSSL_PARAM *saltlen_param;
  int saltlen;
} AWSLC_PROV_RSA_SIG_PARAMS;

// Reads |params| into |out| without touching AWS-LC. When |digest_fixed|, a
// digest parameter must name |fixed_digest|, the one the operation started
// with.
static int awslc_prov_rsa_sig_parse_params(const AWSLC_PROV_CTX *provctx,
                                           const OSSL_PARAM params[],
                                           int digest_fixed,
                                           const char *fixed_digest,
                                           AWSLC_PROV_RSA_SIG_PARAMS *out) {
  memset(out, 0, sizeof(*out));
  if (params == NULL) {
    return 1;
  }
  out->pad_param =
      OSSL_PARAM_locate_const(params, OSSL_SIGNATURE_PARAM_PAD_MODE);
  if (out->pad_param != NULL &&
      !awslc_prov_rsa_sig_get_padding(out->pad_param, &out->padding)) {
    AWSLC_PROV_ERROR_RAISE(provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           OSSL_SIGNATURE_PARAM_PAD_MODE);
    return 0;
  }
  out->saltlen_param =
      OSSL_PARAM_locate_const(params, OSSL_SIGNATURE_PARAM_PSS_SALTLEN);
  if (out->saltlen_param != NULL &&
      !awslc_prov_rsa_sig_get_saltlen(out->saltlen_param, &out->saltlen)) {
    AWSLC_PROV_ERROR_RAISE(provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           OSSL_SIGNATURE_PARAM_PSS_SALTLEN);
    return 0;
  }
  if (!awslc_prov_param_get_digest(
          provctx, OSSL_PARAM_locate_const(params, OSSL_SIGNATURE_PARAM_DIGEST),
          &out->digest) ||
      !awslc_prov_param_get_digest(
          provctx,
          OSSL_PARAM_locate_const(params, OSSL_SIGNATURE_PARAM_MGF1_DIGEST),
          &out->mgf1_digest)) {
    return 0;
  }
  if (out->digest != NULL && digest_fixed) {
    if (fixed_digest == NULL || strcmp(out->digest, fixed_digest) != 0) {
      AWSLC_PROV_ERROR_RAISE(provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                             OSSL_SIGNATURE_PARAM_DIGEST);
      return 0;
    }
    out->digest = NULL;
  }
  return 1;
}

// Applies |params| to |rsa_ctx| inside the caller's bracket. On failure
// |*step| names the parameter AWS-LC refused.
static int awslc_prov_rsa_sig_apply_params(
    void *rsa_ctx, const AWSLC_PROV_RSA_SIG_PARAMS *params, const char **step) {
  if (params->pad_param != NULL) {
    *step = OSSL_SIGNATURE_PARAM_PAD_MODE;
    if (!awslc_prov_rsa_sig_set_padding(rsa_ctx, params->padding)) {
      return 0;
    }
  }
  if (params->digest != NULL) {
    *step = OSSL_SIGNATURE_PARAM_DIGEST;
    if (!awslc_prov_rsa_sig_set_digest(rsa_ctx, params->digest)) {
      return 0;
    }
  }
  if (params->mgf1_digest != NULL) {
    *step = OSSL_SIGNATURE_PARAM_MGF1_DIGEST;
    if (!awslc_prov_rsa_sig_set_mgf1_digest(rsa_ctx, params->mgf1_digest)) {
      return 0;
    }
  }
  if (params->saltlen_param != NULL) {
    *step = OSSL_SIGNATURE_PARAM_PSS_SALTLEN;
    if (!awslc_prov_rsa_sig_set_pss_saltlen(rsa_ctx, params->saltlen)) {
      return 0;
    }
  }
  return 1;
}

static int awslc_prov_rsa_sig_set_ctx_params(void *vctx,
                                             const OSSL_PARAM params[]) {
  AWSLC_PROV_RSA_SIG_CTX *ctx = (AWSLC_PROV_RSA_SIG_CTX *)vctx;
  AWSLC_PROV_RSA_SIG_PARAMS parsed;
  void *staged = NULL;
  const char *step = AWSLC_PROV_RSA_SIG_NAME;
  AWSLC_PROV_CALL call;
  int ok = 0;

  if (ctx == NULL) {
    return 0;
  }
  if (params == NULL || params[0].key == NULL) {
    return 1;
  }
  if (ctx->rsa_ctx == NULL) {
    AWSLC_PROV_ERROR_RAISE(ctx->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           AWSLC_PROV_RSA_SIG_NAME);
    return 0;
  }
  if (!awslc_prov_rsa_sig_parse_params(
          ctx->provctx, params, awslc_prov_rsa_sig_digest_fixed(ctx),
          awslc_prov_rsa_sig_digest(ctx->rsa_ctx), &parsed)) {
    return 0;
  }

  awslc_prov_call_begin(&call, ctx->provctx);
  staged = awslc_prov_rsa_sig_dup(ctx->rsa_ctx);
  ok =
      staged != NULL && awslc_prov_rsa_sig_apply_params(staged, &parsed, &step);
  if (!AWSLC_PROV_CALL_END(&call, ok, step)) {
    awslc_prov_rsa_sig_free(staged);
    return 0;
  }
  awslc_prov_rsa_sig_free(ctx->rsa_ctx);
  ctx->rsa_ctx = staged;
  return 1;
}

static const OSSL_PARAM *awslc_prov_rsa_sig_settable_ctx_params(void *vctx,
                                                                void *provctx) {
  const AWSLC_PROV_RSA_SIG_CTX *ctx = (const AWSLC_PROV_RSA_SIG_CTX *)vctx;

  (void)provctx;
  if (ctx != NULL && awslc_prov_rsa_sig_digest_fixed(ctx)) {
    return awslc_prov_rsa_sig_settable_fixed_digest;
  }
  return awslc_prov_rsa_sig_settable;
}

static int awslc_prov_rsa_sig_set_padding_param(const AWSLC_PROV_CTX *provctx,
                                                OSSL_PARAM *p, int padding) {
  for (size_t i = 0; i < AWSLC_PROV_COUNT(awslc_prov_rsa_sig_paddings); i++) {
    if ((int)awslc_prov_rsa_sig_paddings[i].awslc_padding != padding) {
      continue;
    }
    if (p->data_type == OSSL_PARAM_INTEGER
            ? OSSL_PARAM_set_int(p,
                                 awslc_prov_rsa_sig_paddings[i].openssl_padding)
            : OSSL_PARAM_set_utf8_string(
                  p, awslc_prov_rsa_sig_paddings[i].padding_name)) {
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

  for (size_t i = 0; i < AWSLC_PROV_COUNT(awslc_prov_rsa_sig_saltlen_sentinels);
       i++) {
    if (awslc_prov_rsa_sig_saltlen_sentinels[i].awslc_saltlen == saltlen) {
      value = awslc_prov_rsa_sig_saltlen_sentinels[i].openssl_saltlen;
      name = awslc_prov_rsa_sig_saltlen_sentinels[i].saltlen_name;
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
  if (ctx->rsa_ctx == NULL) {
    return 1;
  }

  awslc_prov_call_begin(&call, ctx->provctx);
  // OSSL_SIGNATURE_PARAM_ALGORITHM_ID is the DER-encoded AlgorithmIdentifier of
  // the signature the current parameters produce.
  p = OSSL_PARAM_locate(params, OSSL_SIGNATURE_PARAM_ALGORITHM_ID);
  if (p != NULL) {
    unsigned char aid[AWSLC_PROV_RSA_SIG_ALGORITHM_ID_SIZE];
    size_t aid_len = 0;

    if (!awslc_prov_rsa_sig_algorithm_id(ctx->rsa_ctx, aid, sizeof(aid),
                                         &aid_len)) {
      return AWSLC_PROV_CALL_END(&call, 0, p->key);
    }
    ok = awslc_prov_param_set_octet_string(
        ctx->provctx, params, OSSL_SIGNATURE_PARAM_ALGORITHM_ID, aid, aid_len);
  }
  if (ok &&
      (p = OSSL_PARAM_locate(params, OSSL_SIGNATURE_PARAM_PAD_MODE)) != NULL) {
    ok = awslc_prov_rsa_sig_set_padding_param(
        ctx->provctx, p, awslc_prov_rsa_sig_padding(ctx->rsa_ctx));
  }
  if (ok) {
    const char *digest = awslc_prov_rsa_sig_digest(ctx->rsa_ctx);

    ok = awslc_prov_param_set_utf8_string(ctx->provctx, params,
                                          OSSL_SIGNATURE_PARAM_DIGEST,
                                          digest == NULL ? "" : digest);
  }
  if (ok) {
    const char *mgf1_digest =
        awslc_prov_rsa_sig_mgf1_digest(ctx->rsa_ctx);

    ok = awslc_prov_param_set_utf8_string(
        ctx->provctx, params, OSSL_SIGNATURE_PARAM_MGF1_DIGEST,
        mgf1_digest == NULL ? "" : mgf1_digest);
  }
  if (ok && (p = OSSL_PARAM_locate(params, OSSL_SIGNATURE_PARAM_PSS_SALTLEN)) !=
                NULL) {
    ok = awslc_prov_rsa_sig_set_saltlen_param(
        ctx->provctx, p, awslc_prov_rsa_sig_pss_saltlen(ctx->rsa_ctx));
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
// |provkey| is NULL. On failure the context keeps its previous operation.
static int awslc_prov_rsa_sig_init(AWSLC_PROV_RSA_SIG_CTX *ctx, void *provkey,
                                   AWSLC_PROV_RSA_SIG_OPERATION operation,
                                   const char *digest,
                                   const OSSL_PARAM params[]) {
  const AWSLC_PROV_RSA_KEY *key = (const AWSLC_PROV_RSA_KEY *)provkey;
  const int digest_op = awslc_prov_rsa_sig_operation_is_digest(operation);
  AWSLC_PROV_RSA_SIG_PARAMS parsed;
  void *rsa_key = NULL;
  void *staged = NULL;
  const char *step = AWSLC_PROV_RSA_SIG_NAME;
  AWSLC_PROV_CALL call;
  int ok = 0;

  if (ctx == NULL) {
    return 0;
  }
  if ((key == NULL && ctx->rsa_key == NULL) ||
      (key != NULL && key->rsa == NULL)) {
    AWSLC_PROV_ERROR_RAISE(ctx->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           AWSLC_PROV_RSA_SIG_NAME);
    return 0;
  }
  if (digest != NULL) {
    if ((digest = awslc_prov_digest_canonical_name(digest)) == NULL) {
      AWSLC_PROV_ERROR_RAISE(ctx->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                             OSSL_SIGNATURE_PARAM_DIGEST);
      return 0;
    }
  } else if (digest_op &&
             !awslc_prov_param_get_digest(
                 ctx->provctx,
                 OSSL_PARAM_locate_const(params, OSSL_SIGNATURE_PARAM_DIGEST),
                 &digest)) {
    return 0;
  }
  if (!awslc_prov_rsa_sig_parse_params(ctx->provctx, params, digest_op, digest,
                                       &parsed)) {
    return 0;
  }

  awslc_prov_call_begin(&call, ctx->provctx);
  rsa_key = key != NULL ? key->rsa : ctx->rsa_key;
  if (key != NULL && !awslc_prov_rsa_up_ref(rsa_key)) {
    return AWSLC_PROV_CALL_END(&call, 0, AWSLC_PROV_RSA_SIG_NAME);
  }
  staged = awslc_prov_rsa_sig_new(
      rsa_key, key != NULL ? key->pss : ctx->pss,
      key != NULL ? key->restricted : ctx->restricted, operation, digest);
  ok =
      staged != NULL && awslc_prov_rsa_sig_apply_params(staged, &parsed, &step);
  if (!AWSLC_PROV_CALL_END(&call, ok, step)) {
    awslc_prov_rsa_sig_free(staged);
    if (key != NULL) {
      awslc_prov_rsa_free(rsa_key);
    }
    return 0;
  }
  awslc_prov_rsa_sig_free(ctx->rsa_ctx);
  ctx->rsa_ctx = staged;
  if (key != NULL) {
    awslc_prov_rsa_free(ctx->rsa_key);
    ctx->rsa_key = rsa_key;
    ctx->pss = key->pss;
    ctx->restricted = key->restricted;
  }
  ctx->fips_approved = awslc_prov_ctx_is_fips(ctx->provctx);
  return 1;
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
  if (ctx->rsa_ctx == NULL) {
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
  int ok = awslc_prov_rsa_sig_sign(ctx->rsa_ctx, sig, siglen, sigsize,
                                   tbs, tbslen);
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
  int ok =
      awslc_prov_rsa_sig_verify(ctx->rsa_ctx, sig, siglen, tbs, tbslen);
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
  int ok = awslc_prov_rsa_sig_verify_recover(ctx->rsa_ctx, rout, routlen,
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
  int ok = awslc_prov_rsa_sig_update(ctx->rsa_ctx, data, datalen);
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
  int ok =
      awslc_prov_rsa_sig_sign_final(ctx->rsa_ctx, sig, siglen, sigsize);
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
  int ok = awslc_prov_rsa_sig_verify_final(ctx->rsa_ctx, sig, siglen);
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
