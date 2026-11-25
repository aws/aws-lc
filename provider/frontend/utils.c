// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/params.h>

#include "boundary.h"
#include "boundary/utils.h"
#include "frontend/provider.h"
#include "frontend/utils.h"

static int awslc_prov_param_settled(const AWSLC_PROV_CTX *ctx, int ok,
                                    const char *key) {
  if (!ok) {
    AWSLC_PROV_ERROR_RAISE(ctx, AWSLC_PROV_R_INVALID_PARAMETER, key);
  }
  return ok;
}

int awslc_prov_param_set_int(const AWSLC_PROV_CTX *ctx, OSSL_PARAM params[],
                             const char *key, int value) {
  OSSL_PARAM *p = OSSL_PARAM_locate(params, key);

  return p == NULL ||
         awslc_prov_param_settled(ctx, OSSL_PARAM_set_int(p, value), key);
}

int awslc_prov_param_set_size_t(const AWSLC_PROV_CTX *ctx, OSSL_PARAM params[],
                                const char *key, size_t value) {
  OSSL_PARAM *p = OSSL_PARAM_locate(params, key);

  return p == NULL ||
         awslc_prov_param_settled(ctx, OSSL_PARAM_set_size_t(p, value), key);
}

int awslc_prov_param_set_utf8_string(const AWSLC_PROV_CTX *ctx,
                                     OSSL_PARAM params[], const char *key,
                                     const char *value) {
  OSSL_PARAM *p = OSSL_PARAM_locate(params, key);

  return p == NULL || awslc_prov_param_settled(
                          ctx, OSSL_PARAM_set_utf8_string(p, value), key);
}

int awslc_prov_param_set_utf8_ptr(const AWSLC_PROV_CTX *ctx,
                                  OSSL_PARAM params[], const char *key,
                                  const char *value) {
  OSSL_PARAM *p = OSSL_PARAM_locate(params, key);

  return p == NULL ||
         awslc_prov_param_settled(ctx, OSSL_PARAM_set_utf8_ptr(p, value), key);
}

int awslc_prov_param_get_digest(const AWSLC_PROV_CTX *ctx, const OSSL_PARAM *p,
                                const char **out) {
  const char *name = NULL;
  const char *canonical = NULL;

  if (p == NULL) {
    return 1;
  }
  if (!OSSL_PARAM_get_utf8_string_ptr(p, &name) ||
      (canonical = awslc_prov_digest_canonical_name(name)) == NULL) {
    AWSLC_PROV_ERROR_RAISE(ctx, AWSLC_PROV_R_INVALID_PARAMETER, p->key);
    return 0;
  }
  *out = canonical;
  return 1;
}

static int awslc_prov_param_is_integer(const OSSL_PARAM *p) {
  return p->data_type == OSSL_PARAM_UNSIGNED_INTEGER ||
         p->data_type == OSSL_PARAM_INTEGER;
}

int awslc_prov_param_get_bn(const AWSLC_PROV_CTX *provctx,
                            const OSSL_PARAM params[], const char *key,
                            AWSLC_PROV_BN_BYTES *out) {
  const OSSL_PARAM *p = OSSL_PARAM_locate_const(params, key);

  out->data = NULL;
  out->len = 0;
  out->is_signed = 0;
  if (p == NULL) {
    return 1;
  }
  if (!awslc_prov_param_is_integer(p) || p->data == NULL) {
    AWSLC_PROV_ERROR_RAISE(provctx, AWSLC_PROV_R_INVALID_PARAMETER, key);
    return 0;
  }
  out->data = (const unsigned char *)p->data;
  out->len = p->data_size;
  out->is_signed = p->data_type == OSSL_PARAM_INTEGER;
  return 1;
}

int awslc_prov_param_set_bn(const AWSLC_PROV_CTX *provctx,
                            OSSL_PARAM params[], const char *key,
                            const void *bn) {
  OSSL_PARAM *p = OSSL_PARAM_locate(params, key);
  size_t written = 0;
  AWSLC_PROV_CALL call;

  if (p == NULL) {
    return 1;
  }
  p->return_size = 0;
  if (!awslc_prov_param_is_integer(p) || bn == NULL) {
    AWSLC_PROV_ERROR_RAISE(provctx, AWSLC_PROV_R_INVALID_PARAMETER, key);
    return 0;
  }
  int is_signed = p->data_type == OSSL_PARAM_INTEGER;

  awslc_prov_call_begin(&call, provctx);
  if (!awslc_prov_bn_to_bytes(bn, is_signed, NULL, 0, &written)) {
    return AWSLC_PROV_CALL_END(&call, 0, key);
  }
  // A short buffer reports the size the caller retries with.
  p->return_size = written;
  if (p->data != NULL && p->data_size < written) {
    (void)AWSLC_PROV_CALL_END(&call, 1, key);
    AWSLC_PROV_ERROR_RAISE(provctx, AWSLC_PROV_R_INVALID_PARAMETER, key);
    return 0;
  }
  int ok = awslc_prov_bn_to_bytes(bn, is_signed, (unsigned char *)p->data,
                                  p->data_size, &written);
  p->return_size = written;
  return AWSLC_PROV_CALL_END(&call, ok, key);
}

int awslc_prov_param_encode_bns(const AWSLC_PROV_CTX *ctx,
                                const AWSLC_PROV_PARAM_BN *bns, size_t count,
                                OSSL_PARAM *params, unsigned char **buffer,
                                size_t *size) {
  unsigned char *out = NULL;
  size_t total = 0;
  size_t offset = 0;
  int ok = 1;
  AWSLC_PROV_CALL call;

  *buffer = NULL;
  *size = 0;
  if (count == 0) {
    return 1;
  }

  awslc_prov_call_begin(&call, ctx);
  for (size_t i = 0; ok && i < count; i++) {
    size_t len = 0;

    ok = awslc_prov_bn_to_bytes(bns[i].bn, 0, NULL, 0, &len);
    params[i] = OSSL_PARAM_construct_BN(bns[i].key, NULL, len);
    total += len;
  }
  if (ok) {
    out = awslc_prov_zalloc(total);
    ok = out != NULL;
  }
  for (size_t i = 0; ok && i < count; i++) {
    size_t written = 0;

    params[i].data = out + offset;
    ok = awslc_prov_bn_to_bytes(bns[i].bn, 0, out + offset,
                                params[i].data_size, &written);
    offset += params[i].data_size;
  }
  if (!AWSLC_PROV_CALL_END(&call, ok, NULL)) {
    awslc_prov_clear_free(out, total);
    return 0;
  }
  *buffer = out;
  *size = total;
  return 1;
}
