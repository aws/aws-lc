// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// Key-management-class OSSL_PARAM plumbing for big numbers.

#include <openssl/params.h>

#include "internal/backend.h"
#include "internal/backend/keymgmt.h"
#include "internal/frontend/keymgmt.h"
#include "internal/provider.h"

static int awslc_prov_keymgmt_is_integer(const OSSL_PARAM *p) {
  return p->data_type == OSSL_PARAM_UNSIGNED_INTEGER ||
         p->data_type == OSSL_PARAM_INTEGER;
}

int awslc_prov_keymgmt_get_bn(const AWSLC_PROV_CTX *provctx,
                              const OSSL_PARAM params[], const char *key,
                              AWSLC_PROV_BN_BYTES *out) {
  const OSSL_PARAM *p = OSSL_PARAM_locate_const(params, key);

  out->data = NULL;
  out->len = 0;
  out->is_signed = 0;
  if (p == NULL) {
    return 1;
  }
  if (!awslc_prov_keymgmt_is_integer(p) || p->data == NULL) {
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

  if (p == NULL) {
    return 1;
  }
  p->return_size = 0;
  if (!awslc_prov_keymgmt_is_integer(p) || bn == NULL) {
    AWSLC_PROV_ERROR_RAISE(provctx, AWSLC_PROV_R_INVALID_PARAMETER, key);
    return 0;
  }
  awslc_prov_error_mark();
  int ok =
      awslc_prov_bn_to_bytes(bn, p->data_type == OSSL_PARAM_INTEGER,
                             (unsigned char *)p->data, p->data_size, &written);
  // Set on failure too: a short buffer reports the size the caller retries
  // with.
  p->return_size = written;
  return AWSLC_PROV_ERROR_SETTLE(provctx, ok, AWSLC_PROV_R_INVALID_PARAMETER,
                                 key);
}

int awslc_prov_param_encode_bns(const AWSLC_PROV_CTX *ctx,
                                const AWSLC_PROV_KEYMGMT_BN *bns, size_t count,
                                OSSL_PARAM *params, unsigned char **buffer,
                                size_t *size) {
  unsigned char *out = NULL;
  size_t total = 0;
  size_t offset = 0;
  int ok = 1;

  *buffer = NULL;
  *size = 0;
  if (count == 0) {
    return 1;
  }

  awslc_prov_error_mark();
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
  if (!AWSLC_PROV_ERROR_SETTLE(ctx, ok, AWSLC_PROV_R_BACKEND_ERROR, NULL)) {
    awslc_prov_clear_free(out, total);
    return 0;
  }
  *buffer = out;
  *size = total;
  return 1;
}
