// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/params.h>

#include "boundary.h"
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
