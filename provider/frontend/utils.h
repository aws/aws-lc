// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_FRONTEND_UTILS_H
#define AWSLC_PROVIDER_FRONTEND_UTILS_H

#include <stddef.h>

#include <openssl/core.h>

#include "boundary/utils.h"
#include "frontend/provider.h"

#if defined(__cplusplus)
extern "C" {
#endif

// Answer |key| in |params| with |value|. Succeeds when |key| is not requested;
// a failed set raises AWSLC_PROV_R_INVALID_PARAMETER naming |key|, except that
// a NULL |ctx| raises nothing.
int awslc_prov_param_set_int(const AWSLC_PROV_CTX *ctx, OSSL_PARAM params[],
                             const char *key, int value);
int awslc_prov_param_set_size_t(const AWSLC_PROV_CTX *ctx, OSSL_PARAM params[],
                                const char *key, size_t value);
int awslc_prov_param_set_utf8_string(const AWSLC_PROV_CTX *ctx,
                                     OSSL_PARAM params[], const char *key,
                                     const char *value);
int awslc_prov_param_set_utf8_ptr(const AWSLC_PROV_CTX *ctx,
                                  OSSL_PARAM params[], const char *key,
                                  const char *value);

// Read the integer param |key| from |params| into |out|. An absent key
// succeeds with |out->data| NULL.
int awslc_prov_param_get_bn(const AWSLC_PROV_CTX *provctx,
                            const OSSL_PARAM params[], const char *key,
                            AWSLC_PROV_BN_BYTES *out);

// Answer a request for |key| in |params| with |bn| under OSSL_PARAM_set_BN's
// contract, including a NULL |data| size probe. Succeeds when |key| is not
// requested; fails when it is and |bn| is NULL.
int awslc_prov_param_set_bn(const AWSLC_PROV_CTX *provctx,
                            OSSL_PARAM params[], const char *key,
                            const void *bn);

typedef struct {
  const char *key;
  const void *bn;
} AWSLC_PROV_PARAM_BN;

// Encode |bns| into |params[0..count)| over one new buffer the caller wipes
// with awslc_prov_clear_free(*buffer, *size).
int awslc_prov_param_encode_bns(const AWSLC_PROV_CTX *ctx,
                                const AWSLC_PROV_PARAM_BN *bns, size_t count,
                                OSSL_PARAM *params, unsigned char **buffer,
                                size_t *size);

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_FRONTEND_UTILS_H
