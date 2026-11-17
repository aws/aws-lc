// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_FRONTEND_UTILS_H
#define AWSLC_PROVIDER_FRONTEND_UTILS_H

#include <stddef.h>

#include <openssl/core.h>

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

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_FRONTEND_UTILS_H
