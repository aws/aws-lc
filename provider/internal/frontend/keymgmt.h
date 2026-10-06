// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_INTERNAL_FRONTEND_KEYMGMT_H
#define AWSLC_PROVIDER_INTERNAL_FRONTEND_KEYMGMT_H

#include <stddef.h>

#include <openssl/core.h>
#include <openssl/core_dispatch.h>

#include "internal/backend/keymgmt.h"
#include "internal/provider.h"

#if defined(__cplusplus)
extern "C" {
#endif

// Read the integer param |key| from |params| into |out|. An absent key
// succeeds with |out->data| NULL.
int awslc_prov_keymgmt_get_bn(const AWSLC_PROV_CTX *provctx,
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
} AWSLC_PROV_KEYMGMT_BN;

// Encode |bns| into |params[0..count)| over one new buffer the caller wipes
// with awslc_prov_clear_free(*buffer, *size).
int awslc_prov_param_encode_bns(const AWSLC_PROV_CTX *ctx,
                                const AWSLC_PROV_KEYMGMT_BN *bns, size_t count,
                                OSSL_PARAM *params, unsigned char **buffer,
                                size_t *size);

// frontend/operations/keymgmt/rsa.c
extern const OSSL_DISPATCH awslc_prov_rsa_keymgmt_functions[];

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_INTERNAL_FRONTEND_KEYMGMT_H
