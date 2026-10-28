// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_BACKEND_OPERATIONS_RSA_H
#define AWSLC_PROVIDER_BACKEND_OPERATIONS_RSA_H

// Back-side RSA helpers shared across operation classes. These name AWS-LC
// types, so this header is never part of the boundary.

#include <openssl/base.h>

#include <stdint.h>

#if defined(__cplusplus)
extern "C" {
#endif

// Append RFC 4055 RSASSA-PSS-params to |cbb|, omitting each field that holds
// its DER default.
int awslc_prov_rsa_marshal_pss_params(CBB *cbb, const EVP_MD *md,
                                      const EVP_MD *mgf1_md, int64_t saltlen);

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_BACKEND_OPERATIONS_RSA_H
