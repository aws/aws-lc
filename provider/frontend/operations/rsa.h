// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_FRONTEND_OPERATIONS_RSA_H
#define AWSLC_PROVIDER_FRONTEND_OPERATIONS_RSA_H

#include <openssl/core.h>

#if defined(__cplusplus)
extern "C" {
#endif

// frontend/operations/keymgmt/rsa.c
extern const OSSL_DISPATCH awslc_prov_rsa_keymgmt_functions[];
extern const OSSL_DISPATCH awslc_prov_rsa_pss_keymgmt_functions[];

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_FRONTEND_OPERATIONS_RSA_H
