// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_FRONTEND_OPERATIONS_RSA_H
#define AWSLC_PROVIDER_FRONTEND_OPERATIONS_RSA_H

#include <openssl/core.h>

#include "boundary/operations/rsa.h"
#include "frontend/provider.h"

#if defined(__cplusplus)
extern "C" {
#endif

// The keydata of both RSA key managers. A signature reads it at init and takes
// its own reference to |rsa|, which is never mutated once set.
typedef struct {
  AWSLC_PROV_CTX *provctx;
  // NULL until an import or generation fills it.
  void *rsa;
  // An RSA-PSS key, which signs with PSS padding only.
  int pss;
  // Whether AWS-LC enforces |restrictions| on |rsa|.
  int restricted;
  AWSLC_PROV_RSA_PSS_PARAMS restrictions;
} AWSLC_PROV_RSA_KEY;

// frontend/operations/keymgmt/rsa.c
extern const OSSL_DISPATCH awslc_prov_rsa_keymgmt_functions[];
extern const OSSL_DISPATCH awslc_prov_rsa_pss_keymgmt_functions[];

// frontend/operations/signature/rsa.c
extern const OSSL_DISPATCH awslc_prov_rsa_signature_functions[];

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_FRONTEND_OPERATIONS_RSA_H
