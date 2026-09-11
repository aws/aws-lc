// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_INTERNAL_FRONTEND_DIGESTS_H
#define AWSLC_PROVIDER_INTERNAL_FRONTEND_DIGESTS_H

// The digest dispatch tables, one per algorithm, that registry.c hands the core.

#include <openssl/core_dispatch.h>

#if defined(__cplusplus)
extern "C" {
#endif

// frontend/operations/digests/sha2.c
extern const OSSL_DISPATCH awslc_prov_sha256_functions[];

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_INTERNAL_FRONTEND_DIGESTS_H
