// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_FRONTEND_OPERATIONS_SHA2_H
#define AWSLC_PROVIDER_FRONTEND_OPERATIONS_SHA2_H

#include "frontend/operations/digests/digests.h"

#if defined(__cplusplus)
extern "C" {
#endif

// frontend/operations/digests/sha2.c
AWSLC_PROV_DECLARE_DIGEST_TABLE(sha224);
AWSLC_PROV_DECLARE_DIGEST_TABLE(sha256);
AWSLC_PROV_DECLARE_DIGEST_TABLE(sha384);
AWSLC_PROV_DECLARE_DIGEST_TABLE(sha512);
AWSLC_PROV_DECLARE_DIGEST_TABLE(sha512_224);
AWSLC_PROV_DECLARE_DIGEST_TABLE(sha512_256);

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_FRONTEND_OPERATIONS_SHA2_H
