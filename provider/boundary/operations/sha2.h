// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_BOUNDARY_OPERATIONS_SHA2_H
#define AWSLC_PROVIDER_BOUNDARY_OPERATIONS_SHA2_H

#include "boundary/digests.h"

#if defined(__cplusplus)
extern "C" {
#endif

// SHA-2, from backend/operations/digests/sha2.c.
AWSLC_PROV_DECLARE_DIGEST_BACKEND(sha224);
AWSLC_PROV_DECLARE_DIGEST_BACKEND(sha256);
AWSLC_PROV_DECLARE_DIGEST_BACKEND(sha384);
AWSLC_PROV_DECLARE_DIGEST_BACKEND(sha512);
AWSLC_PROV_DECLARE_DIGEST_BACKEND(sha512_224);
AWSLC_PROV_DECLARE_DIGEST_BACKEND(sha512_256);

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_BOUNDARY_OPERATIONS_SHA2_H
