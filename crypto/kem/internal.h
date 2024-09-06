// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_HEADER_KEM_LEGACY_INTERNAL_H
#define AWSLC_HEADER_KEM_LEGACY_INTERNAL_H

#include <openssl/base.h>

#include "../fipsmodule/kem/internal.h"

#if defined(__cplusplus)
extern "C" {
#endif

#define AWSLC_NUM_LEGACY_KEMS 3

extern const KEM_METHOD kem_kyber512r3_method;
extern const KEM_METHOD kem_kyber768r3_method;
extern const KEM_METHOD kem_kyber1024r3_method;

const KEM *get_legacy_kems(void);

#if defined(__cplusplus)
}  // extern C
#endif

#endif
