/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef MLK_CONFIG_H
#define MLK_CONFIG_H

#include "../../internal.h"

/* Namespacing: All symbols are of the form mlkem*. Level-specific
 * symbols are further prefixed with their security level, e.g.
 * mlkem512*, mlkem768*, mlkem1024*. */
#define MLK_NAMESPACE_PREFIX mlkem
#define MLK_NAMESPACE_PREFIX_ADD_LEVEL
#define MLK_MONOBUILD

/* Everything is built in a single CU, so even the top-level
 * mlkem-native API can have internal linkage. */
#define MLK_EXTERNAL_API static

/* Enable PCT if and only if AWS-LC is built in FIPS-mode. */
#if defined(AWSLC_FIPS)
#define MLK_KEYGEN_PCT
#endif /* AWSLC_FIPS */

/* Enable valgrind-based assertions in mlkem-native through macro
 * from AWS-LC/BoringSSL. */
#if defined(BORINGSSL_CONSTANT_TIME_VALIDATION)
#define MLK_CT_TESTING_ENABLED
#endif /* BORINGSSL_CONSTANT_TIME_VALIDATION */

/* Map zeroization function to the one used by AWS-LC */
#define MLK_USE_CT_ZEROIZE_NATIVE
#if !defined(__ASSEMBLER__) && !defined(MLK_MULTILEVEL_BUILD_NO_SHARED)
#include <stdint.h>
#include "mlkem/sys.h"
#include <openssl/base.h>
static MLK_INLINE void ct_zeroize_native(void *ptr, size_t len)
{
    OPENSSL_cleanse(ptr, len);
}
#endif /* !__ASSEMBLER__ */

#endif /* MLkEM_NATIVE_CONFIG_H */
