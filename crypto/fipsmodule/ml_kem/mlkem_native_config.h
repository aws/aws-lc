// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef MLK_CONFIG_H
#define MLK_CONFIG_H

#include "../../internal.h"

// Namespacing: All symbols are of the form mlkem*. Level-specific
// symbols are further prefixed with their security level, e.g.
// mlkem512*, mlkem768*, mlkem1024*.
#define MLK_CONFIG_NAMESPACE_PREFIX mlkem

// Everything is built in a single CU, so both internal and external
// mlkem-native API can have internal linkage.
#define MLK_CONFIG_INTERNAL_API_QUALIFIER static
#define MLK_CONFIG_EXTERNAL_API_QUALIFIER static

// Enable PCT if and only if AWS-LC is built in FIPS-mode.
#if defined(AWSLC_FIPS)
#define MLK_CONFIG_KEYGEN_PCT
#endif

#if defined(BORINGSSL_FIPS_BREAK_TESTS)
#define MLK_CONFIG_KEYGEN_PCT_BREAKAGE_TEST
#if !defined(__ASSEMBLER__) && !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
#include "mlkem/sys.h"
static MLK_INLINE int mlk_break_pct(void) {
  return boringssl_fips_break_test("MLKEM_PWCT");
}
#endif // !__ASSEMBLER__
#endif // BORINGSSL_FIPS_BREAK_TESTS

// Enable valgrind-based assertions in mlkem-native through macro
// from AWS-LC/BoringSSL.
#if defined(BORINGSSL_CONSTANT_TIME_VALIDATION)
#define MLK_CONFIG_CT_TESTING_ENABLED
#endif

// Map zeroization function to the one used by AWS-LC
#define MLK_CONFIG_CUSTOM_ZEROIZE
#if !defined(__ASSEMBLER__) && !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
#include <stdint.h>
#include "mlkem/sys.h"
#include <openssl/base.h>
static MLK_INLINE void mlk_zeroize(void *ptr, size_t len) {
    OPENSSL_cleanse(ptr, len);
}
#endif // !__ASSEMBLER__

// Map randombytes function to the one used by AWS-LC
#define MLK_CONFIG_CUSTOM_RANDOMBYTES
#if !defined(__ASSEMBLER__) && !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
#include <stdint.h>
#include "mlkem/sys.h"
#include <openssl/rand.h>
static MLK_INLINE void mlk_randombytes(void *ptr, size_t len) {
    RAND_bytes(ptr, len);
}
#endif // !__ASSEMBLER__

#if defined(OPENSSL_NO_ASM)
#define MLK_CONFIG_NO_ASM
#endif

#endif // MLkEM_NATIVE_CONFIG_H
