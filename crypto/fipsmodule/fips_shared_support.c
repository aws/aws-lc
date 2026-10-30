// Copyright (c) 2019, Google Inc.
// SPDX-License-Identifier: ISC

// Ensure that no ambient #pragma const_seg is active. BORINGSSL_bcm_text_hash
// MUST be placed outside the FIPS module rodata boundary. If it were placed
// inside the FIPS rodata boundary, the integrity check would hash the expected
// value itself, creating a circular dependency that can never be satisfied.
#if defined(_MSC_VER)
#pragma const_seg()
#endif

#if defined(BORINGSSL_FIPS) && defined(BORINGSSL_SHARED_LIBRARY)
#include <stdint.h>

#if defined(__MINGW32__)
// MinGW brackets the module rodata with symbols in .rdata. Keep the expected
// hash in a separate read-only PE section so it cannot be included in the
// integrity input.
#define AWSLC_FIPS_HASH_SECTION __attribute__((section(".fipshash"), used))
#else
#define AWSLC_FIPS_HASH_SECTION
#endif

// BORINGSSL_bcm_text_hash is the default hash value for the FIPS integrity
// check that must be replaced with the real value during the build process.
// This value need only be distinct, i.e. so that we can safely
// search-and-replace it in an object file.
const uint8_t BORINGSSL_bcm_text_hash[32] AWSLC_FIPS_HASH_SECTION = {
    0xae, 0x2c, 0xea, 0x2a, 0xbd, 0xa6, 0xf3, 0xec, 0x97, 0x7f, 0x9b,
    0xf6, 0x94, 0x9a, 0xfc, 0x83, 0x68, 0x27, 0xcb, 0xa0, 0xa0, 0x9f,
    0x6b, 0x6f, 0xde, 0x52, 0xcd, 0xe2, 0xcd, 0xff, 0x31, 0x80,
};

#if defined(__MINGW32__)
// BORINGSSL_bcm_preferred_base records the link-time (preferred) PE image base
// of the crypto DLL. When a module is relocated for ASLR, the runtime integrity
// check subtracts the load delta from relocated cells before hashing, matching
// the on-disk preferred-base bytes that inject_hash.go measured. Like
// BORINGSSL_bcm_text_hash it lives outside the hashed module boundary, and
// because it is an integer (not a pointer) it carries no base relocation of its
// own, so its value is identical on disk and in memory.
//
// The initializer is a recognizable sentinel: if it survives to runtime, base
// injection did not run and the integrity check fails closed.
#define BORINGSSL_BCM_PREFERRED_BASE_UNSET UINT64_C(0xBADC0FFEE0DDF00D)
const uint64_t BORINGSSL_bcm_preferred_base AWSLC_FIPS_HASH_SECTION =
    BORINGSSL_BCM_PREFERRED_BASE_UNSET;
#endif
#else
// C requires a translation unit to contain at least one declaration. Since
// BORINGSSL_FIPS or BORINGSSL_SHARED_LIBRARY is not defined, this file is
// otherwise empty. This typedef prevents MSVC warning C4206.
typedef int fips_shared_support_dummy;
#endif  // FIPS && SHARED_LIBRARY
