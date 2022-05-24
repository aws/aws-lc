/* Copyright (c) 2014, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#include "internal.h"

#if (defined(OPENSSL_ARM) || defined(OPENSSL_AARCH64))

#if !defined(OPENSSL_STATIC_ARMCAP)

#include <openssl/arm_arch.h>


extern uint32_t OPENSSL_armcap_P;

OPENSSL_INLINE int CRYPTO_is_NEON_capable_at_runtime(void) {
  return (OPENSSL_armcap_P & ARMV7_NEON) != 0;
}

OPENSSL_INLINE int CRYPTO_is_ARMv8_AES_capable_at_runtime(void) {
  return (OPENSSL_armcap_P & ARMV8_AES) != 0;
}

OPENSSL_INLINE int CRYPTO_is_ARMv8_PMULL_capable_at_runtime(void) {
  return (OPENSSL_armcap_P & ARMV8_PMULL) != 0;
}

#endif // !defined(OPENSSL_STATIC_ARMCAP) */

// CRYPTO_is_NEON_capable returns true if the current CPU has a NEON unit. If
// this is known statically, it is a constant inline function.
int CRYPTO_is_NEON_capable(void) {
#if defined(OPENSSL_STATIC_ARMCAP_NEON) || defined(__ARM_NEON)
  return 1;
#elif defined(OPENSSL_STATIC_ARMCAP)
  return 0;
#else
  return CRYPTO_is_NEON_capable_at_runtime();
#endif
}

int CRYPTO_is_ARMv8_AES_capable(void) {
#if defined(OPENSSL_STATIC_ARMCAP_AES) || defined(__ARM_FEATURE_AES)
  return 1;
#elif defined(OPENSSL_STATIC_ARMCAP)
  return 0;
#else
  return CRYPTO_is_ARMv8_AES_capable_at_runtime();
#endif
}

int CRYPTO_is_ARMv8_PMULL_capable(void) {
#if defined(OPENSSL_STATIC_ARMCAP_PMULL) || defined(__ARM_FEATURE_AES)
  return 1;
#elif defined(OPENSSL_STATIC_ARMCAP)
  return 0;
#else
  return CRYPTO_is_ARMv8_PMULL_capable_at_runtime();
#endif
}

#endif // (defined(OPENSSL_ARM) || defined(OPENSSL_AARCH64))
