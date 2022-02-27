/* Copyright (c) 2017, Google Inc.
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

#include <openssl/cpu.h>

#if defined(OPENSSL_X86) || defined(OPENSSL_X86_64)
// OPENSSL_ia32cap_P contains the Intel CPUID bits when running on an x86 or
// x86-64 system.
//
//   Index 0:
//     EDX for CPUID where EAX = 1
//     Bit 20 is always zero
//     Bit 28 is adjusted to reflect whether the data cache is shared between
//       multiple logical cores
//     Bit 30 is used to indicate an Intel CPU
//   Index 1:
//     ECX for CPUID where EAX = 1
//     Bit 11 is used to indicate AMD XOP support, not SDBG
//   Index 2:
//     EBX for CPUID where EAX = 7
//   Index 3:
//     ECX for CPUID where EAX = 7
//
// Note: the CPUID bits are pre-adjusted for the OSXSAVE bit and the YMM and XMM
// bits in XCR0, so it is not necessary to check those.
extern uint32_t OPENSSL_ia32cap_P[4];

// Below functions are consolidated OPENSSL_ia32cap_P checks, which are from boringssl@4d955d2.
// The functions are moved from "crypto/internal.h" to "crypto/fipsmodule/internal.h".
// This move was made in "PR#330: Moved the CPU capability logic inside fipsmodule".

// See Intel manual, volume 2A, table 3-11.

OPENSSL_INLINE int CRYPTO_is_FXSR_capable(void) {
#if defined(__FXSR__)
  return 1;
#else
  return (OPENSSL_ia32cap_P[0] & (1 << 24)) != 0;
#endif
}

OPENSSL_INLINE int CRYPTO_is_intel_cpu(void) {
  // The reserved bit 30 is used to indicate an Intel CPU.
  return (OPENSSL_ia32cap_P[0] & (1 << 30)) != 0;
}

// See Intel manual, volume 2A, table 3-10.

OPENSSL_INLINE int CRYPTO_is_PCLMUL_capable(void) {
#if defined(__PCLMUL__)
  return 1;
#else
  return (OPENSSL_ia32cap_P[1] & (1 << 1)) != 0;
#endif
}

OPENSSL_INLINE int CRYPTO_is_SSSE3_capable(void) {
#if defined(__SSSE3__)
  return 1;
#else
  return (OPENSSL_ia32cap_P[1] & (1 << 9)) != 0;
#endif
}

OPENSSL_INLINE int CRYPTO_is_SSE4_1_capable(void) {
#if defined(__SSE4_1__)
  return 1;
#else
  return (OPENSSL_ia32cap_P[1] & (1 << 19)) != 0;
#endif
}

OPENSSL_INLINE int CRYPTO_is_MOVBE_capable(void) {
#if defined(__MOVBE__)
  return 1;
#else
  return (OPENSSL_ia32cap_P[1] & (1 << 22)) != 0;
#endif
}

OPENSSL_INLINE int CRYPTO_is_AESNI_capable(void) {
#if defined(__AES__)
  return 1;
#else
  return (OPENSSL_ia32cap_P[1] & (1 << 25)) != 0;
#endif
}

OPENSSL_INLINE int CRYPTO_is_AVX_capable(void) {
#if defined(__AVX__)
  return 1;
#else
  return (OPENSSL_ia32cap_P[1] & (1 << 28)) != 0;
#endif
}

OPENSSL_INLINE int CRYPTO_is_RDRAND_capable(void) {
  // The GCC/Clang feature name and preprocessor symbol for RDRAND are "rdrnd"
  // and |__RDRND__|, respectively.
#if defined(__RDRND__)
  return 1;
#else
  return (OPENSSL_ia32cap_P[1] & (1u << 30)) != 0;
#endif
}

// See Intel manual, volume 2A, table 3-8.

OPENSSL_INLINE int CRYPTO_is_BMI1_capable(void) {
#if defined(__BMI1__)
  return 1;
#else
  return (OPENSSL_ia32cap_P[2] & (1 << 3)) != 0;
#endif
}

OPENSSL_INLINE int CRYPTO_is_AVX2_capable(void) {
#if defined(__AVX2__)
  return 1;
#else
  return (OPENSSL_ia32cap_P[2] & (1 << 5)) != 0;
#endif
}

OPENSSL_INLINE int CRYPTO_is_BMI2_capable(void) {
#if defined(__BMI2__)
  return 1;
#else
  return (OPENSSL_ia32cap_P[2] & (1 << 8)) != 0;
#endif
}

OPENSSL_INLINE int CRYPTO_is_ADX_capable(void) {
#if defined(__ADX__)
  return 1;
#else
  return (OPENSSL_ia32cap_P[2] & (1 << 19)) != 0;
#endif
}

#endif  // OPENSSL_X86 || OPENSSL_X86_64
