#ifndef OPENSSL_HEADER_CPUCAP_INTERNAL_H
#define OPENSSL_HEADER_CPUCAP_INTERNAL_H

#include <openssl/base.h>

#if defined(__cplusplus)
extern "C" {
#endif

#if defined(OPENSSL_X86) || defined(OPENSSL_X86_64) || defined(OPENSSL_ARM) || \
    defined(OPENSSL_AARCH64) || defined(OPENSSL_PPC64LE)
// OPENSSL_cpuid_setup initializes the platform-specific feature cache.
void OPENSSL_cpuid_setup(void);
#endif

// Runtime CPU feature support

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

#if defined(BORINGSSL_FIPS) && !defined(BORINGSSL_SHARED_LIBRARY)
// The FIPS module, as a static library, requires an out-of-line version of
// |OPENSSL_ia32cap_get| so accesses can be rewritten by delocate. Mark the
// function const so multiple accesses can be optimized together.
const uint32_t *OPENSSL_ia32cap_get(void) __attribute__((const));
#else
OPENSSL_INLINE const uint32_t *OPENSSL_ia32cap_get(void) {
  return OPENSSL_ia32cap_P;
}
#endif

// See Intel manual, volume 2A, table 3-11.

OPENSSL_INLINE int CRYPTO_is_FXSR_capable(void) {
  return (OPENSSL_ia32cap_get()[0] & (1 << 24)) != 0;
}

OPENSSL_INLINE int CRYPTO_is_intel_cpu(void) {
  // The reserved bit 30 is used to indicate an Intel CPU.
  return (OPENSSL_ia32cap_get()[0] & (1 << 30)) != 0;
}

// See Intel manual, volume 2A, table 3-10.

OPENSSL_INLINE int CRYPTO_is_PCLMUL_capable(void) {
  return (OPENSSL_ia32cap_get()[1] & (1 << 1)) != 0;
}

OPENSSL_INLINE int CRYPTO_is_SSSE3_capable(void) {
  return (OPENSSL_ia32cap_get()[1] & (1 << 9)) != 0;
}

OPENSSL_INLINE int CRYPTO_is_SSE4_1_capable(void) {
  return (OPENSSL_ia32cap_get()[1] & (1 << 19)) != 0;
}

OPENSSL_INLINE int CRYPTO_is_MOVBE_capable(void) {
  return (OPENSSL_ia32cap_get()[1] & (1 << 22)) != 0;
}

OPENSSL_INLINE int CRYPTO_is_AESNI_capable(void) {
  return (OPENSSL_ia32cap_get()[1] & (1 << 25)) != 0;
}

OPENSSL_INLINE int CRYPTO_is_AVX_capable(void) {
  return (OPENSSL_ia32cap_get()[1] & (1 << 28)) != 0;
}

OPENSSL_INLINE int CRYPTO_is_RDRAND_capable(void) {
  return (OPENSSL_ia32cap_get()[1] & (1u << 30)) != 0;
}

OPENSSL_INLINE int CRYPTO_is_AMD_XOP_support(void) {
  return (OPENSSL_ia32cap_get()[1] & (1 << 11)) != 0;
}

// See Intel manual, volume 2A, table 3-8.

OPENSSL_INLINE int CRYPTO_is_BMI1_capable(void) {
  return (OPENSSL_ia32cap_get()[2] & (1 << 3)) != 0;
}

OPENSSL_INLINE int CRYPTO_is_AVX2_capable(void) {
  return (OPENSSL_ia32cap_get()[2] & (1 << 5)) != 0;
}

OPENSSL_INLINE int CRYPTO_is_BMI2_capable(void) {
  return (OPENSSL_ia32cap_get()[2] & (1 << 8)) != 0;
}

OPENSSL_INLINE int CRYPTO_is_ADX_capable(void) {
  return (OPENSSL_ia32cap_get()[2] & (1 << 19)) != 0;
}

OPENSSL_INLINE int CRYPTO_is_SHAEXT_capable(void) {
  return (OPENSSL_ia32cap_get()[2] & (1 << 29)) != 0;
}

OPENSSL_INLINE int CRYPTO_is_AVX512_capable(void) {
  return (OPENSSL_ia32cap_get()[2] & 0xC0030000) == 0xC0030000;
}

OPENSSL_INLINE int CRYPTO_is_VAES_capable(void) {
  return (OPENSSL_ia32cap_get()[3] & (1u << (41 - 32))) != 0;
}

OPENSSL_INLINE int CRYPTO_is_VPCLMULQDQ_capable(void) {
  return (OPENSSL_ia32cap_get()[3] & (1u << (42 - 32))) != 0;
}

OPENSSL_INLINE int CRYPTO_is_VBMI2_capable(void) {
  return (OPENSSL_ia32cap_get()[3] & (1 << 6)) != 0;
}


#endif  // OPENSSL_X86 || OPENSSL_X86_64

#if defined(OPENSSL_ARM) || defined(OPENSSL_AARCH64)

#if defined(OPENSSL_APPLE) && defined(OPENSSL_ARM)
// We do not detect any features at runtime for Apple's 32-bit ARM platforms. On
// 64-bit ARM, we detect some post-ARMv8.0 features.
#define OPENSSL_STATIC_ARMCAP
#endif

// Normalize some older feature flags to their modern ACLE values.
// https://developer.arm.com/architectures/system-architectures/software-standards/acle
#if defined(__ARM_NEON__) && !defined(__ARM_NEON)
#define __ARM_NEON 1
#endif
#if defined(__ARM_FEATURE_CRYPTO)
#if !defined(__ARM_FEATURE_AES)
#define __ARM_FEATURE_AES 1
#endif
#if !defined(__ARM_FEATURE_SHA2)
#define __ARM_FEATURE_SHA2 1
#endif
#endif

#include <openssl/arm_arch.h>

extern uint32_t OPENSSL_armcap_P;

// CRYPTO_is_NEON_capable returns true if the current CPU has a NEON unit.
// If this is known statically, it is a constant inline function.
// Otherwise, the capability is checked at runtime by checking the corresponding
// bit in |OPENSSL_armcap_P|. This is also the same for
// |CRYPTO_is_ARMv8_AES_capable| and |CRYPTO_is_ARMv8_PMULL_capable|
// for checking the support for AES and PMULL instructions, respectively.
OPENSSL_INLINE int CRYPTO_is_NEON_capable(void) {
  return (OPENSSL_armcap_P & ARMV7_NEON) != 0;
}

OPENSSL_INLINE int CRYPTO_is_ARMv8_AES_capable(void) {
  return (OPENSSL_armcap_P & ARMV8_AES) != 0;
}

OPENSSL_INLINE int CRYPTO_is_ARMv8_PMULL_capable(void) {
  return (OPENSSL_armcap_P & ARMV8_PMULL) != 0;
}

OPENSSL_INLINE int CRYPTO_is_ARMv8_GCM_8x_capable(void) {
  return ((OPENSSL_armcap_P & ARMV8_SHA3) != 0 &&
          ((OPENSSL_armcap_P & ARMV8_NEOVERSE_V1) != 0 ||
           (OPENSSL_armcap_P & ARMV8_APPLE_M1) != 0));
}

OPENSSL_INLINE int CRYPTO_is_ARMv8_wide_multiplier_capable(void) {
  return (OPENSSL_armcap_P & ARMV8_NEOVERSE_V1) != 0 ||
           (OPENSSL_armcap_P & ARMV8_APPLE_M1) != 0;
}

#endif  // OPENSSL_ARM || OPENSSL_AARCH64

#if defined(OPENSSL_PPC64LE)

// CRYPTO_is_PPC64LE_vcrypto_capable returns true iff the current CPU supports
// the Vector.AES category of instructions.
int CRYPTO_is_PPC64LE_vcrypto_capable(void);

extern unsigned long OPENSSL_ppc64le_hwcap2;

#endif  // OPENSSL_PPC64LE

#if defined(__cplusplus)
}
#endif

#endif // OPENSSL_HEADER_CPUCAP_INTERNAL_H
