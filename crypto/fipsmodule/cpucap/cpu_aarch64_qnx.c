// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "internal.h"

#if defined(OPENSSL_AARCH64) && defined(__QNX__) && \
    !defined(OPENSSL_STATIC_ARMCAP)

#include <sys/syspage.h>
#include <aarch64/syspage.h>

#include <openssl/arm_arch.h>

#include "cpu_aarch64.h"

// QNX Neutrino has no getauxval/AT_HWCAP. The startup program probes the
// ID_AA64* registers at boot and records the result in the |flags| field of
// each |cpuinfo| entry of the system page, which is mapped read-only into every
// process. See <aarch64/syspage.h> for the AARCH64_CPU_FLAG_* values.
void OPENSSL_cpuid_setup(void) {
  unsigned num_cpu = _syspage_ptr->num_cpu;
  if (num_cpu == 0) {
    return;
  }

  // Only report features present on every core, in case the system is
  // heterogeneous and the thread migrates. Step through the array with
  // SYSPAGE_ARRAY_IDX because the startup program's element size may differ
  // from this SDK's sizeof(struct cpuinfo_entry).
  uint64_t flags = ~(uint64_t)0;
  for (unsigned i = 0; i < num_cpu; i++) {
    flags &= SYSPAGE_ARRAY_IDX(cpuinfo, i)->flags;
  }

  if ((flags & AARCH64_CPU_FLAG_SIMD) == 0) {
    // Matching OpenSSL, if NEON is missing, don't report other features
    // either.
    return;
  }

  OPENSSL_armcap_P |= ARMV7_NEON;

  // SDP 7.x headers lack most of these flags, so check each one. Building
  // against them gives a NEON-only configuration.
#if defined(AARCH64_CPU_FLAG_AES)
  if (flags & AARCH64_CPU_FLAG_AES) {
    OPENSSL_armcap_P |= ARMV8_AES;
  }
#endif
#if defined(AARCH64_CPU_FLAG_PMULL)
  if (flags & AARCH64_CPU_FLAG_PMULL) {
    OPENSSL_armcap_P |= ARMV8_PMULL;
  }
#endif
#if defined(AARCH64_CPU_FLAG_SHA1)
  if (flags & AARCH64_CPU_FLAG_SHA1) {
    OPENSSL_armcap_P |= ARMV8_SHA1;
  }
#endif
#if defined(AARCH64_CPU_FLAG_SHA256)
  if (flags & AARCH64_CPU_FLAG_SHA256) {
    OPENSSL_armcap_P |= ARMV8_SHA256;
  }
#endif
#if defined(AARCH64_CPU_FLAG_SHA512)
  if (flags & AARCH64_CPU_FLAG_SHA512) {
    OPENSSL_armcap_P |= ARMV8_SHA512;
  }
#endif
#if defined(AARCH64_CPU_FLAG_SHA3)
  if (flags & AARCH64_CPU_FLAG_SHA3) {
    OPENSSL_armcap_P |= ARMV8_SHA3;
  }
#endif
#if defined(AARCH64_CPU_FLAG_RNDR)
  if (flags & AARCH64_CPU_FLAG_RNDR) {
    OPENSSL_armcap_P |= ARMV8_RNG;
  }
#endif

  // The startup program also records each core's MIDR_EL1 in the |cpu| field
  // of its |cpuinfo| entry, so the Neoverse checks done in
  // cpu_aarch64_linux.c can be made here without reading the register. As
  // with |flags| above, only set them if every core is the same model.
  uint64_t midr = SYSPAGE_ARRAY_IDX(cpuinfo, 0)->cpu;
  int same_model = 1;
  for (unsigned i = 1; i < num_cpu; i++) {
    uint64_t other = SYSPAGE_ARRAY_IDX(cpuinfo, i)->cpu;
    if ((other & MIDR_CPU_MODEL_MASK) != (midr & MIDR_CPU_MODEL_MASK)) {
      same_model = 0;
      break;
    }
  }
  if (same_model) {
    if (MIDR_IS_CPU_MODEL(midr, ARM_CPU_IMP_ARM, ARM_CPU_PART_N1)) {
      OPENSSL_armcap_P |= ARMV8_NEOVERSE_N1;
    }
    if (MIDR_IS_CPU_MODEL(midr, ARM_CPU_IMP_ARM, ARM_CPU_PART_V1)) {
      OPENSSL_armcap_P |= ARMV8_NEOVERSE_V1;
      // CPU capabilities of N1 are a subset of CPU capabilities of V1
      OPENSSL_armcap_P |= ARMV8_NEOVERSE_N1;
    }
    if (MIDR_IS_CPU_MODEL(midr, ARM_CPU_IMP_ARM, ARM_CPU_PART_V2)) {
      OPENSSL_armcap_P |= ARMV8_NEOVERSE_V2;
      // CPU capabilities of N1 are a subset of CPU capabilities of V2
      OPENSSL_armcap_P |= ARMV8_NEOVERSE_N1;
    }
    if (MIDR_IS_CPU_MODEL(midr, ARM_CPU_IMP_ARM, ARM_CPU_PART_V3)) {
      OPENSSL_armcap_P |= ARMV8_NEOVERSE_V3;
      // CPU capabilities of N1 are a subset of CPU capabilities of V3
      OPENSSL_armcap_P |= ARMV8_NEOVERSE_N1;
    }
  }

  // See the comment in cpu_aarch64_linux.c about OPENSSL_armcap.
  const char *env = getenv("OPENSSL_armcap");
  if (env != NULL) {
    handle_cpu_env(&OPENSSL_armcap_P, env);
  }

  OPENSSL_cpucap_initialized = 1;
}

#endif  // OPENSSL_AARCH64 && __QNX__ && !OPENSSL_STATIC_ARMCAP
