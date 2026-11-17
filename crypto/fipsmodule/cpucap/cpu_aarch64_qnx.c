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

  // See the comment in cpu_aarch64_linux.c about OPENSSL_armcap.
  const char *env = getenv("OPENSSL_armcap");
  if (env != NULL) {
    handle_cpu_env(&OPENSSL_armcap_P, env);
  }

  OPENSSL_cpucap_initialized = 1;
}

#endif  // OPENSSL_AARCH64 && __QNX__ && !OPENSSL_STATIC_ARMCAP
