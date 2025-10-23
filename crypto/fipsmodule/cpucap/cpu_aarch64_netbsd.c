// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/cpu.h>

#if defined(OPENSSL_AARCH64) && defined(OPENSSL_NETBSD) && \
    !defined(OPENSSL_STATIC_ARMCAP)

#include <aarch64/armreg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/param.h>
#include <sys/sysctl.h>

#include <openssl/arm_arch.h>

#include "internal.h"

void OPENSSL_cpuid_setup(void) {
  // Use sysctl to read ID_AA64ISAR0_EL1 register
  size_t len = sizeof(uint64_t);
  uint64_t id_aa64isar0 = 0;

  // Try to read the aarch64 instruction set attribute register
  if (sysctlbyname("machdep.id_aa64isar0", &id_aa64isar0, &len, NULL, 0) < 0) {
    return;
  }

  OPENSSL_armcap_P |= ARMV7_NEON; // NEON is baseline on AArch64

  if (ID_AA64ISAR0_EL1_AES(id_aa64isar0) >= ID_AA64ISAR0_EL1_AES_AES) {
    OPENSSL_armcap_P |= ARMV8_AES;
  }

  if (ID_AA64ISAR0_EL1_AES(id_aa64isar0) >= ID_AA64ISAR0_EL1_AES_PMUL) {
    OPENSSL_armcap_P |= ARMV8_PMULL;
  }

  if (ID_AA64ISAR0_EL1_SHA1(id_aa64isar0) >= ID_AA64ISAR0_EL1_SHA1_SHA1) {
    OPENSSL_armcap_P |= ARMV8_SHA1;
  }

  if (ID_AA64ISAR0_EL1_SHA2(id_aa64isar0) >= ID_AA64ISAR0_EL1_SHA2_SHA256) {
    OPENSSL_armcap_P |= ARMV8_SHA256;
  }

  if (ID_AA64ISAR0_EL1_SHA2(id_aa64isar0) >= ID_AA64ISAR0_EL1_SHA2_SHA512) {
    OPENSSL_armcap_P |= ARMV8_SHA512;
  }
}

#endif  // OPENSSL_AARCH64 && OPENSSL_NETBSD && !OPENSSL_STATIC_ARMCAP
