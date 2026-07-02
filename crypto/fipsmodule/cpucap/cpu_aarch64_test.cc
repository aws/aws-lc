// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>

#if defined(OPENSSL_AARCH64)

#include <openssl/arm_arch.h>

#include <gtest/gtest.h>

TEST(AArch64CPUTest, NeoverseN2MIDR) {
  struct {
    uint64_t midr;
    bool is_neoverse_n2;
  } kTests[] = {
      {MIDR_CPU_MODEL(ARM_CPU_IMP_ARM, ARM_CPU_PART_N2), true},
      {MIDR_CPU_MODEL(ARM_CPU_IMP_MICROSOFT,
                      MICROSOFT_CPU_PART_AZURE_COBALT_100),
       true},
      {MIDR_CPU_MODEL(ARM_CPU_IMP_ARM, ARM_CPU_PART_N2) | (1UL << 20) | 1,
       true},
      {MIDR_CPU_MODEL(0x42, ARM_CPU_PART_N2), false},
      {MIDR_CPU_MODEL(ARM_CPU_IMP_ARM, ARM_CPU_PART_V2), false},
  };

  for (const auto &test : kTests) {
    SCOPED_TRACE(test.midr);
    EXPECT_EQ(test.is_neoverse_n2, MIDR_IS_NEOVERSE_N2(test.midr));
  }
}

#endif  // OPENSSL_AARCH64
