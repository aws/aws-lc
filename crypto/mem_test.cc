// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include "internal.h"
#include "openssl/mem.h"

#include <stdio.h>

#include <gtest/gtest.h>

static bool verify_memory_alignment(void *aligned_ptr,
                                    size_t requested_alignment) {
  return (((uintptr_t) aligned_ptr) % requested_alignment) == 0;
}

TEST(MemTest, AlignedHeapAllocation) {
 
  // Should do nothing
  OPENSSL_free_align_internal(nullptr);

  size_t power_of_two = 1;

  do {
      for (size_t memory_size = 1; memory_size <= 2*power_of_two; memory_size++) {
        fprintf(stderr, "memory_size = %zu\n", memory_size);
        void *aligned_memory = OPENSSL_malloc_align_internal(memory_size, power_of_two);
        ASSERT_TRUE(aligned_memory);
        ASSERT_TRUE(verify_memory_alignment(aligned_memory, power_of_two));
        OPENSSL_free_align_internal(aligned_memory);
        aligned_memory = NULL;
    }
    power_of_two <<= 1;
  } while (power_of_two <= 128);

  EXPECT_EQ(power_of_two, static_cast<size_t>(256));

  for (size_t alignment_boundary_should_fail : {0, 3, 24, 129}) {
    void *aligned_memory = OPENSSL_malloc_align_internal(64, alignment_boundary_should_fail);
    ASSERT_FALSE(aligned_memory);
    aligned_memory = NULL;
  }
}
