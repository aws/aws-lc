// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include "internal.h"
#include "openssl/mem.h"

#include <stdio.h>

#include <gtest/gtest.h>

TEST(MemTest, AlignedHeapAllocation) {
 
  // Should do nothing
  OPENSSL_free_align_internal(nullptr);

  size_t power_of_two = 1;

  do {
  	for (size_t memory_size : {1, 10, 32, 1001}) {
  		uint8_t *aligned_memory = (uint8_t *) OPENSSL_malloc_align_internal(memory_size, power_of_two);
  		ASSERT_TRUE(aligned_memory);
  		OPENSSL_free_align_internal(aligned_memory);
  		aligned_memory = NULL;
  	}
  	power_of_two <<= 1;
  } while (power_of_two <= 128);

  EXPECT_EQ(power_of_two, static_cast<size_t>(256));

  for (size_t alignment_boundary_should_fail : {0, 3, 24, 129}) {
  	uint8_t *aligned_memory = (uint8_t *) OPENSSL_malloc_align_internal(64, alignment_boundary_should_fail);
  	ASSERT_FALSE(aligned_memory);
  	aligned_memory = NULL;
  }
}
