// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <gtest/gtest.h>
#include <openssl/mem.h>

int alloc_count = 0;
size_t test_size = 0;
int free_count = 0;
int size_count = 0;
int realloc_count = 0;

extern "C" {
  OPENSSL_EXPORT void *OPENSSL_memory_alloc(size_t size);
  OPENSSL_EXPORT void OPENSSL_memory_free(void *ptr);
  OPENSSL_EXPORT size_t OPENSSL_memory_get_size(void *ptr);
  OPENSSL_EXPORT void *OPENSSL_memory_realloc(void *ptr, size_t size);

  void *OPENSSL_memory_alloc(size_t size) {
    alloc_count++;
    test_size = size;
    return malloc(size);
  }

  void OPENSSL_memory_free(void *ptr) {
    free_count++;
    free(ptr);
  }

  size_t OPENSSL_memory_get_size(void *ptr) {
    size_count++;
    return test_size;
  }

  void *OPENSSL_memory_realloc(void *ptr, size_t size) {
    realloc_count++;
    return realloc(ptr, size);
  }
}
TEST(MemTest, BasicOverrides) {
  // The FIPS build which runs the power on self tests can call a lot of functions
  // before this test. Therefore all of the expected counts are relative to the
  // starting point
  int starting_alloc = alloc_count;
  int starting_free = free_count;
  int starting_realloc = realloc_count;

  void *malloc_ptr = nullptr;
  // Check setup conditions
  ASSERT_EQ(starting_alloc, alloc_count);
  ASSERT_EQ(starting_free, free_count);
  ASSERT_EQ(starting_realloc, realloc_count);
  ASSERT_EQ(0, size_count);
  ASSERT_EQ(malloc_ptr, nullptr);

  // Verify malloc calls OPENSSL_memory_alloc and doesn't do anything else
  test_size = 10;
  malloc_ptr = OPENSSL_malloc(test_size);
  ASSERT_NE(malloc_ptr, nullptr);
  ASSERT_EQ(starting_alloc + 1, alloc_count);
  ASSERT_EQ(starting_free, free_count);
  ASSERT_EQ(starting_realloc, realloc_count);
  ASSERT_EQ(0, size_count);

  // Calling realloc with null actually calls OPENSSL_malloc which calls
  // OPENSSL_memory_alloc
  void *null_realloc_ptr = nullptr;
  test_size = 200;
  void *realloc_ptr_1 = OPENSSL_realloc(null_realloc_ptr, test_size);
  ASSERT_NE(realloc_ptr_1, nullptr);
  ASSERT_EQ(starting_alloc + 2, alloc_count);
  ASSERT_EQ(starting_free, free_count);
  ASSERT_EQ(starting_realloc, realloc_count);
  ASSERT_EQ(0, size_count);
  ASSERT_EQ(nullptr, null_realloc_ptr);

  // Check realloc with a not null pointer calls OPENSSL_memory_realloc
  ASSERT_NE(realloc_ptr_1, nullptr);
  test_size = 300;
  void *realloc_ptr_2 = OPENSSL_realloc(malloc_ptr, test_size);
  ASSERT_NE(realloc_ptr_2, realloc_ptr_1);
  ASSERT_NE(realloc_ptr_2, malloc_ptr);
  ASSERT_EQ(starting_alloc + 2, alloc_count);
  ASSERT_EQ(starting_free, free_count);
  ASSERT_EQ(starting_realloc + 1, realloc_count);
  ASSERT_EQ(0, size_count);

  // Check OPENSSL_memory_free
  OPENSSL_free(realloc_ptr_1);
  ASSERT_EQ(starting_alloc + 2, alloc_count);
  ASSERT_EQ(starting_free + 1, free_count);
  ASSERT_EQ(starting_realloc + 1, realloc_count);
  ASSERT_EQ(0, size_count);
  OPENSSL_free(realloc_ptr_2);
}
