// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <gtest/gtest.h>
#include <openssl/mem.h>

int alloc_count = 0;
void *test_pointer = NULL;
size_t test_size = 0;
int free_count = 0;
int get_count = 0;
int realloc_count = 0;

extern "C" {
__attribute__((visibility("default"))) void *OPENSSL_memory_alloc(size_t size);
__attribute__((visibility("default"))) void OPENSSL_memory_free(void *ptr);
__attribute__((visibility("default"))) size_t OPENSSL_memory_get_size(void *ptr);
__attribute__((visibility("default"))) void *OPENSSL_memory_realloc(void *ptr, size_t size);

void *OPENSSL_memory_alloc(size_t size) {
  alloc_count++;
  return test_pointer;
}

void OPENSSL_memory_free(void *ptr) {
  free_count++;
}

size_t OPENSSL_memory_get_size(void *ptr) {
  get_count++;
  return test_size;
}

void *OPENSSL_memory_realloc(void *ptr, size_t size) {
  realloc_count++;
  return test_pointer;
}
}
TEST(MemTest, BasicOverrides) {
  // Check setup conditions
  ASSERT_EQ(alloc_count, 0);
  ASSERT_EQ(free_count, 0);
  ASSERT_EQ(realloc_count, 0);
  ASSERT_EQ(get_count, 0);
  ASSERT_EQ(test_pointer, nullptr);

  // Verify malloc calls OPENSSL_memory_alloc and doesn't do anything else
  test_size = 10;
  ASSERT_EQ(OPENSSL_malloc(test_size), nullptr);
  ASSERT_EQ(alloc_count, 1);

  // Calling realloc with null actually calls OPENSSL_malloc which calls
  // OPENSSL_memory_alloc
  test_size = 20;
  ASSERT_EQ(OPENSSL_realloc(test_pointer, test_size), nullptr);
  ASSERT_EQ(alloc_count, 2);
  ASSERT_EQ(free_count, 0);
  ASSERT_EQ(realloc_count, 0);
  ASSERT_EQ(get_count, 0);
  ASSERT_EQ(test_pointer, nullptr);

  // Check realloc with a not null pointer calls OPENSSL_memory_realloc
  test_pointer = malloc(10);
  ASSERT_NE(test_pointer, nullptr);
  ASSERT_EQ(OPENSSL_realloc(test_pointer, 20), test_pointer);
  ASSERT_EQ(alloc_count, 2);
  ASSERT_EQ(free_count, 0);
  ASSERT_EQ(realloc_count, 1);
  ASSERT_EQ(get_count, 0);

  // Check OPENSSL_memory_free
  OPENSSL_free(test_pointer);
  ASSERT_NE(test_pointer, nullptr);
  ASSERT_EQ(alloc_count, 2);
  ASSERT_EQ(free_count, 1);
  ASSERT_EQ(realloc_count, 1);
  ASSERT_EQ(get_count, 0);
}
