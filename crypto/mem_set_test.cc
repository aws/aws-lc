// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/ec.h>
#include <openssl/mem.h>
#include <openssl/nid.h>

int alloc_count = 0;
size_t test_size = 0;
int free_count = 0;
int size_count = 0;
int realloc_count = 0;

// Number of further allocations that will succeed, or a negative value to let
// every allocation succeed. Used by |ScopedAllocBudget| to drive a library
// function into its out-of-memory paths.
static int allocs_left = -1;

extern "C" {
  void *new_malloc_impl(size_t size, const char *file, int line);
  void new_free_impl(void *ptr, const char *file, int line);
  void *new_realloc_impl(void *ptr, size_t size, const char *file, int line);
}

void *new_malloc_impl(size_t size, const char *file, int line) {
  if (allocs_left >= 0) {
    if (allocs_left == 0) {
      return nullptr;
    }
    allocs_left--;
  }
  alloc_count++;
  test_size = size;
  return malloc(size);
}

void new_free_impl(void *ptr, const char *file, int line) {
  free_count++;
  free(ptr);
}

void *new_realloc_impl(void *ptr, size_t size, const char *file, int line) {
  realloc_count++;
  return realloc(ptr, size);
}

// |CRYPTO_set_mem_functions| may only be called once per process, so every
// test in this binary installs the overrides through this helper, which
// performs the call on first use and reports the same result afterwards. This
// keeps the tests independent of the order they run in.
static int SetMemFunctionsOnce(void) {
  static const int ret =
      CRYPTO_set_mem_functions(new_malloc_impl, new_realloc_impl,
                               new_free_impl);
  return ret;
}

// Fails every |OPENSSL_malloc| after the first |budget| of them, for the
// lifetime of the object.
class ScopedAllocBudget {
 public:
  explicit ScopedAllocBudget(int budget) { allocs_left = budget; }
  ~ScopedAllocBudget() { allocs_left = -1; }
  ScopedAllocBudget(const ScopedAllocBudget &) = delete;
  ScopedAllocBudget &operator=(const ScopedAllocBudget &) = delete;
};

// This test is copy of |MemTest.BasicOverrides| in mem_test.cc.
// |MemTest.BasicOverrides| changed the |OPENSSL_malloc/free/realloc| by overriding related weak symbols.
// This test achieved the mem behavior change by calling |CRYPTO_set_mem_functions|.
TEST(MemTest, BasicMemSet) {
  // The FIPS build which runs the power on self tests can call a lot of functions
  // before this test. Therefore, all the expected counts are relative to the
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

  // Call |CRYPTO_set_mem_functions| to override |OPENSSL_malloc/realloc/free|.
  ASSERT_EQ(1, SetMemFunctionsOnce());

  // Verify malloc calls |new_malloc_impl| and doesn't do anything else
  test_size = 10;
  malloc_ptr = OPENSSL_malloc(test_size);
  ASSERT_NE(malloc_ptr, nullptr);
  ASSERT_EQ(starting_alloc + 1, alloc_count);
  ASSERT_EQ(starting_free, free_count);
  ASSERT_EQ(starting_realloc, realloc_count);
  ASSERT_EQ(0, size_count);

  // Calling realloc with null actually calls |OPENSSL_malloc| which calls
  // |new_realloc_impl|
  void *null_realloc_ptr = nullptr;
  test_size = 200;
  void *realloc_ptr_1 = OPENSSL_realloc(null_realloc_ptr, test_size);
  ASSERT_NE(realloc_ptr_1, nullptr);
  ASSERT_EQ(starting_alloc + 2, alloc_count);
  ASSERT_EQ(starting_free, free_count);
  ASSERT_EQ(starting_realloc, realloc_count);
  ASSERT_EQ(0, size_count);
  ASSERT_EQ(nullptr, null_realloc_ptr);

  // Calling realloc with a not null pointer calls |new_realloc_impl|
  test_size = 300;
  void *realloc_ptr_2 = OPENSSL_realloc(malloc_ptr, test_size);
  ASSERT_EQ(starting_alloc + 2, alloc_count);
  ASSERT_EQ(starting_free, free_count);
  ASSERT_EQ(starting_realloc + 1, realloc_count);
  ASSERT_EQ(0, size_count);

  // Check |new_free_impl| calls our symbol as expected
  OPENSSL_free(realloc_ptr_1);
  ASSERT_EQ(starting_alloc + 2, alloc_count);
  ASSERT_EQ(starting_free + 1, free_count);
  ASSERT_EQ(starting_realloc + 1, realloc_count);
  ASSERT_EQ(0, size_count);
  OPENSSL_free(realloc_ptr_2);
}


TEST(ECTest, PointNewGroupDupFailure) {
  ASSERT_EQ(1, SetMemFunctionsOnce());

  // We support both mutable and static |EC_GROUP| objects. |EC_POINT_new|
  // therefore either deep copies or simply returns a reference to the argument
  // when generating the new |EC_POINT| object. Test that we don't crash if the
  // deep copy fails.

  // The static built-in groups are never copied, so use a mutable one.
  bssl::UniquePtr<EC_GROUP> group(
      EC_GROUP_new_by_curve_name_mutable(NID_X9_62_prime256v1));
  ASSERT_TRUE(group);

  // Sanity check: the call succeeds when allocation is unconstrained, and the
  // resulting point is usable.
  bssl::UniquePtr<EC_POINT> point(EC_POINT_new(group.get()));
  ASSERT_TRUE(point);
  EXPECT_TRUE(EC_POINT_is_at_infinity(group.get(), point.get()));
  point.reset();

  {
    // Fail the very first allocation, which is the |EC_POINT| itself.
    ScopedAllocBudget budget(0);
    EXPECT_FALSE(EC_POINT_new(group.get()));
  }

  {
    // Allow the |EC_POINT| allocation to succeed and fail the group copy that
    // follows it.
    ScopedAllocBudget budget(1);
    point.reset(EC_POINT_new(group.get()));
    EXPECT_FALSE(point);
  }

  // Allocation works again afterwards.
  point.reset(EC_POINT_new(group.get()));
  ASSERT_TRUE(point);
  EXPECT_TRUE(EC_POINT_is_at_infinity(group.get(), point.get()));
}
