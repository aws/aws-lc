// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include <set>

#include "err/internal.h"
#include "internal.h"
#if defined(AWSLC_MEM_SET_TEST_SSL)
#include "../ssl/internal.h"
#endif

int alloc_count = 0;
size_t test_size = 0;
int free_count = 0;
int size_count = 0;
int realloc_count = 0;

extern "C" {
  void *new_malloc_impl(size_t size, const char *file, int line);
  void new_free_impl(void *ptr, const char *file, int line);
  void *new_realloc_impl(void *ptr, size_t size, const char *file, int line);
}

// The custom allocator tracks its live allocations. If AWS-LC passes a system
// |malloc| pointer to |new_free_impl|, it aborts. This mirrors a shared-memory
// allocator, where mixing the two corrupts the heap. The tests check the
// allocation and free counts to catch the reverse, a custom allocation freed
// with the system |free|. The set is never destroyed because AWS-LC may free
// memory from thread-local destructors during process exit. It is not locked
// because these tests are single-threaded, and some targets, such as WASI, have
// no |std::mutex|.
static std::set<void *> *g_live = new std::set<void *>;

static void *track(void *ptr) {
  if (ptr != nullptr) {
    g_live->insert(ptr);
  }
  return ptr;
}

static void untrack(void *ptr) {
  if (g_live->erase(ptr) != 1) {
    abort();
  }
}

void *new_malloc_impl(size_t size, const char *file, int line) {
  alloc_count++;
  test_size = size;
  return track(malloc(size));
}

void new_free_impl(void *ptr, const char *file, int line) {
  free_count++;
  untrack(ptr);
  free(ptr);
}

void *new_realloc_impl(void *ptr, size_t size, const char *file, int line) {
  realloc_count++;
  untrack(ptr);
  void *ret = realloc(ptr, size);
  if (ret == nullptr) {
    // On failure, |ptr| is still live.
    track(ptr);
    return nullptr;
  }
  return track(ret);
}

// |CRYPTO_set_mem_functions| may only succeed once per process, so every test
// installs the allocator through this.
static bool g_installed = false;
static void InstallMemFunctions() {
  if (!g_installed) {
    ASSERT_EQ(1, CRYPTO_set_mem_functions(new_malloc_impl, new_realloc_impl,
                                          new_free_impl));
    g_installed = true;
  }
}

// |OPENSSL_raw_malloc| must use the custom allocator once one is installed, and
// memory from before then must still be freed with the system |free|. This test
// is first so it runs before the allocator is installed.
TEST(MemTest, RawMallocUsesMemSet) {
  int hooked = 0;
  void *before = nullptr;
  if (!g_installed) {
    before = OPENSSL_raw_malloc(10, &hooked);
    ASSERT_TRUE(before);
    EXPECT_EQ(0, hooked);
  }

  ASSERT_NO_FATAL_FAILURE(InstallMemFunctions());

  int starting_alloc = alloc_count;
  int starting_free = free_count;
  void *after = OPENSSL_raw_malloc(10, &hooked);
  ASSERT_TRUE(after);
  EXPECT_EQ(1, hooked);
  EXPECT_EQ(starting_alloc + 1, alloc_count);
  OPENSSL_raw_free(after, hooked);
  EXPECT_EQ(starting_free + 1, free_count);

  // Must not reach |new_free_impl|, which would abort on an untracked pointer.
  OPENSSL_raw_free(before, 0);
  EXPECT_EQ(starting_free + 1, free_count);
}

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
  ASSERT_NO_FATAL_FAILURE(InstallMemFunctions());
  ASSERT_EQ(0, CRYPTO_set_mem_functions(new_malloc_impl, new_realloc_impl,
                                        new_free_impl));

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

// Error data and |ERR_SAVE_STATE| are stored in |SSL| objects, so they must use
// the custom allocator.
TEST(MemTest, ErrUsesMemSet) {
  ASSERT_NO_FATAL_FAILURE(InstallMemFunctions());
  ERR_clear_error();

  int starting_alloc = alloc_count;
  int starting_free = free_count;
  OPENSSL_PUT_ERROR(SSL, ERR_R_INTERNAL_ERROR);
  ERR_add_error_data(2, "hello ", "world");
  ERR_add_error_dataf("%s %d", "number", 42);
  // The error data strings go through the custom allocator.
  EXPECT_GT(alloc_count, starting_alloc);

  int saved_alloc = alloc_count;
  ERR_SAVE_STATE *saved = ERR_save_state();
  ASSERT_TRUE(saved);
  // The state, its errors, and the copied data string.
  EXPECT_EQ(saved_alloc + 3, alloc_count);

  ERR_clear_error();
  ERR_restore_state(saved);
  const char *data = nullptr;
  int flags = 0;
  ERR_peek_error_line_data(nullptr, nullptr, &data, &flags);
  EXPECT_STREQ("number 42", data);
  ERR_SAVE_STATE_free(saved);

  ERR_clear_error();
  // Everything allocated by this test has been freed with |new_free_impl|.
  EXPECT_EQ(alloc_count - starting_alloc, free_count - starting_free);
}

#if defined(AWSLC_MEM_SET_TEST_SSL)
// |SSLBuffer| backs the TLS record buffers in |SSL| objects, so it must use the
// custom allocator.
TEST(MemTest, SSLBufferUsesMemSet) {
  ASSERT_NO_FATAL_FAILURE(InstallMemFunctions());

  int starting_alloc = alloc_count;
  int starting_free = free_count;
  {
    bssl::SSLBuffer buf;
    ASSERT_TRUE(buf.EnsureCap(SSL3_RT_HEADER_LENGTH, 1000));
    EXPECT_EQ(starting_alloc + 1, alloc_count);
    // Growing the buffer frees the old allocation with the custom allocator.
    ASSERT_TRUE(buf.EnsureCap(SSL3_RT_HEADER_LENGTH, 2000));
    EXPECT_EQ(starting_alloc + 2, alloc_count);
    EXPECT_EQ(starting_free + 1, free_count);
  }
  EXPECT_EQ(starting_free + 2, free_count);
}
#endif
