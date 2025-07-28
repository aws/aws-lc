/* Copyright (c) 2020, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#if !defined(_GNU_SOURCE)
#define _GNU_SOURCE  // needed for madvise() and MAP_ANONYMOUS on Linux.
#endif

#include <openssl/base.h>

#include "fork_detect.h"

#if defined(OPENSSL_LINUX)
#include <sys/mman.h>
#include <unistd.h>
#include <stdlib.h>

#include <openssl/type_check.h>

#include "../delocate.h"
#include "../../internal.h"


#if defined(MADV_WIPEONFORK)
OPENSSL_STATIC_ASSERT(MADV_WIPEONFORK == 18, MADV_WIPEONFORK_is_not_18)
#else
#define MADV_WIPEONFORK 18
#endif

DEFINE_STATIC_ONCE(g_fork_detect_once)
DEFINE_STATIC_MUTEX(g_fork_detect_lock)
DEFINE_BSS_GET(volatile char *, g_fork_detect_addr)
DEFINE_BSS_GET(uint64_t, g_fork_generation)
DEFINE_BSS_GET(int, g_ignore_madv_wipeonfork)

static int init_fork_detect_madv_wipeonfork(void *addr, long page_size) {

  // Some versions of qemu (up to at least 5.0.0-rc4, see linux-user/syscall.c)
  // ignore |madvise| calls and just return zero (i.e. success). But we need to
  // know whether MADV_WIPEONFORK actually took effect. Therefore try an invalid
  // call to check that the implementation of |madvise| is actually rejecting
  // unknown |advice| values.
  if (madvise(addr, (size_t)page_size, -1) == 0 ||
      madvise(addr, (size_t)page_size, MADV_WIPEONFORK) != 0) {
    // The mapping |addr| points to is unmapped by caller.
    return 0;
  }

  return 1;
}

static void init_fork_detect(void) {

  int res = 0;
  void *addr = MAP_FAILED;
  long page_size = 0;

  // Check whether we are completely ignoring fork detection. This is only done
  // during testing.
  if (*g_ignore_madv_wipeonfork_bss_get() == 1) {
    goto cleanup;
  }

  page_size = sysconf(_SC_PAGESIZE);
  if (page_size <= 0) {
    goto cleanup;
  }

  addr = mmap(NULL, (size_t)page_size, PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (addr == MAP_FAILED) {
    goto cleanup;
  }


  if (init_fork_detect_madv_wipeonfork(addr, page_size) == 0) {
    goto cleanup;
  }

  *((volatile char *) addr) = 1;
  *g_fork_detect_addr_bss_get() = addr;
  *g_fork_generation_bss_get() = 1;

  res = 1;

cleanup:
  if (res == 0 && addr != MAP_FAILED) {
    munmap(addr, (size_t)page_size);
    addr = NULL;
  }
}

uint64_t CRYPTO_get_fork_generation(void) {
  // In a single-threaded process, there are obviously no races because there's
  // only a single mutator in the address space.
  //
  // In a multi-threaded environment, |CRYPTO_once| ensures that the flag byte
  // is initialised atomically, even if multiple threads enter this function
  // concurrently.
  //
  // In the limit, the kernel may clear WIPEONFORK pages while a multi-threaded
  // process is running. (For example, because a VM was cloned.) Therefore a
  // lock is used below to synchronise the potentially multiple threads that may
  // concurrently observe the cleared flag.

  CRYPTO_once(g_fork_detect_once_bss_get(), init_fork_detect);
  // This pointer is |volatile| because the value pointed to may be changed by
  // external forces (i.e. the kernel wiping the page) thus the compiler must
  // not assume that it has exclusive access to it.
  volatile char *const flag_ptr = *g_fork_detect_addr_bss_get();
  if (flag_ptr == NULL) {
    // Our kernel is too old to support |MADV_WIPEONFORK|.
    return 0;
  }

  struct CRYPTO_STATIC_MUTEX *const lock = g_fork_detect_lock_bss_get();
  uint64_t *const generation_ptr = g_fork_generation_bss_get();

  CRYPTO_STATIC_MUTEX_lock_read(lock);
  uint64_t current_generation = *generation_ptr;
  if (*flag_ptr) {
    CRYPTO_STATIC_MUTEX_unlock_read(lock);
    return current_generation;
  }

  CRYPTO_STATIC_MUTEX_unlock_read(lock);
  CRYPTO_STATIC_MUTEX_lock_write(lock);
  current_generation = *generation_ptr;
  if (*flag_ptr == 0) {
    // A fork has occurred.
    *flag_ptr = 1;

    current_generation++;
    if (current_generation == 0) {
      current_generation = 1;
    }
    *generation_ptr = current_generation;
  }
  CRYPTO_STATIC_MUTEX_unlock_write(lock);

  return current_generation;
}

void CRYPTO_fork_detect_ignore_madv_wipeonfork_for_testing(void) {
  *g_ignore_madv_wipeonfork_bss_get() = 1;
}

#elif defined(OPENSSL_WINDOWS)

// These platforms are guaranteed not to fork, and therefore do not require
// fork detection support. Returning a constant non zero value makes BoringSSL
// assume address space duplication is not a concern and adding entropy to
// every RAND_bytes call is not needed.
uint64_t CRYPTO_get_fork_generation(void) { return 0xc0ffee; }

#else

// These platforms may fork, but we do not have a mitigation mechanism in
// place.  Returning a constant zero value makes BoringSSL assume that address
// space duplication could have occured on any call entropy must be added to
// every RAND_bytes call.
uint64_t CRYPTO_get_fork_generation(void) { return 0; }

#endif
