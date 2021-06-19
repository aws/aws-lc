// -----------------------------------------------------------------------------
// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// -----------------------------------------------------------------------------

#include <openssl/crypto.h>

#include "snapsafe_detect.h"

#if defined(OPENSSL_LINUX)

#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>

#include "../delocate.h"

DEFINE_STATIC_ONCE(g_snapsafe_detect_once)
DEFINE_STATIC_MUTEX(g_snapsafe_detect_lock)
DEFINE_BSS_GET(volatile uint32_t *, g_sysgenid_addr)
DEFINE_BSS_GET(int, g_ignore_snapsafe)
DEFINE_BSS_GET(int, g_overwrite_sysgenid)

static void init_snapsafe_detect(void) {

  // For testing purposes, we sometimes ignore snapsafe detection or overwrite
  // the SysGenID callback.
  if (*g_ignore_snapsafe_bss_get() == 1 || *g_overwrite_sysgenid_bss_get() == 1) {
    return;
  }

  long page_size = sysconf(_SC_PAGESIZE);
  if (page_size <= 0) {
    return;
  }

  int fd_sysgenid = open(AWSLC_SYSGENID_FILE_PATH, O_RDONLY);
  if (fd_sysgenid == -1) {
    return;
  }

  void *addr = mmap(NULL, (size_t) page_size, PROT_READ, MAP_SHARED,
                    fd_sysgenid, 0);

  // Can close |fd_sysgenid| now per
  // https://man7.org/linux/man-pages/man2/mmap.2.html: "After the mmap() call
  // has returned, the file descriptor, |fd_sysgenid|, can be closed immediately
  // without invalidating the mapping.". We have initialised Snapsafe detection
  // without errors and |init_snapsafe_detect| is only called once. Therefore,
  // try to close |fd_sysgenid|, but don't error if it fails.
  close(fd_sysgenid);

  if (addr == MAP_FAILED) {
    return;
  }

  *g_sysgenid_addr_bss_get() = addr;
}

int CRYPTO_get_snapsafe_generation(uint32_t *snapsafe_generation_number) {

  // Best-effort attempt to initialise Snapsafe detection.
  CRYPTO_once(g_snapsafe_detect_once_bss_get(), init_snapsafe_detect);

  volatile uint32_t *const sysgenid_addr = *g_sysgenid_addr_bss_get();
  if (sysgenid_addr == NULL) {
    // SysGenId is not supported on system.
    return 0;
  }

  struct CRYPTO_STATIC_MUTEX *const lock = g_snapsafe_detect_lock_bss_get();

  // Aquire both read and write locks for a short while.
  CRYPTO_STATIC_MUTEX_lock_write(lock);
  *snapsafe_generation_number = *sysgenid_addr;
  CRYPTO_STATIC_MUTEX_unlock_write(lock);

  return 1;
}

void CRYPTO_snapsafe_detect_ignore_for_testing(void) {
  *g_ignore_snapsafe_bss_get() = 1;
}

// Must call |HAZMAT_reset_sysgenid_for_testing| after finishing test suite to
// reset the SysGenID callback.
int HAZMAT_overwrite_sysgenid_for_testing(void) {

  *g_overwrite_sysgenid_bss_get() = 1;
  if (*g_sysgenid_addr_bss_get() != NULL) {
    // Release the current mapping.
    if (munmap((void *) *g_sysgenid_addr_bss_get(), sysconf(_SC_PAGESIZE)) == -1) {
      return 0;
    }
  }

  // Use plain dynamically allocated memory to simulate the SysGenID device.
  *g_sysgenid_addr_bss_get() = calloc(sizeof(uint32_t), 1);
  if (*g_sysgenid_addr_bss_get() == NULL) {
    return 0;
  }

  return 1;
}

void HAZMAT_reset_sysgenid_for_testing(void) {

  *g_overwrite_sysgenid_bss_get() = 0;
  free((void *) *g_sysgenid_addr_bss_get());
  *g_sysgenid_addr_bss_get() = NULL;

  // Re-initialise with default path. Needed because the init-once sentinel
  // |g_snapsafe_detect_once| might have been tripped and there is no way to
  // reset it.
  init_snapsafe_detect();
}

void HAZMAT_set_overwritten_sysgenid_for_testing(uint32_t val) {
  **g_sysgenid_addr_bss_get() = val;
}

#else // !defined(OPENSSL_LINUX)

int CRYPTO_get_snapsafe_generation(uint32_t *snapsafe_generation_number) { return 0; }

#endif // defined(OPENSSL_LINUX)
