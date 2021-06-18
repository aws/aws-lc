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
DEFINE_BSS_GET(const char *, g_sysgenid_file_path)
DEFINE_BSS_GET(int, g_ignore_snapsafe)

static char const * retrieve_sysgenid_file_path(void) {

  // If |sysgenid_file_path| is NULL, it means we have set the file path
  // through |hazmat_replace_snapsafe_file_path_for_testing| for testing
  // purposes. If NULL, use the expected SysGenID file path. This file path can
  // be overwritten at compile-time by defining the |SYSGENID_PATH| preprocessor
  // symbol to the desired path.
  if (*g_sysgenid_file_path_bss_get() != NULL) {
    return *g_sysgenid_file_path_bss_get();
  }
  else {
    return AWSLC_SYSGENID_FILE_PATH;
  }
}

static void init_snapsafe_detect(void) {

  // For testing purposes, we sometimes ignore snapsafe detection.
  if (*g_ignore_snapsafe_bss_get() == 1) {
    return;
  }

  long page_size = sysconf(_SC_PAGESIZE);
  if (page_size <= 0) {
    return;
  }

  fprintf(stderr, "init_snapsafe_detect sysgenid file path %s\n", retrieve_sysgenid_file_path());
  int fd_sysgenid = open(retrieve_sysgenid_file_path(), O_RDONLY);
  if (fd_sysgenid == -1) {
    return;
  }

  fprintf(stderr, "init_snapsafe_detect mmap\n");
  void *addr = mmap(NULL, (size_t) page_size, PROT_READ, MAP_SHARED,
            fd_sysgenid, 0);

  // Can close fd now per https://man7.org/linux/man-pages/man2/mmap.2.html
  // "After the mmap() call has returned, the file descriptor, fd, can
  // be closed immediately without invalidating the mapping.". We have
  // initialised Snapsafe detection without errors and |init_snapsafe_detect| is
  // only called once. Therefore, try to close fd, but don't error if it fails.
  close(fd_sysgenid);

  fprintf(stderr, "init_snapsafe_detect mmap failed?\n");
  if (addr == MAP_FAILED) {
    return;
  }

  fprintf(stderr, "init_snapsafe_detect set cb address\n");
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

void HAZMAT_replace_sysgenid_file_path_for_testing(const char *new_sysgenid_path) {
  fprintf(stderr, "Replacing the default SysGenID path with the path %s\n"
    "This should only happen during testing!\n",
    new_sysgenid_path);
  *g_sysgenid_file_path_bss_get() = new_sysgenid_path;
  fprintf(stderr, "HAZMAT_replace_sysgenid_file_path_for_testing sysgenid file path %s\n", retrieve_sysgenid_file_path());
}

#else // !defined(OPENSSL_LINUX)

int CRYPTO_get_snapsafe_generation(uint32_t *snapsafe_generation_number) { return 0; }

#endif // defined(OPENSSL_LINUX)
