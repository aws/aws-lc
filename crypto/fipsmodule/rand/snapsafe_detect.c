// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/crypto.h>

#include "snapsafe_detect.h"

#if defined(OPENSSL_LINUX)
#include <fcntl.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>
#include "../delocate.h"

// Snapsafety state
#define SNAPSAFETY_STATE_FAILED_INITIALISE 0x00
#define SNAPSAFETY_STATE_SUCCESS_INITIALISE 0x01
#define SNAPSAFETY_STATE_NOT_SUPPORTED 0x02

DEFINE_STATIC_ONCE(aws_snapsafe_init)
DEFINE_BSS_GET(volatile uint32_t *, sgc_addr)
DEFINE_BSS_GET(int, snapsafety_state)

// aws_snapsafe_check_kernel_support returns 1 if the special sysgenid device
// file exists and 0 otherwise.
static int aws_snapsafe_check_kernel_support(void) {
  // This file-exist method is generally brittle. But for our purpose, this
  // should be more than fine.
  if (access(CRYPTO_get_sysgenid_path(), F_OK) != 0) {
    return 0;
  }
  return 1;
}

static void do_aws_snapsafe_init(void) {
  *snapsafety_state_bss_get() = SNAPSAFETY_STATE_NOT_SUPPORTED;
  *sgc_addr_bss_get() = NULL;

  if (aws_snapsafe_check_kernel_support() != 1) {
    return;
  }
  *snapsafety_state_bss_get() = SNAPSAFETY_STATE_FAILED_INITIALISE;

  int fd_sgc = open(CRYPTO_get_sysgenid_path(), O_RDONLY);
  if (fd_sgc == -1) {
    return;
  }

  void *addr = mmap(NULL, sizeof(uint32_t), PROT_READ, MAP_SHARED, fd_sgc, 0);

  // Can close file descriptor now per
  // https://man7.org/linux/man-pages/man2/mmap.2.html: "After the mmap() call
  // has returned, the file descriptor, fd, can be closed immediately without
  // invalidating the mapping.". We have initialised snapsafety without errors
  // and this function is only executed once. Therefore, try to close file
  // descriptor but don't error if it fails. */
  close(fd_sgc);

  if (addr == MAP_FAILED) {
    return;
  }

  // sgc_addr will now point at the mapped memory and any 4-byte read from
  // this pointer will correspond to the sgn managed by the VMM.
  *sgc_addr_bss_get() = addr;
  *snapsafety_state_bss_get() = SNAPSAFETY_STATE_SUCCESS_INITIALISE;
}

static uint32_t aws_snapsafe_read_sgn(void) {
  if (*snapsafety_state_bss_get() == SNAPSAFETY_STATE_SUCCESS_INITIALISE) {
    return **sgc_addr_bss_get();
  }

  return 0;
}

int CRYPTO_get_snapsafe_generation(uint32_t *snapsafe_generation_number) {
  CRYPTO_once(aws_snapsafe_init_bss_get(), do_aws_snapsafe_init);

  int state = *snapsafety_state_bss_get();
  switch (state) {
    case SNAPSAFETY_STATE_NOT_SUPPORTED:
      *snapsafe_generation_number = 0;
      return 1;
    case SNAPSAFETY_STATE_SUCCESS_INITIALISE:
      *snapsafe_generation_number = aws_snapsafe_read_sgn();
      return 1;
    case SNAPSAFETY_STATE_FAILED_INITIALISE:
      *snapsafe_generation_number = 0;
      return 0;
    default:
      // No other state should be possible.
      abort();
  }
}

int CRYPTO_get_snapsafe_active(void) {
  CRYPTO_once(aws_snapsafe_init_bss_get(), do_aws_snapsafe_init);

  if (*snapsafety_state_bss_get() == SNAPSAFETY_STATE_SUCCESS_INITIALISE) {
    return 1;
  }

  return 0;
}

int CRYPTO_get_snapsafe_supported(void) {
  CRYPTO_once(aws_snapsafe_init_bss_get(), do_aws_snapsafe_init);

  if (*snapsafety_state_bss_get() == SNAPSAFETY_STATE_NOT_SUPPORTED) {
    return 0;
  }

  return 1;
}

#else  // !defined(OPENSSL_LINUX)

int CRYPTO_get_snapsafe_generation(uint32_t *snapsafe_generation_number) {
  *snapsafe_generation_number = 0;
  return 1;
}

int CRYPTO_get_snapsafe_active(void) { return 0; }

int CRYPTO_get_snapsafe_supported(void) { return 0; }

#endif  // defined(OPENSSL_LINUX)

const char* CRYPTO_get_sysgenid_path(void) {
  return AWSLC_SYSGENID_PATH;
}

#if defined(OPENSSL_LINUX) && defined(AWSLC_SNAPSAFE_TESTING)
int HAZMAT_init_sysgenid_file(void) {
  int fd_sgn = open(CRYPTO_get_sysgenid_path(), O_CREAT | O_RDWR,
                    S_IRWXU | S_IRGRP | S_IROTH);
  if (fd_sgn == -1) {
    return 0;
  }
  // If the file is empty, populate it. Otherwise, no change.
  if (0 == lseek(fd_sgn, 0, SEEK_END)) {
    if (0 != lseek(fd_sgn, 0, SEEK_SET)) {
      close(fd_sgn);
      return 0;
    }
    uint32_t value = 0;
    if (0 >= write(fd_sgn, &value, sizeof(uint32_t))) {
      close(fd_sgn);
      return 0;
    }

    if (0 != fsync(fd_sgn)) {
      close(fd_sgn);
      return 0;
    }
  }

  close(fd_sgn);

  return 1;
}
#endif
