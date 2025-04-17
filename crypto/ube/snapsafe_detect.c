// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/crypto.h>

#include "snapsafe_detect.h"

#if defined(OPENSSL_LINUX)
#include <fcntl.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include "../internal.h"

// Snapsafety state
#define SNAPSAFETY_STATE_FAILED_INITIALISE 0x00
#define SNAPSAFETY_STATE_SUCCESS_INITIALISE 0x01
#define SNAPSAFETY_STATE_NOT_SUPPORTED 0x02

static CRYPTO_once_t aws_snapsafe_init = CRYPTO_ONCE_INIT;

static volatile uint32_t *sgn_addr = NULL;
static int snapsafety_state = 0;


static void do_aws_snapsafe_init(void) {
  snapsafety_state = SNAPSAFETY_STATE_NOT_SUPPORTED;
  sgn_addr = NULL;

  struct stat buff;
  if (stat(CRYPTO_get_sysgenid_path(), &buff) != 0) {
    return;
  }
  
  snapsafety_state = SNAPSAFETY_STATE_FAILED_INITIALISE;

  int fd_sgn = open(CRYPTO_get_sysgenid_path(), O_RDONLY);
  if (fd_sgn == -1) {
    return;
  }

  void *addr = mmap(NULL, sizeof(uint32_t), PROT_READ, MAP_SHARED, fd_sgn, 0);

  // Can close file descriptor now per
  // https://man7.org/linux/man-pages/man2/mmap.2.html: "After the mmap() call
  // has returned, the file descriptor, fd, can be closed immediately without
  // invalidating the mapping.". We have initialised snapsafety without errors
  // and this function is only executed once. Therefore, try to close file
  // descriptor but don't error if it fails. */
  close(fd_sgn);

  if (addr == MAP_FAILED) {
    return;
  }

  // sgn_addr will now point at the mapped memory and any 4-byte read from
  // this pointer will correspond to the sgn managed by the VMM.
  sgn_addr = addr;
  snapsafety_state = SNAPSAFETY_STATE_SUCCESS_INITIALISE;
}

static uint32_t aws_snapsafe_read_sgn(void) {
  if (snapsafety_state == SNAPSAFETY_STATE_SUCCESS_INITIALISE) {
    return *sgn_addr;
  }

  return 0;
}

int CRYPTO_get_snapsafe_generation(uint32_t *snapsafe_generation_number) {
  CRYPTO_once(&aws_snapsafe_init, do_aws_snapsafe_init);

  switch (snapsafety_state) {
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
  CRYPTO_once(&aws_snapsafe_init, do_aws_snapsafe_init);

  if (snapsafety_state == SNAPSAFETY_STATE_SUCCESS_INITIALISE) {
    return 1;
  }

  return 0;
}

int CRYPTO_get_snapsafe_supported(void) {
  CRYPTO_once(&aws_snapsafe_init, do_aws_snapsafe_init);

  if (snapsafety_state == SNAPSAFETY_STATE_NOT_SUPPORTED) {
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
