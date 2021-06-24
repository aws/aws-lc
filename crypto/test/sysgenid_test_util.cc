// -----------------------------------------------------------------------------
// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// -----------------------------------------------------------------------------

#include "sysgenid_test_util.h"

#if defined(OPENSSL_LINUX)

#include <stdio.h>

#include "../fipsmodule/rand/snapsafe_detect.h"

#include <fcntl.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <string.h>
#include <unistd.h>

// These values can be found here: https://lkml.org/lkml/2021/3/8/677.
#define SYSGENID_IOCTL                  0xE4
#define SYSGENID_TRIGGER_GEN_UPDATE     _IO(SYSGENID_IOCTL, 3)

static int system_supports_snapsafe = SNAPSAFE_NOT_SUPPORTED;
static uint32_t current_snapsafe_number = 0;

// |set_sysgenid_file_value| interfaces with the SysGenID device. If this is not
// supported on the system we are running, |set_mocked_sysgenid_value|
// that sets the value of a mocked SysGenID device.

static int set_mocked_sysgenid_value(uint32_t new_sysgenid_value) {
  HAZMAT_set_overwritten_sysgenid_for_testing(new_sysgenid_value);
  current_snapsafe_number = new_sysgenid_value;
  return 1;
}

static int increment_real_sysgenid_value() {

  int fd_sysgenid = open(AWSLC_SYSGENID_FILE_PATH, O_RDONLY);
  if (fd_sysgenid == -1) {
    return 0;
  }

  // API details can be found here: https://lkml.org/lkml/2021/3/8/677.
  // Requesting 1 will always increment the SysGenID value by 1.
  if (ioctl(fd_sysgenid, SYSGENID_TRIGGER_GEN_UPDATE, 1) == -1) {
    close(fd_sysgenid);
    return 0;
  }

  if (close(fd_sysgenid) == -1) {
    return 0;
  }

  return 1;
}

int set_new_sysgenid_value(uint32_t new_sysgenid_value) {
  if (system_supports_snapsafe == SNAPSAFE_SUPPORTED) {
    return increment_real_sysgenid_value();
  }
  else {
    return set_mocked_sysgenid_value(new_sysgenid_value);
  }
}

int increment_sysgenid_value(void) {
  if (system_supports_snapsafe == SNAPSAFE_SUPPORTED) {
    return increment_real_sysgenid_value();
  }
  else {
    current_snapsafe_number = current_snapsafe_number + 1;
    return set_mocked_sysgenid_value(current_snapsafe_number);
  }
}

int setup_sysgenid_support(int preference) {
  struct stat buf;
  // System should support Snapsafe if |AWSLC_SYSGENID_FILE_PATH| is present.
  if (preference != MUST_BE_MOCKED &&
      stat(AWSLC_SYSGENID_FILE_PATH, &buf) == 0) {
    system_supports_snapsafe = SNAPSAFE_SUPPORTED;
    return 1;
  }
  else {
    system_supports_snapsafe = SNAPSAFE_NOT_SUPPORTED;

    // Overwrite the SysGenID mmapped callback to memory we control.
    return HAZMAT_overwrite_sysgenid_for_testing();
  }
}

void maybe_cleanup(void) {
  if (system_supports_snapsafe == SNAPSAFE_NOT_SUPPORTED) {
    HAZMAT_reset_sysgenid_for_testing();
  }
}

#endif // defined(OPENSSL_LINUX)
