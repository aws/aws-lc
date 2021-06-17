// -----------------------------------------------------------------------------
// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// -----------------------------------------------------------------------------

#include <openssl/base.h>

#if defined(OPENSSL_LINUX)

#include "snapsafe_detect.h"

#include <fcntl.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <string.h>
#include <unistd.h>

#include <gtest/gtest.h>

// These values can be found here: https://lkml.org/lkml/2021/3/8/677.
#define SYSGENID_IOCTL                  0xE4
#define SYSGENID_TRIGGER_GEN_UPDATE     _IO(SYSGENID_IOCTL, 3)

#define SYSGENID_MOCKED_FILE_PATH "./sysgenid_test_file"
#define NUMBER_OF_TEST_VALUES 5
#define SNAPSAFE_SUPPORTED 0
#define SNAPSAFE_NOT_SUPPORTED 1

// |set_sysgenid_file_value| interfaces with the SysGenID device. If this is not
// supported on the system we are running, we use a backup method to perform
// tests.
// |set_mocked_sysgenid_file_value| writes to a file and mocks the SysGenID
// device.

static int system_supports_snapsafe = SNAPSAFE_NOT_SUPPORTED;

static int set_mocked_sysgenid_file_value(uint32_t new_sysgenid_value) {

  FILE *mocked_sysgenid_file_path = fopen(SYSGENID_MOCKED_FILE_PATH, "wb");
  if (mocked_sysgenid_file_path == NULL) {
    return 0;
  }

  if (fwrite(&new_sysgenid_value, sizeof(uint32_t), 1,
      mocked_sysgenid_file_path) != 1) {
    fclose(mocked_sysgenid_file_path);
    return 0;
  }

  if(fclose(mocked_sysgenid_file_path) == EOF) {
    return 0;
  }

  return 1;
}

static int set_sysgenid_file_value(uint32_t new_sysgenid_value) {

  int fd_sysgenid = open(SYSGENID_FILE_PATH, O_RDONLY);
  if (fd_sysgenid == -1) {
    return 0;
  }

  // Details can be found here: https://lkml.org/lkml/2021/3/8/677.
  if (ioctl(fd_sysgenid, SYSGENID_TRIGGER_GEN_UPDATE,
      new_sysgenid_value) == -1) {
    close(fd_sysgenid);
    return 0;
  }

  if (close(fd_sysgenid) == -1) {
    return 0;
  }

  return 1;
}

static int set_new_sysgenid_value(uint32_t new_sysgenid_value) {
    if (system_supports_snapsafe == SNAPSAFE_SUPPORTED) {
        return set_sysgenid_file_value(new_sysgenid_value);
    }
    else {
        return set_mocked_sysgenid_file_value(new_sysgenid_value);
    }
}

static int check_snapsafe_system_support(void) {
    struct stat buf;
    // System should support Snapsafe if |SYSGENID_FILE_PATH| is present.
    if (stat(SYSGENID_FILE_PATH, &buf) == 0) {
        fprintf(stdout, "System supports Snapsafe\n");
        return SNAPSAFE_SUPPORTED;
    }
    else {
        fprintf(stdout, "System does not support Snapsafe\n");
        return SNAPSAFE_NOT_SUPPORTED;
    }
}

TEST(SnapsafeGenerationTest, Test) {

  // First part of this test suite generates two snapsafe generation numbers and
  // compares them. Since the generation should be stable it is expected the two
  // values are equal.
  // Second part of this test suite This test sets a new SysGenID value
  // (|new_sysgenid_value|), attempts to generate the snapsafe generation
  // number, and compares the new SysGenID value against the generation number
  // (|current_snapsafe_gen_num|). The expectation is that the two values are
  // equal.

  int snapsafe_detection_should_be_ignored = 0; // no

  if (getenv("AWSLC_IGNORE_SNAPSAFE")) {
    snapsafe_detection_should_be_ignored = 1; // yes
    CRYPTO_snapsafe_detect_ignore_for_testing();
  }

  system_supports_snapsafe = check_snapsafe_system_support();
  if (system_supports_snapsafe == SNAPSAFE_NOT_SUPPORTED) {
    char mocked_sysgenid_file_path[] = SYSGENID_MOCKED_FILE_PATH;
    HAZMAT_replace_sysgenid_file_path_for_testing(mocked_sysgenid_file_path);
  }

  // Set initial sysgenid value, such that we can call
  // |CRYPTO_get_snapsafe_generation| below.
  set_new_sysgenid_value(1);

  uint32_t first_gen_num_call = 0;
  const int first_call = CRYPTO_get_snapsafe_generation(&first_gen_num_call);
  if (first_call == 0) {
    // Returning 0 means that snapsafe is not supported. Verify this should
    // indeed be the case.
    EXPECT_EQ(snapsafe_detection_should_be_ignored, 1);
    fprintf(stderr, "Snapsafe tests should be ignored; skipping them.\n");
    return;
  }
  ASSERT_EQ(first_gen_num_call, (uint32_t) 1);

  // The snapsafe generation should be stable.
  uint32_t second_gen_num_call = 0;
  ASSERT_TRUE(CRYPTO_get_snapsafe_generation(&second_gen_num_call));
  ASSERT_EQ(first_gen_num_call, second_gen_num_call);

  uint32_t new_sysgenid_value = 1;
  uint32_t current_snapsafe_gen_num = 0;
  uint32_t test_sysgenid_values[NUMBER_OF_TEST_VALUES] = {
    0x03, // 2^0 + 2
    0x103, // 2^8 + 3
    0x10004, // 2^16 + 4
    0x1000005, // 2^24 + 5
    0xFFFFFFFF // 2^32 - 1
  };

  for (size_t i = 0; i < NUMBER_OF_TEST_VALUES; i++) {
    // Exercise all bytes of the 32-bit generation number.
    new_sysgenid_value = test_sysgenid_values[i];
    ASSERT_TRUE(set_new_sysgenid_value(new_sysgenid_value));
    ASSERT_TRUE(CRYPTO_get_snapsafe_generation(&current_snapsafe_gen_num));
    ASSERT_EQ(new_sysgenid_value, current_snapsafe_gen_num);
  }
}

#endif // defined(OPENSSL_LINUX)
