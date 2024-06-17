// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <cstdint>

#include <gtest/gtest.h>
#include "snapsafe_detect.h"

#if defined(OPENSSL_LINUX) && defined(AWSLC_SNAPSAFE_TESTING)
#include <fcntl.h>
#include <cstring>
#include <sys/mman.h>

#define NUMBER_OF_TEST_VALUES 5

typedef struct sgn_test_s {
  void* addr;
  size_t pgsize;
} sgn_test_s;

int init_sgn_file(sgn_test_s* sgn_test);
int init_sgn_file(sgn_test_s* sgn_test) {
  const char* sgc_file_path = AWSLC_SYSGENID_PATH;
  int fd_sgn = open(sgc_file_path, O_CREAT | O_RDWR | O_APPEND, (mode_t)0600);
  if (fd_sgn == -1) {
    return 0;
  }
  if (0 != lseek(fd_sgn, 0, SEEK_SET)) {
    return 0;
  }
  
  unsigned int set_sgn = 0;
  if(0 >= write(fd_sgn, &set_sgn, sizeof(unsigned int))) {
    return 0;
  }
  long page_size = sysconf(_SC_PAGESIZE);
  if (page_size <= 0) {
    return 0;
  }
  size_t pgsize = (size_t)page_size;

  void* addr = mmap(NULL, pgsize, PROT_WRITE, MAP_SHARED, fd_sgn, 0);
  if (addr == MAP_FAILED) {
    return 0;
  }

  close(fd_sgn);

  sgn_test->addr = addr;
  sgn_test->pgsize = pgsize;

  return 1;  
}

int set_sgn(const sgn_test_s* sgn_test, unsigned int val);
int set_sgn(const sgn_test_s* sgn_test, unsigned int val) {
  memcpy(sgn_test->addr, &val, sizeof(unsigned int));
  if(0 != msync(sgn_test->addr, sgn_test->pgsize, MS_SYNC)) {
    return 0;
  }
  return 1;
}

TEST(SnapsafeGenerationTest, SysGenIDretrievalTesting) {
  sgn_test_s sgn_test;
  if(1 != init_sgn_file(&sgn_test)) {
    FAIL();
  }

  if(1 != set_sgn(&sgn_test, 0)) {
    FAIL();
  }

  ASSERT_TRUE(CRYPTO_get_snapsafe_supported());
  ASSERT_TRUE(CRYPTO_get_snapsafe_active());

  unsigned int current_snapsafe_gen_num = 0;
  ASSERT_TRUE(set_sgn(&sgn_test, 7));
  ASSERT_TRUE(CRYPTO_get_snapsafe_generation(&current_snapsafe_gen_num));
  ASSERT_EQ((unsigned int)7, current_snapsafe_gen_num);

  uint32_t test_sysgenid_values[NUMBER_OF_TEST_VALUES] = {
    0x03, // 2^0 + 2
    0x103, // 2^8 + 3
    0x10004, // 2^16 + 4
    0x1000005, // 2^24 + 5
    0xFFFFFFFF // 2^32 - 1
  };

  for (size_t i = 0; i < NUMBER_OF_TEST_VALUES; i++) {
    // Exercise all bytes of the 32-bit generation number.
    unsigned int new_sysgenid_value_hint = test_sysgenid_values[i];
    ASSERT_TRUE(set_sgn(&sgn_test, new_sysgenid_value_hint));
    ASSERT_TRUE(CRYPTO_get_snapsafe_generation(&current_snapsafe_gen_num));
    ASSERT_EQ(new_sysgenid_value_hint, current_snapsafe_gen_num);
  }
}
#elif defined(OPENSSL_LINUX)
TEST(SnapsafeGenerationTest, SysGenIDretrievalLinux) {
  unsigned int current_snapsafe_gen_num = 0xffffffff;
  ASSERT_TRUE(CRYPTO_get_snapsafe_generation(&current_snapsafe_gen_num));
  if(CRYPTO_get_snapsafe_supported()) {
    ASSERT_TRUE(CRYPTO_get_snapsafe_active());
    // If we're on a system possible where the SysGenId is available, we won't
    // know what sgn value to expect, but we assume it's not 0xffffffff
    ASSERT_NE(0xffffffff, current_snapsafe_gen_num);
  } else {
    ASSERT_FALSE(CRYPTO_get_snapsafe_active());
    ASSERT_EQ((unsigned int)0, current_snapsafe_gen_num);
  }
}
#else
TEST(SnapsafeGenerationTest, SysGenIDretrievalNonLinux) {
  ASSERT_FALSE(CRYPTO_get_snapsafe_supported());
  ASSERT_FALSE(CRYPTO_get_snapsafe_active());
  unsigned int current_snapsafe_gen_num = 0xffffffff;
  ASSERT_TRUE(CRYPTO_get_snapsafe_generation(&current_snapsafe_gen_num));
  ASSERT_EQ((unsigned int)0, current_snapsafe_gen_num);
}
#endif // defined(OPENSSL_LINUX)
