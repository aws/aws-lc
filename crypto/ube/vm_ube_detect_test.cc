// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <cstdint>

#include <gtest/gtest.h>
#include "vm_ube_detect.h"

#if defined(OPENSSL_LINUX) && defined(AWSLC_VM_UBE_TESTING)
#include <fcntl.h>
#include <cstring>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <atomic>
#include <thread>

#include "vmclock_abi.h"

#define NUMBER_OF_TEST_VALUES 5

#if defined(AWSLC_TEST_SYSGENID)
// Test helper for sysgenid backend
typedef struct sgn_test_s {
  void *addr;
} sgn_test_s;

static int init_sgn_file(void** addr);
static int init_sgn_file(void** addr) {
  *addr = nullptr;

  // This file should've been created during test initialization
  const int fd_sgn = open(CRYPTO_get_sysgenid_path(), O_RDWR);
  if (fd_sgn == -1) {
    return 0;
  }

  if (0 != lseek(fd_sgn, 0, SEEK_SET)) {
    close(fd_sgn);
    return 0;
  }

  void* my_addr = mmap(nullptr, sizeof(uint32_t), PROT_WRITE, MAP_SHARED, fd_sgn, 0);
  if (my_addr == MAP_FAILED) {
    close(fd_sgn);
    return 0;
  }

  close(fd_sgn);

  *addr = my_addr;

  return 1;
}

static int init_sgn_test(sgn_test_s* sgn_test);
static int init_sgn_test(sgn_test_s* sgn_test) {
  return init_sgn_file(&sgn_test->addr);
}

static int set_sgn(const sgn_test_s* sgn_test, uint32_t val);
static int set_sgn(const sgn_test_s* sgn_test, uint32_t val) {
  memcpy(sgn_test->addr, &val, sizeof(uint32_t));
  if(0 != msync(sgn_test->addr, sizeof(uint32_t), MS_SYNC)) {
    return 0;
  }
  return 1;
}
#endif  // defined(AWSLC_TEST_SYSGENID)

#if defined(AWSLC_TEST_VMCLOCK)
// Test helper for vmclock backend
typedef struct vmclock_test_s {
  struct vmclock_abi *addr;
} vmclock_test_s;

static int init_vmclock_test(vmclock_test_s* vmc_test) {
  const int fd = open(CRYPTO_get_vmclock_path(), O_RDWR);
  if (fd == -1) {
    return 0;
  }

  void* addr = mmap(nullptr, sizeof(struct vmclock_abi), PROT_WRITE | PROT_READ,
                    MAP_SHARED, fd, 0);
  close(fd);

  if (addr == MAP_FAILED) {
    return 0;
  }

  vmc_test->addr = static_cast<struct vmclock_abi *>(addr);
  return 1;
}

static int set_vmclock_generation(vmclock_test_s* vmc_test, uint64_t val) {
  // Use seqlock protocol: increment seq_count to odd, write, increment to even
  vmc_test->addr->seq_count++;
  __atomic_thread_fence(__ATOMIC_RELEASE);
  vmc_test->addr->vm_generation_counter = val;
  __atomic_thread_fence(__ATOMIC_RELEASE);
  vmc_test->addr->seq_count++;
  if (0 != msync(vmc_test->addr, sizeof(struct vmclock_abi), MS_SYNC)) {
    return 0;
  }
  return 1;
}

// set_vmclock_seq_count forces |seq_count| to an arbitrary value. A test uses
// this to leave the seqlock "held" (odd value), simulating a VMM that is
// perpetually mid-update or a corrupt mapping.
static int set_vmclock_seq_count(vmclock_test_s* vmc_test, uint32_t seq) {
  vmc_test->addr->seq_count = seq;
  if (0 != msync(vmc_test->addr, sizeof(struct vmclock_abi), MS_SYNC)) {
    return 0;
  }
  return 1;
}

TEST(VmUbeGenerationTest, DISABLED_VmclockRetrievalTesting) {
  vmclock_test_s vmc_test;
  ASSERT_TRUE(init_vmclock_test(&vmc_test));

  EXPECT_EQ(1, CRYPTO_get_vm_ube_supported());
  EXPECT_EQ(1, CRYPTO_get_vm_ube_active());

  uint64_t current_vm_ube_gen_num = 0;
  ASSERT_TRUE(set_vmclock_generation(&vmc_test, 42));
  ASSERT_TRUE(CRYPTO_get_vm_ube_generation(&current_vm_ube_gen_num));
  ASSERT_EQ((uint64_t)42, current_vm_ube_gen_num);

  // Test values that exercise the full 64-bit range
  uint64_t test_vmclock_values[] = {
    0x03,
    0x100000003ULL,        // > 32-bit
    0xFFFFFFFFULL,         // 32-bit max
    0x100000000ULL,        // Just above 32-bit max
    0xFFFFFFFFFFFFFFFFULL  // 64-bit max
  };

  for (size_t i = 0; i < sizeof(test_vmclock_values) / sizeof(test_vmclock_values[0]); i++) {
    ASSERT_TRUE(set_vmclock_generation(&vmc_test, test_vmclock_values[i]));
    ASSERT_TRUE(CRYPTO_get_vm_ube_generation(&current_vm_ube_gen_num));
    EXPECT_EQ(test_vmclock_values[i], current_vm_ube_gen_num);
  }
}

// A wedged seqlock (stuck at an odd value, i.e. a write perpetually "in
// progress") must not spin the reader forever. |CRYPTO_get_vm_ube_generation|
// must give up after a bounded number of retries and report failure (return 0),
// which the DRBG layer treats as "reseed conservatively". Once the seqlock is
// released (even value again), reads must succeed.
TEST(VmUbeGenerationTest, DISABLED_VmclockSeqlockWedged) {
  vmclock_test_s vmc_test;
  ASSERT_TRUE(init_vmclock_test(&vmc_test));

  // Establish a known-good baseline.
  uint64_t gen = 0;
  ASSERT_TRUE(set_vmclock_generation(&vmc_test, 100));
  ASSERT_TRUE(CRYPTO_get_vm_ube_generation(&gen));
  ASSERT_EQ((uint64_t)100, gen);

  // Wedge the seqlock at an odd value. The generation counter underneath is
  // irrelevant; the reader must never observe a consistent seq_count.
  ASSERT_TRUE(set_vmclock_seq_count(&vmc_test, 0x7FFFFFFF));

  // The read must terminate (bounded retries) and report failure rather than
  // hang. This test hanging *is* the failure signal for the unbounded-loop bug.
  gen = 0xdeadbeef;
  ASSERT_EQ(0, CRYPTO_get_vm_ube_generation(&gen));
  ASSERT_EQ((uint64_t)0, gen);

  // Release the seqlock. Reset seq_count to an even value first: the seqlock
  // was left odd (0x7FFFFFFF), and set_vmclock_generation() applies two
  // increments, which from an odd start would land back on odd (still "held").
  ASSERT_TRUE(set_vmclock_seq_count(&vmc_test, 0));
  ASSERT_TRUE(set_vmclock_generation(&vmc_test, 101));
  ASSERT_TRUE(CRYPTO_get_vm_ube_generation(&gen));
  ASSERT_EQ((uint64_t)101, gen);
}

// Hammer the reader while a background thread continuously updates the
// generation counter through the seqlock write protocol, writing the 64-bit
// value in two 32-bit halves so that a naive (non-seqlock) reader could observe
// a torn value. The reader must only ever return one of the two whole values
// that were actually written -- never a mix of their halves -- or fail cleanly.
TEST(VmUbeGenerationTest, DISABLED_VmclockConcurrentTornRead) {
  vmclock_test_s vmc_test;
  ASSERT_TRUE(init_vmclock_test(&vmc_test));

  // Two values whose 32-bit halves are distinct bit patterns. Any torn read
  // that mixes a low half from one write with a high half from the other
  // yields a value equal to neither kValueA nor kValueB (e.g. 0xAAAAAAAA55555555
  // or 0x55555555AAAAAAAA).
  const uint64_t kValueA = 0xAAAAAAAAAAAAAAAAULL;
  const uint64_t kValueB = 0x5555555555555555ULL;

  // Start from a whole value.
  ASSERT_TRUE(set_vmclock_generation(&vmc_test, kValueA));

  std::atomic<bool> stop(false);
  volatile struct vmclock_abi *abi = vmc_test.addr;

  std::thread writer([&]() {
    bool toggle = false;
    while (!stop.load(std::memory_order_relaxed)) {
      uint64_t next = toggle ? kValueA : kValueB;
      toggle = !toggle;

      volatile uint32_t *lo =
          reinterpret_cast<volatile uint32_t *>(&abi->vm_generation_counter);
      volatile uint32_t *hi = lo + 1;

      // Enter the write section: make seq_count odd.
      abi->seq_count++;
      __atomic_thread_fence(__ATOMIC_RELEASE);

      // Write the two halves separately, leaving a window where the 64-bit
      // value is a torn mix of the previous and next values.
      *lo = (uint32_t)(next & 0xFFFFFFFFULL);
      *hi = (uint32_t)(next >> 32);

      __atomic_thread_fence(__ATOMIC_RELEASE);
      // Leave the write section: make seq_count even.
      abi->seq_count++;
    }
  });

  // Read many times. Every successful read must be a whole value; a failed
  // read (0 return) is acceptable (writer happened to keep the lock held past
  // the retry bound) but must never be a torn value. We record any torn read
  // and stop, but must NOT return before join()ing the writer -- letting a
  // std::thread destruct while joinable calls std::terminate() and would mask
  // the real failure.
  // 20k iterations is enough to land in the writer's torn window many times
  // over (the writer flips continuously) while keeping runtime low even on a
  // loaded CI host, where each read may spin up to the seqlock retry bound.
  size_t whole_reads = 0;
  bool torn_read = false;
  uint64_t torn_value = 0;
  for (size_t i = 0; i < 20000 && !torn_read; i++) {
    uint64_t gen = 0;
    if (CRYPTO_get_vm_ube_generation(&gen) == 1) {
      if (gen != kValueA && gen != kValueB) {
        torn_read = true;
        torn_value = gen;
        break;
      }
      whole_reads++;
    }
  }

  stop.store(true, std::memory_order_relaxed);
  writer.join();

  EXPECT_FALSE(torn_read) << "torn read observed: 0x" << std::hex << torn_value;
  // Sanity: we should have gotten at least some consistent reads.
  EXPECT_GT(whole_reads, (size_t)0);

  // Restore a clean, released state for any subsequent readers.
  ASSERT_TRUE(set_vmclock_generation(&vmc_test, kValueA));
}

// Regression test for graceful degradation when the vmclock device is present
// but not a valid vmclock (here: corrupt magic). Initialization must treat the
// backend as unavailable and degrade to "not supported" -- returning success
// with generation 0 -- NOT a hard failure. A hard failure would propagate
// through ube.c and disable all UBE detection (including fork detection) and
// force the DRBG to reseed on every request. This is uid-independent: it does
// not rely on file permissions, so it behaves identically as root or non-root.
TEST(VmUbeGenerationTest, DISABLED_VmclockPresentButInvalidDegradesGracefully) {
  vmclock_test_s vmc_test;
  ASSERT_TRUE(init_vmclock_test(&vmc_test));

  // Corrupt the magic so the device no longer looks like a vmclock.
  const uint32_t kOriginalMagic = vmc_test.addr->magic;
  vmc_test.addr->magic = ~kOriginalMagic;
  ASSERT_EQ(0, msync(vmc_test.addr, sizeof(struct vmclock_abi), MS_SYNC));

  HAZMAT_reinit_vm_ube_FOR_TESTING();

  // Present-but-invalid must degrade to "not supported", not hard failure.
  EXPECT_EQ(0, CRYPTO_get_vm_ube_supported());
  EXPECT_EQ(0, CRYPTO_get_vm_ube_active());

  // The generation query still "succeeds" (returns 1) with generation 0. This
  // is the contract that keeps ube.c from disabling all UBE detection.
  uint64_t gen = 0xdeadbeef;
  EXPECT_EQ(1, CRYPTO_get_vm_ube_generation(&gen));
  EXPECT_EQ((uint64_t)0, gen);

  // Restore a valid device and re-init so later readers see a clean vmclock.
  vmc_test.addr->magic = kOriginalMagic;
  ASSERT_EQ(0, msync(vmc_test.addr, sizeof(struct vmclock_abi), MS_SYNC));
  HAZMAT_reinit_vm_ube_FOR_TESTING();
  EXPECT_EQ(1, CRYPTO_get_vm_ube_supported());
}

// Regression test for the exact production bug: on a host where /dev/vmclock0
// exists but is not readable by the process (e.g. root-only crw-------), an
// unprivileged process must degrade gracefully rather than hard-fail. We
// reproduce the EACCES by removing read permission from the stand-in file.
//
// This only reproduces EACCES for a non-root process: root bypasses file
// permission checks, so the test is skipped when running as root rather than
// producing a misleading result.
TEST(VmUbeGenerationTest, DISABLED_VmclockInaccessibleDegradesGracefully) {
  if (geteuid() == 0) {
    GTEST_SKIP() << "root bypasses file permissions; cannot reproduce EACCES";
  }

  const char *path = CRYPTO_get_vmclock_path();

  // Make the stand-in file unreadable so open(O_RDONLY) fails with EACCES,
  // mirroring a root-only /dev/vmclock0 seen by an unprivileged process.
  ASSERT_EQ(0, chmod(path, 0));

  HAZMAT_reinit_vm_ube_FOR_TESTING();

  // Inaccessible device must degrade to "not supported", not hard failure.
  EXPECT_EQ(0, CRYPTO_get_vm_ube_supported());
  EXPECT_EQ(0, CRYPTO_get_vm_ube_active());
  uint64_t gen = 0xdeadbeef;
  EXPECT_EQ(1, CRYPTO_get_vm_ube_generation(&gen));
  EXPECT_EQ((uint64_t)0, gen);

  // Restore readability and re-init so later readers see a usable vmclock.
  ASSERT_EQ(0, chmod(path, S_IRWXU | S_IRGRP | S_IROTH));
  HAZMAT_reinit_vm_ube_FOR_TESTING();
  EXPECT_EQ(1, CRYPTO_get_vm_ube_supported());
}
#endif  // defined(AWSLC_TEST_VMCLOCK)

#if defined(AWSLC_TEST_SYSGENID)
TEST(VmUbeGenerationTest, DISABLED_SysGenIDretrievalTesting) {
  sgn_test_s sgn_test;
  ASSERT_TRUE(init_sgn_test(&sgn_test));

  ASSERT_TRUE(set_sgn(&sgn_test, 0));

  EXPECT_EQ(1, CRYPTO_get_vm_ube_supported());
  EXPECT_EQ(1, CRYPTO_get_vm_ube_active());

  uint64_t current_vm_ube_gen_num = 0;
  ASSERT_TRUE(set_sgn(&sgn_test, 7));
  ASSERT_TRUE(CRYPTO_get_vm_ube_generation(&current_vm_ube_gen_num));
  ASSERT_EQ((uint64_t) 7, current_vm_ube_gen_num);

  uint32_t test_sysgenid_values[NUMBER_OF_TEST_VALUES] = {
    0x03, // 2^0 + 2
    0x103, // 2^8 + 3
    0x10004, // 2^16 + 4
    0x1000005, // 2^24 + 5
    0xFFFFFFFF // 2^32 - 1
  };

  for (size_t i = 0; i < NUMBER_OF_TEST_VALUES; i++) {
    uint32_t new_sysgenid_value_hint = test_sysgenid_values[i];
    ASSERT_TRUE(set_sgn(&sgn_test, new_sysgenid_value_hint));
    ASSERT_TRUE(CRYPTO_get_vm_ube_generation(&current_vm_ube_gen_num));
    EXPECT_EQ((uint64_t)new_sysgenid_value_hint, current_vm_ube_gen_num);
  }
}
#endif  // defined(AWSLC_TEST_SYSGENID)

#elif defined(OPENSSL_LINUX)
TEST(VmUbeGenerationTest, SysGenIDretrievalLinux) {
  uint64_t current_vm_ube_gen_num = 0xffffffffffffffff;
  ASSERT_TRUE(CRYPTO_get_vm_ube_generation(&current_vm_ube_gen_num));
  if (CRYPTO_get_vm_ube_supported()) {
    ASSERT_TRUE(CRYPTO_get_vm_ube_active());
    // If we're on a system where a VM UBE interface is available, we won't
    // know what value to expect, but we assume it's not 0xffffffffffffffff
    ASSERT_NE((uint64_t)0xffffffffffffffff, current_vm_ube_gen_num);
  } else {
    ASSERT_FALSE(CRYPTO_get_vm_ube_active());
    ASSERT_EQ((uint64_t) 0, current_vm_ube_gen_num);
  }
}
#else
TEST(VmUbeGenerationTest, SysGenIDretrievalNonLinux) {
  ASSERT_FALSE(CRYPTO_get_vm_ube_supported());
  ASSERT_FALSE(CRYPTO_get_vm_ube_active());
  uint64_t current_vm_ube_gen_num = 0xffffffffffffffff;
  ASSERT_TRUE(CRYPTO_get_vm_ube_generation(&current_vm_ube_gen_num));
  ASSERT_EQ((uint64_t) 0, current_vm_ube_gen_num);
}
#endif // defined(OPENSSL_LINUX)
