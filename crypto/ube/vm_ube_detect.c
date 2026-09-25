// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/crypto.h>

#include "vm_ube_detect.h"

#if defined(OPENSSL_LINUX)
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include "../internal.h"
#include "vmclock_abi.h"

// Acquire barrier for the vmclock seqlock reader. C11 <stdatomic.h> isn't always
// available (the legacy gcc 4.1 build predates it), so mirror the tree's C11
// gating (crypto/internal.h) and fall back to __sync_synchronize -- a full
// barrier, stronger than the acquire we need, so always correct.
#if !defined(__STDC_NO_ATOMICS__) && defined(__STDC_VERSION__) && \
    __STDC_VERSION__ >= 201112L
#include <stdatomic.h>
static void vm_ube_acquire_fence(void) {
  atomic_thread_fence(memory_order_acquire);
}
#else
static void vm_ube_acquire_fence(void) {
  __sync_synchronize();
}
#endif

// VM UBE state. A backend either initializes successfully or VM UBE detection
// is unavailable ("not supported"). There is deliberately no hard-failure
// state: an inaccessible or invalid device degrades to NOT_SUPPORTED so that
// the independent fork detection in ube.c keeps working (see do_vm_ube_init).
#define VM_UBE_STATE_SUCCESS_INITIALISE 0x01
#define VM_UBE_STATE_NOT_SUPPORTED 0x02

// VM UBE backend type
#define VM_UBE_BACKEND_NONE 0x00
#define VM_UBE_BACKEND_VMCLOCK 0x01
#define VM_UBE_BACKEND_SYSGENID 0x02

// Iteration budget for a contended or wedged seqlock, not a guarantee a VMM
// update completes. Exhausting it reports a transient read failure (see
// vm_ube_read_vmclock_gn) so a stuck |seq_count| can't spin |RAND_bytes|
// forever.
#define VMCLOCK_SEQLOCK_MAX_RETRIES 1024

static CRYPTO_once_t vm_ube_init = CRYPTO_ONCE_INIT;

// vm_ube_state_st holds all VM UBE detection state. Exactly one instance
// (|vm_ube|) exists; |do_vm_ube_init| populates it once via |CRYPTO_once| and
// it is read-only thereafter.
struct vm_ube_state_st {
  int state;                                  // VM_UBE_STATE_*
  int backend;                                // VM_UBE_BACKEND_*
  volatile uint32_t *sysgenid_addr;           // SysGenID counter mapping
  volatile struct vmclock_abi *vmclock_addr;  // vmclock region mapping
};
static struct vm_ube_state_st vm_ube = {
    VM_UBE_STATE_NOT_SUPPORTED, VM_UBE_BACKEND_NONE, NULL, NULL,
};

// try_vmclock_init attempts to initialize the vmclock backend into |st|. It
// returns 1 on success and 0 otherwise. All failure modes are equivalent to the
// caller (fall through to the next backend), so they are not distinguished: an
// absent device (|open| ENOENT), a device present but not usable by this
// process (|open| EACCES on a root-only node, |mmap| failure), and a device
// that is not a valid vmclock (bad magic, or the generation-counter flag unset)
// all return 0.
static int try_vmclock_init(struct vm_ube_state_st *st) {
  int fd = open(CRYPTO_get_vmclock_path(), O_RDONLY);
  if (fd == -1) {
    return 0;
  }

  void *addr = mmap(NULL, sizeof(struct vmclock_abi), PROT_READ, MAP_SHARED,
                    fd, 0);
  close(fd);

  if (addr == MAP_FAILED) {
    return 0;
  }

  volatile struct vmclock_abi *vmc = (volatile struct vmclock_abi *)addr;

  // |magic| is constant (never touched by the seqlock), so read it directly.
  // On big-endian this comparison fails and we treat the device as unavailable
  // (see vmclock_abi.h).
  if (vmc->magic != VMCLOCK_MAGIC) {
    munmap(addr, sizeof(struct vmclock_abi));
    return 0;
  }

  // |flags| is seqlock-protected, but this runs once at init against a freshly
  // mapped device. A torn read would at worst mis-detect the feature bit and
  // fall through to the next backend -- never a wrong generation number.
  uint64_t flags = vmc->flags;
  if (!(flags & VMCLOCK_FLAG_VM_GEN_COUNTER_PRESENT)) {
    munmap(addr, sizeof(struct vmclock_abi));
    return 0;
  }

  st->vmclock_addr = vmc;
  return 1;
}

// try_sysgenid_init attempts to initialize the SysGenID backend into |st|.
// Returns 1 on success and 0 otherwise (absent, or present but unusable). Like
// vmclock, the failure modes are not distinguished -- see |do_vm_ube_init| for
// why an unusable device degrades rather than forcing a per-call reseed.
static int try_sysgenid_init(struct vm_ube_state_st *st) {
  int fd = open(CRYPTO_get_sysgenid_path(), O_RDONLY);
  if (fd == -1) {
    return 0;
  }

  void *addr = mmap(NULL, sizeof(uint32_t), PROT_READ, MAP_SHARED, fd, 0);
  close(fd);

  if (addr == MAP_FAILED) {
    return 0;
  }

  st->sysgenid_addr = addr;
  return 1;
}

// VM UBE detection is a *non-required* detector: unlike fork detection, its
// unavailability must not force a reseed on every RAND_bytes call (VM devices
// are often absent, e.g. sysgenid is Lambda-specific). So any device that is
// absent or present-but-unusable degrades to NOT_SUPPORTED -- there is no
// "present but failed" state that reports permanent failure up the stack. That
// keeps the required fork detector working and avoids the per-call reseed tax
// for what is usually just a permissions issue on a root-only device.
static void do_vm_ube_init(void) {
  vm_ube.state = VM_UBE_STATE_NOT_SUPPORTED;
  vm_ube.backend = VM_UBE_BACKEND_NONE;
  vm_ube.sysgenid_addr = NULL;
  vm_ube.vmclock_addr = NULL;

  // Try vmclock first (preferred). If it is present but unusable, fall through
  // to sysgenid rather than giving up -- both can coexist during the transition.
  if (try_vmclock_init(&vm_ube)) {
    vm_ube.backend = VM_UBE_BACKEND_VMCLOCK;
    vm_ube.state = VM_UBE_STATE_SUCCESS_INITIALISE;
    return;
  }

  if (try_sysgenid_init(&vm_ube)) {
    vm_ube.backend = VM_UBE_BACKEND_SYSGENID;
    vm_ube.state = VM_UBE_STATE_SUCCESS_INITIALISE;
    return;
  }

  // No backend initialized -- degrade to "not supported" (see note above).
  vm_ube.state = VM_UBE_STATE_NOT_SUPPORTED;
}

#if defined(AWSLC_VM_UBE_TESTING)
// See vm_ube_detect.h. Re-runs init against the current stand-in file(s);
// single-threaded test use only.
void HAZMAT_reinit_vm_ube_FOR_TESTING(void) {
  if (vm_ube.vmclock_addr != NULL) {
    munmap((void *)vm_ube.vmclock_addr, sizeof(struct vmclock_abi));
    vm_ube.vmclock_addr = NULL;
  }
  if (vm_ube.sysgenid_addr != NULL) {
    munmap((void *)vm_ube.sysgenid_addr, sizeof(uint32_t));
    vm_ube.sysgenid_addr = NULL;
  }
  do_vm_ube_init();
}
#endif

// vm_ube_read_vmclock_gn reads the vmclock generation counter using the
// seqlock protocol described in the vmclock specification. On success it writes
// the value to |*out| and returns 1. It returns 0 if it cannot obtain a
// consistent read within |VMCLOCK_SEQLOCK_MAX_RETRIES| attempts.
static int vm_ube_read_vmclock_gn(const struct vm_ube_state_st *st,
                                  uint64_t *out) {
  for (size_t i = 0; i < VMCLOCK_SEQLOCK_MAX_RETRIES; i++) {
    uint32_t seq = st->vmclock_addr->seq_count & ~1u;
    // Keep the first |seq_count| read ordered before the counter read.
    vm_ube_acquire_fence();

    uint64_t value = st->vmclock_addr->vm_generation_counter;

    // Keep the second |seq_count| read ordered after the counter read.
    vm_ube_acquire_fence();
    if (seq == st->vmclock_addr->seq_count) {
      *out = value;
      return 1;
    }
  }
  return 0;
}

static int vm_ube_read_sysgenid_gn(const struct vm_ube_state_st *st,
                                   uint64_t *out) {
  *out = (uint64_t)*st->sysgenid_addr;
  return 1;
}

// vm_ube_read_generation reads |st|'s active backend generation number into
// |*out|. Returns 1 on success and 0 on failure.
static int vm_ube_read_generation(const struct vm_ube_state_st *st,
                                  uint64_t *out) {
  if (st->backend == VM_UBE_BACKEND_VMCLOCK) {
    return vm_ube_read_vmclock_gn(st, out);
  }
  if (st->backend == VM_UBE_BACKEND_SYSGENID) {
    return vm_ube_read_sysgenid_gn(st, out);
  }
  return 0;
}

// Bit 63 marks a synthesized "transient failure" generation number. A real
// counter increments slowly per snapshot and never reaches 2^63, so a poison
// value never collides with a genuine one.
#define VM_UBE_TRANSIENT_POISON_BIT (UINT64_C(1) << 63)

// vm_ube_transient_poison returns a distinct poison value on each call (a
// monotonic counter with bit 63 set), so it differs from any real counter and
// from the previous poison. This drives the UBE layer's normal "changed" path
// (a conservative reseed) without a dedicated failure state. Atomic, gated for
// gcc 4.1 like the fence above.
#if !defined(__STDC_NO_ATOMICS__) && defined(__STDC_VERSION__) && \
    __STDC_VERSION__ >= 201112L
static uint64_t vm_ube_transient_poison(void) {
  static _Atomic uint64_t transient_seq;
  uint64_t n = atomic_fetch_add(&transient_seq, 1) + 1;
  return VM_UBE_TRANSIENT_POISON_BIT | n;
}
#else
static uint64_t vm_ube_transient_poison(void) {
  static uint64_t transient_seq;
  uint64_t n = (uint64_t)__sync_add_and_fetch(&transient_seq, 1);
  return VM_UBE_TRANSIENT_POISON_BIT | n;
}
#endif

int CRYPTO_get_vm_ube_generation(uint64_t *vm_ube_generation_number) {
  CRYPTO_once(&vm_ube_init, do_vm_ube_init);

  switch (vm_ube.state) {
    case VM_UBE_STATE_NOT_SUPPORTED:
      *vm_ube_generation_number = 0;
      return 1;
    case VM_UBE_STATE_SUCCESS_INITIALISE:
      if (vm_ube_read_generation(&vm_ube, vm_ube_generation_number) != 1) {
        // Initialized but no consistent read this call (e.g. a wedged seqlock):
        // a transient failure. Hand back a poison value so the UBE layer reseeds
        // conservatively; detection recovers on the next consistent read.
        *vm_ube_generation_number = vm_ube_transient_poison();
        return 1;
      }
      return 1;
    default:
      abort();
  }
}

int CRYPTO_get_vm_ube_active(void) {
  CRYPTO_once(&vm_ube_init, do_vm_ube_init);

  if (vm_ube.state == VM_UBE_STATE_SUCCESS_INITIALISE) {
    return 1;
  }

  return 0;
}

int CRYPTO_get_vm_ube_supported(void) {
  CRYPTO_once(&vm_ube_init, do_vm_ube_init);

  if (vm_ube.state == VM_UBE_STATE_NOT_SUPPORTED) {
    return 0;
  }

  return 1;
}

#else  // !defined(OPENSSL_LINUX)

int CRYPTO_get_vm_ube_generation(uint64_t *vm_ube_generation_number) {
  *vm_ube_generation_number = 0;
  return 1;
}

int CRYPTO_get_vm_ube_active(void) { return 0; }

int CRYPTO_get_vm_ube_supported(void) { return 0; }

#endif  // defined(OPENSSL_LINUX)

const char* CRYPTO_get_sysgenid_path(void) {
  return AWSLC_SYSGENID_PATH;
}

const char* CRYPTO_get_vmclock_path(void) {
  return AWSLC_VMCLOCK_PATH;
}

#if defined(OPENSSL_LINUX) && defined(AWSLC_TEST_SYSGENID)
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

#if defined(OPENSSL_LINUX) && defined(AWSLC_TEST_VMCLOCK)
int HAZMAT_init_vmclock_file(void) {
  int fd = open(CRYPTO_get_vmclock_path(), O_CREAT | O_RDWR,
                S_IRWXU | S_IRGRP | S_IROTH);
  if (fd == -1) {
    return 0;
  }

  // Initialize only if the file has no valid vmclock yet (magic unset); leave it
  // otherwise. Concurrent crypto_test processes share this stand-in file, so
  // rewriting it would reset |vm_generation_counter| mid-test in another
  // process. (sysgenid keys off an empty file instead, but CI dd-fills this one,
  // so vmclock keys off magic.)
  uint32_t existing_magic = 0;
  if ((ssize_t)sizeof(existing_magic) ==
          read(fd, &existing_magic, sizeof(existing_magic)) &&
      existing_magic == VMCLOCK_MAGIC) {
    close(fd);
    return 1;
  }

  if (0 != lseek(fd, 0, SEEK_SET)) {
    close(fd);
    return 0;
  }

  struct vmclock_abi vmc;
  memset(&vmc, 0, sizeof(vmc));
  vmc.magic = VMCLOCK_MAGIC;
  vmc.size = sizeof(struct vmclock_abi);
  vmc.version = 1;
  vmc.flags = VMCLOCK_FLAG_VM_GEN_COUNTER_PRESENT;
  vmc.seq_count = 0;
  vmc.vm_generation_counter = 0;

  if ((ssize_t)sizeof(vmc) != write(fd, &vmc, sizeof(vmc))) {
    close(fd);
    return 0;
  }

  if (0 != fsync(fd)) {
    close(fd);
    return 0;
  }

  close(fd);

  return 1;
}
#endif
