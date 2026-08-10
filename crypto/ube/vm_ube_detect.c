// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/crypto.h>

#include "vm_ube_detect.h"

#if defined(OPENSSL_LINUX)
#include <fcntl.h>
// This file is compiled only for Linux, where the toolchains we support
// (GCC/Clang) always provide working, lock-free C11 atomics. We use
// <stdatomic.h> directly for the acquire fence in the vmclock seqlock reader
// rather than the tree's |CRYPTO_atomic_*| refcount helpers, which do not
// expose a general-purpose fence.
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include "../internal.h"
#include "vmclock_abi.h"

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

// Result of attempting to initialize a single detection backend.
#define VM_UBE_BACKEND_NOT_PRESENT 0x00   // device file does not exist
#define VM_UBE_BACKEND_INITIALISED 0x01   // device present and usable
#define VM_UBE_BACKEND_UNAVAILABLE 0x02   // device present but not usable by us
                                          // (e.g. EACCES, mmap failure, or the
                                          // device is not a valid vmclock)

// Upper bound on seqlock read retries. The vmclock seqcount only advances
// while the VMM is mid-update, which is momentary, so a handful of retries is
// always sufficient in practice. The bound exists purely so that a wedged or
// corrupt |seq_count| (e.g. one stuck at an odd value) cannot spin this
// function -- and therefore |RAND_bytes| -- forever.
#define VMCLOCK_SEQLOCK_MAX_RETRIES 1024

static CRYPTO_once_t vm_ube_init = CRYPTO_ONCE_INIT;
static int vm_ube_state = 0;
static int vm_ube_backend = VM_UBE_BACKEND_NONE;

// SysGenID generation number pointer
static volatile uint32_t *sgn_addr = NULL;

// vmclock mapped region
static volatile struct vmclock_abi *vmclock_addr = NULL;

// try_vmclock_init attempts to initialize the vmclock backend. It returns one
// of the VM_UBE_BACKEND_* result codes. A non-present device, or a device that
// is present but not usable by this process (open/mmap failure such as EACCES,
// bad magic, or missing generation-counter flag), both leave the caller free to
// try the next backend and ultimately degrade to "not supported".
static int try_vmclock_init(void) {
  struct stat buff;
  if (stat(CRYPTO_get_vmclock_path(), &buff) != 0) {
    return VM_UBE_BACKEND_NOT_PRESENT;
  }

  // The device node exists but may not be usable by this process. A common
  // case is /dev/vmclock0 being root-only (crw-------): an unprivileged process
  // will get EACCES here. That is not an error -- we simply cannot use vmclock,
  // so report it as unavailable and let detection fall through / degrade.
  int fd = open(CRYPTO_get_vmclock_path(), O_RDONLY);
  if (fd == -1) {
    return VM_UBE_BACKEND_UNAVAILABLE;
  }

  void *addr = mmap(NULL, sizeof(struct vmclock_abi), PROT_READ, MAP_SHARED,
                    fd, 0);
  close(fd);

  if (addr == MAP_FAILED) {
    return VM_UBE_BACKEND_UNAVAILABLE;
  }

  volatile struct vmclock_abi *vmc = (volatile struct vmclock_abi *)addr;

  // |magic| is a constant field (never touched by the seqlock), so it is safe
  // to read directly. On a big-endian host this comparison fails and we treat
  // the device as unavailable; see the note in vmclock_abi.h.
  if (vmc->magic != VMCLOCK_MAGIC) {
    munmap(addr, sizeof(struct vmclock_abi));
    return VM_UBE_BACKEND_UNAVAILABLE;
  }

  // |flags| lives in the seqlock-protected region, but this runs once at
  // init from |CRYPTO_once| against a freshly mapped device, so a concurrent
  // VMM update racing this single read is not a concern. Even if |flags| were
  // read torn, the only consequence is mis-detecting the feature bit, which
  // fails closed to the next backend -- never a wrong generation number.
  uint64_t flags = vmc->flags;
  if (!(flags & VMCLOCK_FLAG_VM_GEN_COUNTER_PRESENT)) {
    munmap(addr, sizeof(struct vmclock_abi));
    return VM_UBE_BACKEND_UNAVAILABLE;
  }

  vmclock_addr = vmc;
  return VM_UBE_BACKEND_INITIALISED;
}

static int try_sysgenid_init(void) {
  struct stat buff;
  if (stat(CRYPTO_get_sysgenid_path(), &buff) != 0) {
    return VM_UBE_BACKEND_NOT_PRESENT;
  }

  int fd = open(CRYPTO_get_sysgenid_path(), O_RDONLY);
  if (fd == -1) {
    return VM_UBE_BACKEND_UNAVAILABLE;
  }

  void *addr = mmap(NULL, sizeof(uint32_t), PROT_READ, MAP_SHARED, fd, 0);
  close(fd);

  if (addr == MAP_FAILED) {
    return VM_UBE_BACKEND_UNAVAILABLE;
  }

  sgn_addr = addr;
  return VM_UBE_BACKEND_INITIALISED;
}

static void do_vm_ube_init(void) {
  vm_ube_state = VM_UBE_STATE_NOT_SUPPORTED;
  vm_ube_backend = VM_UBE_BACKEND_NONE;
  sgn_addr = NULL;
  vmclock_addr = NULL;

  // Try vmclock first (preferred). Crucially, if vmclock is present but not
  // usable by us -- e.g. |open|/|mmap| fails (EACCES on a root-only device),
  // or the VMM exposes the device without the generation-counter flag -- we
  // must still fall through to sysgenid. On a host that carries both devices
  // during the sysgenid -> vmclock transition, letting a vmclock hiccup disable
  // detection outright would silently drop UBE reseeding, which is the whole
  // reason this code exists.
  if (try_vmclock_init() == VM_UBE_BACKEND_INITIALISED) {
    vm_ube_backend = VM_UBE_BACKEND_VMCLOCK;
    vm_ube_state = VM_UBE_STATE_SUCCESS_INITIALISE;
    return;
  }

  if (try_sysgenid_init() == VM_UBE_BACKEND_INITIALISED) {
    vm_ube_backend = VM_UBE_BACKEND_SYSGENID;
    vm_ube_state = VM_UBE_STATE_SUCCESS_INITIALISE;
    return;
  }

  // No backend initialized. Whether a device was entirely absent
  // (NOT_PRESENT) or was present but not usable by this process (UNAVAILABLE),
  // VM UBE detection is simply not available here -- degrade to "not
  // supported". This is intentionally NOT a hard failure: a hard failure
  // propagates up through ube.c and disables *all* UBE detection (including the
  // independent fork detection) and forces the DRBG to reseed on every request.
  // A common trigger is an unprivileged process on a host where /dev/vmclock0
  // is root-only; that process must still get fork detection and normal reseed
  // behaviour.
  vm_ube_state = VM_UBE_STATE_NOT_SUPPORTED;
}

#if defined(AWSLC_VM_UBE_TESTING)
// HAZMAT_reinit_vm_ube_FOR_TESTING re-runs backend initialization against the
// current on-disk state of the stand-in device file(s). It exists so tests can
// observe |do_vm_ube_init|'s behaviour for a device that is present but not
// usable at init time (e.g. corrupt contents or EACCES) -- something the normal
// once-per-process |CRYPTO_once| path, already completed against a valid file,
// cannot exercise. It must only be called from a single-threaded test context.
void HAZMAT_reinit_vm_ube_FOR_TESTING(void) {
  if (vmclock_addr != NULL) {
    munmap((void *)vmclock_addr, sizeof(struct vmclock_abi));
    vmclock_addr = NULL;
  }
  if (sgn_addr != NULL) {
    munmap((void *)sgn_addr, sizeof(uint32_t));
    sgn_addr = NULL;
  }
  do_vm_ube_init();
}
#endif

// vm_ube_read_vmclock_gn reads the vmclock generation counter using the
// seqlock protocol described in the vmclock specification. On success it writes
// the value to |*out| and returns 1. It returns 0 if it cannot obtain a
// consistent read within |VMCLOCK_SEQLOCK_MAX_RETRIES| attempts.
static int vm_ube_read_vmclock_gn(uint64_t *out) {
  for (size_t i = 0; i < VMCLOCK_SEQLOCK_MAX_RETRIES; i++) {
    uint32_t seq = vmclock_addr->seq_count & ~1u;
    // Acquire fence pairs with the VMM's release fence: it ensures the
    // |seq_count| read is not reordered after the |vm_generation_counter| read.
    atomic_thread_fence(memory_order_acquire);

    uint64_t value = vmclock_addr->vm_generation_counter;

    // Acquire fence ensures the second |seq_count| read is not reordered before
    // the |vm_generation_counter| read.
    atomic_thread_fence(memory_order_acquire);
    if (seq == vmclock_addr->seq_count) {
      *out = value;
      return 1;
    }
  }
  return 0;
}

static int vm_ube_read_sysgenid_gn(uint64_t *out) {
  *out = (uint64_t)*sgn_addr;
  return 1;
}

// vm_ube_read_generation reads the active backend's generation number into
// |*out|. Returns 1 on success and 0 on failure.
static int vm_ube_read_generation(uint64_t *out) {
  if (vm_ube_backend == VM_UBE_BACKEND_VMCLOCK) {
    return vm_ube_read_vmclock_gn(out);
  }
  if (vm_ube_backend == VM_UBE_BACKEND_SYSGENID) {
    return vm_ube_read_sysgenid_gn(out);
  }
  return 0;
}

int CRYPTO_get_vm_ube_generation(uint64_t *vm_ube_generation_number) {
  CRYPTO_once(&vm_ube_init, do_vm_ube_init);

  switch (vm_ube_state) {
    case VM_UBE_STATE_NOT_SUPPORTED:
      *vm_ube_generation_number = 0;
      return 1;
    case VM_UBE_STATE_SUCCESS_INITIALISE:
      if (vm_ube_read_generation(vm_ube_generation_number) != 1) {
        // A backend that initialized successfully but now cannot produce a
        // consistent read (e.g. a wedged vmclock seqlock) is treated as a
        // failure so the caller reseeds conservatively rather than trusting a
        // stale or torn value.
        *vm_ube_generation_number = 0;
        return 0;
      }
      return 1;
    default:
      abort();
  }
}

int CRYPTO_get_vm_ube_active(void) {
  CRYPTO_once(&vm_ube_init, do_vm_ube_init);

  if (vm_ube_state == VM_UBE_STATE_SUCCESS_INITIALISE) {
    return 1;
  }

  return 0;
}

int CRYPTO_get_vm_ube_supported(void) {
  CRYPTO_once(&vm_ube_init, do_vm_ube_init);

  if (vm_ube_state == VM_UBE_STATE_NOT_SUPPORTED) {
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

  if (0 != lseek(fd, 0, SEEK_SET)) {
    close(fd);
    return 0;
  }

  // Always write a valid vmclock structure at the start of the file.
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
