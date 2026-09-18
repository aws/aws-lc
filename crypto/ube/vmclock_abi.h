// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef HEADER_VMCLOCK_ABI
#define HEADER_VMCLOCK_ABI

#include <openssl/base.h>

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

// This mirrors the Linux kernel's vmclock ABI (struct vmclock_abi in
// include/uapi/linux/vmclock-abi.h). See
// https://uapi-group.org/specifications/specs/vmclock/ for the specification.
//
// The on-device representation is little-endian. We read the fields natively
// (see vm_ube_detect.c), so on a big-endian host the |magic| comparison will
// fail and we fall through to another detection backend. This is intentional:
// we would rather disable vmclock on big-endian than byte-swap an interface we
// cannot exercise there.
//
// The field layout is defined so that every member is naturally aligned; the
// kernel struct is not packed and neither is this. The OPENSSL_STATIC_ASSERTs
// below pin the size and the offsets we actually dereference so that an
// accidental edit to this struct fails the build instead of silently shifting
// |vm_generation_counter|.

#define VMCLOCK_MAGIC 0x4b4c4356 /* "VCLK" */

#define VMCLOCK_FLAG_VM_GEN_COUNTER_PRESENT (1ULL << 8)

struct vmclock_abi {
  /* Constant fields */
  uint32_t magic;
  uint32_t size;
  uint16_t version;
  uint8_t counter_id;
  uint8_t time_type;

  /* Non-constant fields protected by seqcount lock */
  uint32_t seq_count;
  uint64_t disruption_marker;
  uint64_t flags;
  uint8_t pad[2];
  uint8_t clock_status;
  uint8_t leap_second_smearing_hint;
  uint16_t tai_offset_sec;
  uint8_t leap_indicator;
  uint8_t counter_period_shift;
  uint64_t counter_value;
  uint64_t counter_period_frac_sec;
  uint64_t counter_period_esterror_rate_frac_sec;
  uint64_t counter_period_maxerror_rate_frac_sec;
  uint64_t time_sec;
  uint64_t time_frac_sec;
  uint64_t time_esterror_nanosec;
  uint64_t time_maxerror_nanosec;
  uint64_t vm_generation_counter;
};

// Pin the ABI layout. These values come from the kernel's vmclock-abi.h; if a
// change to |struct vmclock_abi| moves any of them, the build must fail.
OPENSSL_STATIC_ASSERT(sizeof(struct vmclock_abi) == 112,
                      vmclock_abi_unexpected_size);
OPENSSL_STATIC_ASSERT(offsetof(struct vmclock_abi, magic) == 0,
                      vmclock_abi_unexpected_magic_offset);
OPENSSL_STATIC_ASSERT(offsetof(struct vmclock_abi, seq_count) == 12,
                      vmclock_abi_unexpected_seq_count_offset);
OPENSSL_STATIC_ASSERT(offsetof(struct vmclock_abi, flags) == 24,
                      vmclock_abi_unexpected_flags_offset);
OPENSSL_STATIC_ASSERT(offsetof(struct vmclock_abi, vm_generation_counter) == 104,
                      vmclock_abi_unexpected_vm_generation_counter_offset);

#ifdef __cplusplus
}
#endif

#endif /* HEADER_VMCLOCK_ABI */
