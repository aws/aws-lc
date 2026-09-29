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

// Mirrors the Linux kernel's struct vmclock_abi
// (include/uapi/linux/vmclock-abi.h). Spec:
// https://uapi-group.org/specifications/specs/vmclock/
//
// The layout is little-endian and read natively, so vmclock is disabled at
// compile time on big-endian hosts (see the OPENSSL_BIG_ENDIAN guard in
// vm_ube_detect.c) -- intentional; we don't byte-swap an interface we can't
// exercise there.
//
// Members are naturally aligned (struct not packed, matching the kernel). The
// static asserts below pin the size and the offsets we dereference so an edit
// can't silently shift |vm_generation_counter|.

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
