// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef HEADER_VM_UBE_DETECT
#define HEADER_VM_UBE_DETECT

#include <openssl/base.h>

#ifdef __cplusplus
extern "C" {
#endif

#if !defined(AWSLC_SYSGENID_PATH)
  #define AWSLC_SYSGENID_PATH "/dev/sysgenid"
#endif

#if !defined(AWSLC_VMCLOCK_PATH)
  #define AWSLC_VMCLOCK_PATH "/dev/vmclock0"
#endif

// VM UBE-type uniqueness breaking event (ube detection).
//
// CRYPTO_get_vm_ube_generation provides the VM UBE generation number for
// the current process. For a genuine reading the VM UBE generation number is a
// non-zero, strictly-monotonic counter with the property that, if queried in an
// address space and then again in a subsequently resumed snapshot/VM, the
// resumed address space will observe a greater value.
//
// Two detection mechanisms are supported:
//   1. vmclock -- /dev/vmclock0 (preferred). See
//      https://uapi-group.org/specifications/specs/vmclock/
//   2. SysGenID -- /dev/sysgenid (fallback). See
//      https://lkml.org/lkml/2021/3/8/677
//
// vmclock is preferred when available. If neither is available, the function
// reports that VM UBE detection is not supported.
//
// Return values:
//   1  |*vm_ube_generation_number| holds a usable value:
//        - the current generation number for a consistent read;
//        - 0 if no VM UBE interface is present (not supported);
//        - a "poison" value (bit 63 set) on a transient read failure (e.g. a
//          wedged vmclock seqlock). It differs from any cached or genuine
//          counter, so the caller reseeds via its normal "changed" path and
//          recovers on the next consistent read.
//      Callers must only test whether the value changed, not its magnitude.
//   0  Permanent failure: an interface is present but uninitializable. Not
//      returned on Linux (degrades to "not supported"), but reserved for
//      callers that must distinguish it.
OPENSSL_EXPORT int CRYPTO_get_vm_ube_generation(
                                          uint64_t *vm_ube_generation_number);

// CRYPTO_get_vm_ube_active returns 1 if the file system presents a VM UBE
// interface (vmclock or SysGenID) and the library has successfully initialized
// its use. Otherwise, it returns 0.
OPENSSL_EXPORT int CRYPTO_get_vm_ube_active(void);

// CRYPTO_get_vm_ube_supported returns 1 if the file system presents a VM UBE
// interface (vmclock or SysGenID). Otherwise, it returns 0.
OPENSSL_EXPORT int CRYPTO_get_vm_ube_supported(void);

// CRYPTO_get_sysgenid_path returns the path used for the SysGenId interface.
OPENSSL_EXPORT const char *CRYPTO_get_sysgenid_path(void);

// CRYPTO_get_vmclock_path returns the path used for the vmclock interface.
OPENSSL_EXPORT const char *CRYPTO_get_vmclock_path(void);

#if defined(OPENSSL_LINUX) && defined(AWSLC_TEST_SYSGENID)
// HAZMAT_init_sysgenid_file should only be used for testing. It creates and
// initializes the sysgenid path indicated by AWSLC_SYSGENID_PATH.
// On success, it returns 1. Otherwise, returns 0.
OPENSSL_EXPORT int HAZMAT_init_sysgenid_file(void);
#endif

#if defined(OPENSSL_LINUX) && defined(AWSLC_TEST_VMCLOCK)
// HAZMAT_init_vmclock_file should only be used for testing. It creates and
// initializes the vmclock path indicated by AWSLC_VMCLOCK_PATH.
// On success, it returns 1. Otherwise, returns 0.
OPENSSL_EXPORT int HAZMAT_init_vmclock_file(void);
#endif

#if defined(OPENSSL_LINUX) && defined(AWSLC_VM_UBE_TESTING)
// HAZMAT_reinit_vm_ube_FOR_TESTING (testing only) unmaps any active backend and
// re-runs init against the current stand-in file(s), so tests can exercise init
// outcomes (corrupt or inaccessible device) the once-per-process path can't
// reach. Single-threaded test context only.
OPENSSL_EXPORT void HAZMAT_reinit_vm_ube_FOR_TESTING(void);
#endif

#ifdef __cplusplus
}
#endif

#endif /* HEADER_VM_UBE_DETECT */
