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
// the current process. The VM UBE generation number is a non-zero,
// strictly-monotonic counter with the property that, if queried in an address
// space and then again in a subsequently resumed snapshot/VM, the resumed
// address space will observe a greater value.
//
// Two detection mechanisms are supported:
//   1. vmclock — Uses /dev/vmclock0 (preferred). See
//      https://uapi-group.org/specifications/specs/vmclock/ for details.
//   2. SysGenID — Uses /dev/sysgenid (fallback). See
//      https://lkml.org/lkml/2021/3/8/677 for details.
//
// vmclock is preferred when available. If neither is available, the function
// reports that VM UBE detection is not supported.
//
// |CRYPTO_get_vm_ube_generation| returns 0 only when the filesystem
// presents a VM UBE interface but we are unable to initialize its use.
// Otherwise, it returns 1.
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
// HAZMAT_reinit_vm_ube_FOR_TESTING should only be used for testing. It unmaps
// any active backend mapping and re-runs VM UBE backend initialization against
// the current on-disk state of the stand-in device file(s). This lets tests
// exercise initialization outcomes (e.g. a device that is present but corrupt
// or inaccessible) that the once-per-process init path cannot otherwise reach.
// It must only be called from a single-threaded test context.
OPENSSL_EXPORT void HAZMAT_reinit_vm_ube_FOR_TESTING(void);
#endif

#ifdef __cplusplus
}
#endif

#endif /* HEADER_VM_UBE_DETECT */
