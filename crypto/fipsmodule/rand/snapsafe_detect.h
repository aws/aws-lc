// -----------------------------------------------------------------------------
// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// -----------------------------------------------------------------------------

#ifndef HEADER_SNAPSAFE_DETECT
#define HEADER_SNAPSAFE_DETECT

#include <openssl/base.h>

#ifdef  __cplusplus
extern "C" {
#endif

#if defined(AWSLC_SYSGENID_PATH)
	#define AWSLC_SYSGENID_FILE_PATH AWSLC_SYSGENID_PATH
#else
	// If no user-specified path is provided at compile-time, use a default
	// path. Path taken from https://lkml.org/lkml/2021/3/8/677. This path
	// might change in the future, becasue the SysGenID interface is not yet
	// stable.
	#define AWSLC_SYSGENID_FILE_PATH "/dev/sysgenid"
#endif

// Experimental support for Snapsafe-type uniqueness breaking event (ube)
// detection.
//
// CRYPTO_get_snapsafe_generation returns the snapsafe generation number for the
// current process, or zero if not supported on the platform. The snapsafe
// generation number is a non-zero, strictly-monotonic counter with the property
// that, if queried in an address space and then again in a subsequently
// resumed snapshot/VM, the resumed address space will observe a greater value.
//
// We use SysGenID to detect resumed snapshot/VM events. See
// https://lkml.org/lkml/2021/3/8/677 for details about how SysGenID works.
// We make light use of the SysGenId capabilities and only use the following
// supported functions on the device: |open| and |mmap|.
//
// SysGenID is very new and the interface is not yet finalised. Therefore, we
// we only use this as a hardening mechanism and fail open. Hence the
// experimental note in the beginning.
//
// |CRYPTO_get_snapsafe_generation| expects exclusive write access to memory
// pointed to by |snapsafe_generation_number parameter|. If this can not be
// guaranteed (e.g. |snapsafe_generation_number| is a shared variable), caller
// must synchronise access.
OPENSSL_EXPORT int CRYPTO_get_snapsafe_generation(uint32_t *snapsafe_generation_number);

// Below functions are strictly for testing only!

// CRYPTO_snapsafe_detect_ignore_for_testing is an internal detail used for
// testing purposes.
OPENSSL_EXPORT void CRYPTO_snapsafe_detect_ignore_for_testing(void);

// HAZMAT_overwrite_sysgenid_for_testing is an internal detail used for testing
// purposes. Call |HAZMAT_overwrite_sysgenid_for_testing| after test suite has
// run. Function allocates memory and associates it with the SysGenID callback
// pointer.
// Returns 1 if succesfull and 0 otherwise.
OPENSSL_EXPORT int HAZMAT_overwrite_sysgenid_for_testing(void);

// HAZMAT_reset_sysgenid_for_testing is an internal detail used for testing
// purposes. It frees memory allocated in
// |HAZMAT_overwrite_sysgenid_for_testing| and deassociates the SysGenID
// callback pointer.
OPENSSL_EXPORT void HAZMAT_reset_sysgenid_for_testing(void);

// HAZMAT_overwrite_sysgenid_for_testing is an internal detail used for testing
// purposes. It assigns value |val| to the memory allocated in
// |HAZMAT_overwrite_sysgenid_for_testing|, which will be the new SysGenID
// value.
OPENSSL_EXPORT void HAZMAT_set_overwritten_sysgenid_for_testing(uint32_t val);

#ifdef  __cplusplus
}
#endif

#endif /* HEADER_SNAPSAFE_DETECT */
