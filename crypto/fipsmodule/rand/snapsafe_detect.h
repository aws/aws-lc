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

// CRYPTO_get_snapsafe_generation returns the snapsafe generation number for the
// current process, or zero if not supported on the platform. The snapsafe
// generation number is a non-zero, strictly-monotonic counter with the property
// that, if queried in an address space and then again in a subsequently
// resumed snapshot/VM, the resumed snapshot address space will observe a
// greater value.
//
// We use SysGenID to detect when snapsafe can be violated. See
// https://lkml.org/lkml/2021/3/8/677 for details about how SysGenID works.
// We make light use of the SysGenId capabilities and only use the following
// supported functions on the device: |open| and |mmap|.
//
// SysGenID is very new and the interface is not yet finalised. Therefore, we
// we only use this as a hardening mechanism and fail open.
OPENSSL_EXPORT int CRYPTO_get_snapsafe_generation(uint32_t *snapsafe_generation_number);

// CRYPTO_snapsafe_detect_ignore_for_testing is an internal detail
// used for testing purposes.
OPENSSL_EXPORT void CRYPTO_snapsafe_detect_ignore_for_testing(void);

// hazmat_replace_sysgenid_file_path_for_testing is an internal detail
// used for testing purposes.
OPENSSL_EXPORT void HAZMAT_replace_sysgenid_file_path_for_testing(char *new_sysgenid_path);

#ifdef  __cplusplus
}
#endif

#endif /* HEADER_SNAPSAFE_DETECT */
