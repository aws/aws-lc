// -----------------------------------------------------------------------------
// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// -----------------------------------------------------------------------------

#ifndef HEADER_SYSGENID_TEST_UTIL
#define HEADER_SYSGENID_TEST_UTIL

#include <openssl/base.h>

#if defined(OPENSSL_LINUX)

#define SNAPSAFE_SUPPORTED 0
#define SNAPSAFE_NOT_SUPPORTED 1

// set_new_sysgenid_value sets the SysGenID value to |new_sysgenid_value|.
// Returns 1 if successful and 0 otherwise.
int set_new_sysgenid_value(uint32_t new_sysgenid_value);

// setup_sysgenid_support determines if SysGenID is supported, and if not,
// initialises a back up method that imitates the SysGenID device through a
// plain file.
void setup_sysgenid_support(void);

// Maybe clean up after tests: removes the SysGenID mock file if generated, and
// resets Snapsafe detection.
void maybe_cleanup(void);

#endif // defined(OPENSSL_LINUX)

#endif // HEADER_SYSGENID_TEST_UTIL
