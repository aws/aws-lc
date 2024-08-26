// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef OPENSSL_HEADER_CRYPTO_UBE_INTERNAL_H
#define OPENSSL_HEADER_CRYPTO_UBE_INTERNAL_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <openssl/base.h>

// get_ube_generation_number returns the UBE generation number for the address
// space in |current_generation_number|. The UBE generation number is a
// non-zero, strictly-monotonic counter with the following property: if queried
// in an address space and then subsequently queried, after an UBE occurred, a
// greater value will be observed.
//
// This function should be used to protect volatile memory. First cache a UBE
// generation number associating it to the volatile memory at
// creation/initialization time. Before using the volatile memory check whether
// the generation number has changed. Note, however, that detection methods rely
// on technology that is unique to a platform. Hence, support for UBE detection
// also depends on the platform AWS-LC is executed on.
//
// The parameter |current_generation_number| must be synchronized by the caller.
//
// Returns 1 on success and 0 if not supported. 0 means that UBE detection is
// not supported and any volatile state must randomize before usage.
// In case of an error or if UBE detection is unavailable, all subsequent
// entries will immediately return.
OPENSSL_EXPORT int get_ube_generation_number(uint64_t *current_generation_number);

// TODO
// Temporary overrides. Replace with something better. Used atm to test
// implementation during development.
OPENSSL_EXPORT void set_fork_generation_number_FOR_TESTING(uint64_t fork_gn);
OPENSSL_EXPORT void set_snapsafe_generation_number_FOR_TESTING(uint64_t snapsafe_gn);

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_CRYPTO_UBE_INTERNAL_H
