// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef OPENSSL_HEADER_CRYPTO_UBE_INTERNAL_H
#define OPENSSL_HEADER_CRYPTO_UBE_INTERNAL_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <openssl/base.h>

// get_ube_generation_number returns the uniqueness-breaking event (UBE)
// generation number for the address space in |current_generation_number|. The
// UBE generation number is a non-zero, strictly-monotonic counter with the
// following property: if queried in an address space and then subsequently
// queried, after an UBE occurred, a greater value will be observed.
//
// This function should be used to protect unique memory. First cache a UBE
// generation number associating it to the unique memory at
// creation/initialization time. Before using the unique memory check whether
// the generation number has changed. Note, however, that detection methods rely
// on technology that is unique to a platform. Hence, support for UBE detection
// also depends on the platform AWS-LC is executed on.
//
// The parameter |current_generation_number| must be synchronized by the caller.
//
// Returns 1 on success and 0 otherwise. On 0, any unique state must randomize
// before usage. A 0 is either permanent (UBE detection is not supported or has
// failed; all subsequent entries will immediately return 0) or limited to this
// call (a VM UBE read failed). |CRYPTO_ube_detection_unavailable| tells the
// two apart.
OPENSSL_EXPORT int CRYPTO_get_ube_generation_number(uint64_t *current_generation_number);

// CRYPTO_ube_detection_unavailable returns 1 if UBE detection is permanently
// unavailable, i.e. |CRYPTO_get_ube_generation_number| will always return 0.
// Otherwise, it returns 0.
OPENSSL_EXPORT int CRYPTO_ube_detection_unavailable(void);

// CRYPTO_ube_detection_disable permanently disables UBE detection for the
// process, for when a detection method keeps failing at runtime. Afterwards
// |CRYPTO_ube_detection_unavailable| returns 1 and any unique state must
// randomize before every use.
OPENSSL_EXPORT void CRYPTO_ube_detection_disable(void);

// set_fork_ube_generation_number_FOR_TESTING sets the fork generation number to
// the value |fork_gn|. This value will be the fork generation value used by the
// UBE logic, overriding the generation number from the real fork detection.
// |allow_mocked_ube_detection_FOR_TESTING| must have been invoked
// (once per-process) to allow mocking the fork generation number.
OPENSSL_EXPORT void set_fork_ube_generation_number_FOR_TESTING(uint64_t fork_gn);

// set_vm_ube_generation_number_FOR_TESTING sets the vm_ube generation
// number to the value |vm_ube_gn|. This value will be the vm_ube generation
// value used by the UBE logic, overriding the generation number from the real
// vm_ube detection.
// |allow_mocked_ube_detection_FOR_TESTING| must have been invoked, once
// per-process, to allow mocking the vm_ube generation number.
OPENSSL_EXPORT void set_vm_ube_generation_number_FOR_TESTING(uint64_t vm_ube_gn);

// set_vm_ube_read_failures_FOR_TESTING makes the next |num_failures| mocked
// vm_ube generation number reads fail, as a vmclock seqlock that does not
// settle would. |allow_mocked_ube_detection_FOR_TESTING| must have been
// invoked.
OPENSSL_EXPORT void set_vm_ube_read_failures_FOR_TESTING(uint64_t num_failures);

// allow_mocked_ube_detection_FOR_TESTING allows mocking UBE detection even
// though real detection is not available. This function must be called in
// test code when mocking the generation numbers, once per-process. Mocking is
// process-global i.e. all threads will read the same mocked value.
OPENSSL_EXPORT void allow_mocked_ube_detection_FOR_TESTING(void);

// disable_mocked_ube_detection_FOR_TESTING disables mocking UBE detection. It
// also resets any mocked values to default values (0). This function should be
// invoked when exiting testing.
OPENSSL_EXPORT void disable_mocked_ube_detection_FOR_TESTING(void);

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_CRYPTO_UBE_INTERNAL_H
