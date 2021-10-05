// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#ifndef AWSLC_HEADER_SERVICE_INDICATOR_INTERNAL_H
#define AWSLC_HEADER_SERVICE_INDICATOR_INTERNAL_H

#include <openssl/service_indicator.h>

#if defined(AWSLC_FIPS)

#define STATE_LOCKED       0

struct fips_service_indicator_state {
  uint64_t lock_state;
  uint64_t counter;
};

// Only to be used internally, it is not intended for the user to update the
// state. This function is used to update the service indicator state, if the
// service is deemed to be approved.
void FIPS_service_indicator_update_state(void);

// Only to be used internally. Certain approved algorithms call upon other
// approved algorithms, and some services provide one-shot functions that call
// upon multiple functions that are approved themselves.
// These functions lock/unlock the counter state, so that nested calls of
// |FIPS_service_indicator_update_state| within don't update the counter
// unintentionally. The lock is implemented as a counter, as one-shot functions
// may call upon approved nested functions which have approved nested algorithms
// within them as well. The counter state can only be updated when the
// |lock_state| has a value of 0.
// For the approval checks to work correctly, whenever
// |FIPS_service_indicator_lock_state| is called,
// |FIPS_service_indicator_unlock_state| must be called before exiting the
// function. This ensures that the counter is only updated when the most
// high level function that initially locked the state first, unlocks the
// |lock_state| back to 0.
void FIPS_service_indicator_lock_state(void);
void FIPS_service_indicator_unlock_state(void);

#else

// Service indicator functions are not intended for use during non-FIPS mode.
// If these functions are run during non-FIPS mode, they will provide no
// operations.
OPENSSL_INLINE void FIPS_service_indicator_update_state(void) { }
OPENSSL_INLINE void FIPS_service_indicator_lock_state(void) { }
OPENSSL_INLINE void FIPS_service_indicator_unlock_state(void) { }

#endif // AWSLC_FIPS

// Parameters of service indicator check functions to verify against should and
// are assumed to be not NULL.

// Service indicator check for most AES algorithms.
// hwaes_capable when enabled in x86 uses 9, 11, 13 for key rounds.
// hwaes_capable when enabled in ARM uses 10, 12, 14 for key rounds.
// When compiling with different ARM specific platforms, 9, 11, 13 are used for
// key rounds.
void AES_verify_service_indicator(unsigned key_rounds);

// The service indicator checks use different parameters for AEAD APIs than
// those of other AES modes. AES-GCM is approved only with an internal IV, see
// SP 800-38D Sec 8.2.2.
void AEAD_verify_service_indicator(size_t key_length);

void AES_CMAC_verify_service_indicator(const CMAC_CTX *ctx);

void HMAC_verify_service_indicator(const EVP_MD *evp_md);

#endif  // AWSLC_HEADER_SERVICE_INDICATOR_INTERNAL_H
