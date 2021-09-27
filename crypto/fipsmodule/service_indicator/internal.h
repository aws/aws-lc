// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#ifndef AWSLC_HEADER_SERVICE_INDICATOR_INTERNAL_H
#define AWSLC_HEADER_SERVICE_INDICATOR_INTERNAL_H

#include <openssl/service_indicator.h>

#if defined(AWSLC_FIPS)

struct fips_service_indicator_state {
  uint64_t counter;
};

// Only to be used internally, it is not intended for the user to update the
// state. This function is used to update the service indicator state, if the
// service is deemed to be approved.
void FIPS_service_indicator_update_state(void);

#else

// Service indicator functions are not intended for use during non-FIPS mode.
// If these functions are run during non-FIPS mode, they will return nothing or
// 0 accordingly.
OPENSSL_INLINE void FIPS_service_indicator_update_state(void) { }

#endif // AWSLC_FIPS

// Service indicator check for most AES algorithms.
// hwaes_capable when enabled in x86 uses 9, 11, 13 for key rounds.
// hwaes_capable when enabled in ARM uses 10, 12, 14 for key rounds.
// When compiling with different ARM specific platforms, 9, 11, 13 are used for
// key rounds.
void AES_verify_service_indicator(unsigned key_rounds);

// AEAD APIs work with different parameters. Only internal IV for AES-GCM is
// meant to be approved.
void AEAD_verify_service_indicator(size_t key_length);

#endif  // AWSLC_HEADER_SERVICE_INDICATOR_INTERNAL_H
