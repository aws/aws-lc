//
// Created by Chiang, Samuel on 9/20/21.
//

#ifndef AWSLC_HEADER_SERVICE_INDICATOR_INTERNAL_H
#define AWSLC_HEADER_SERVICE_INDICATOR_INTERNAL_H

#include <openssl/service_indicator.h>

// FIPS functions.
#if defined(AWSLC_FIPS)

struct fips_service_indicator_state {
  uint64_t counter;
};

int FIPS_service_indicator_reset_state(void);
void FIPS_service_indicator_update_state(void);

#else
OPENSSL_INLINE int FIPS_service_indicator_reset_state(void) { return 0; }
OPENSSL_INLINE void FIPS_service_indicator_update_state(void) { }
#endif // AWSLC_FIPS

void AES_verify_service_indicator(unsigned key_rounds);
void AEAD_verify_service_indicator(size_t key_length);

#endif  // AWSLC_HEADER_SERVICE_INDICATOR_INTERNAL_H
