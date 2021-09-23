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

// hwaes_capable when enabled in x86 uses 9, 11, 13 for key rounds.
// hwaes_capable when enabled in ARM uses 10, 12, 14 for key rounds.
// When compiling with different ARM specific platforms, 9, 11, 13 are used for
// key rounds.
// TODO: narrow down when and which assembly/x86 ARM CPUs use [9,11,13] and [10,12,14]
#define AES_verify_service_indicator(key_rounds)                            \
do {                                                                        \
  switch (key_rounds) {                                                     \
    case 9:                                                                 \
    case 10:                                                                \
    case 11:                                                                \
    case 12:                                                                \
    case 13:                                                                \
    case 14:                                                                \
      FIPS_service_indicator_update_state();                                \
      break;                                                                \
    default:                                                                \
      break;                                                                \
  }                                                                         \
}                                                                           \
while(0)                                                                    \

// AEAD APIs work with different parameters.
#define AEAD_verify_service_indicator(key_length)                           \
do {                                                                        \
  switch (key_length) {                                                     \
    case 16:                                                                \
    case 32:                                                                \
      FIPS_service_indicator_update_state();                                \
      break;                                                                \
    default:                                                                \
      break;                                                                \
  }                                                                         \
}                                                                           \
while(0)                                                                    \

#endif  // AWSLC_HEADER_SERVICE_INDICATOR_INTERNAL_H
