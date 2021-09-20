// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#ifndef AWSLC_HEADER_SERVICE_INDICATOR_H
#define AWSLC_HEADER_SERVICE_INDICATOR_H

#if defined(__cplusplus)
extern "C" {
#endif

#define FIPS_APPROVED                             1
#define FIPS_NOT_APPROVED                         0

enum fips_approved_algorithm_t {
  FIPS_APPROVED_NO_STATE        = 0,
  FIPS_APPROVED_EVP_AES_128_GCM = 1,
  FIPS_APPROVED_EVP_AES_256_GCM = 2,
  FIPS_APPROVED_EVP_AES_128_CTR = 3,
  FIPS_APPROVED_EVP_AES_192_CTR = 4,
  FIPS_APPROVED_EVP_AES_256_CTR = 5,
  FIPS_APPROVED_EVP_AES_128_CBC = 6,
  FIPS_APPROVED_EVP_AES_192_CBC = 7,
  FIPS_APPROVED_EVP_AES_256_CBC = 8,

  FIPS_APPROVED_ALGORITHM_MAX = 8,
};

OPENSSL_EXPORT uint64_t awslc_fips_service_indicator_get_counter(void);
OPENSSL_EXPORT uint32_t awslc_fips_service_indicator_get_serviceID(void);

#if defined(AWSLC_FIPS)
#define IS_FIPS_APPROVED_CALL_SERVICE(approved, func)                       \
  do {                                                                      \
    (approved) = FIPS_NOT_APPROVED;                                         \
    uint64_t counter = awslc_fips_service_indicator_get_counter();          \
    func;                                                                   \
    if (awslc_fips_service_indicator_get_counter() != counter) {            \
        (approved) = FIPS_APPROVED;                                         \
    }                                                                       \
 }                                                                          \
 while(0)                                                                   \

#else
// Assume true when FIPS is not on, for easier consumer compatibility that have
// both FIPS and non-FIPS libraries.
#define IS_FIPS_APPROVED_CALL_SERVICE(approved, func)                       \
  do {                                                                      \
    (approved) = FIPS_APPROVED;                                             \
    func;                                                                   \
 }                                                                          \
 while(0)                                                                   \

#endif // AWSLC_FIPS

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // AWSLC_SERVICE_INDICATOR_H
