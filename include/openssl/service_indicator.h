// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#ifndef AWSLC_HEADER_SERVICE_INDICATOR_H
#define AWSLC_HEADER_SERVICE_INDICATOR_H

#if defined(__cplusplus)
extern "C" {
#endif

OPENSSL_EXPORT uint64_t awslc_fips_service_indicator_get_counter(void);
OPENSSL_EXPORT uint32_t awslc_fips_service_indicator_get_serviceID(void);

#if defined(AWSLC_FIPS)
#define IS_FIPS_APPROVED_CALL_SERVICE(approved, func)                       \
  do {                                                                      \
    (approved) = 0;                                                         \
    uint64_t counter = awslc_fips_service_indicator_get_counter();          \
    func;                                                                   \
    if (awslc_fips_service_indicator_get_counter() != counter) {            \
        (approved) = 1;                                                     \
    }                                                                       \
 }                                                                          \
 while(0)                                                                   \

#else
#define IS_FIPS_APPROVED_CALL_SERVICE(approved, func, ...)                  \
  do {                                                                      \
    (approved) = 0;                                                         \
    func;                                                                   \
 }                                                                          \
 while(0)                                                                   \

#endif // AWSLC_FIPS

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // AWSLC_SERVICE_INDICATOR_H
