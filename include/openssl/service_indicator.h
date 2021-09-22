// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#ifndef AWSLC_HEADER_SERVICE_INDICATOR_H
#define AWSLC_HEADER_SERVICE_INDICATOR_H

#if defined(__cplusplus)
extern "C" {
#endif

#define APPROVED                             1
#define NOT_APPROVED                         0

OPENSSL_EXPORT uint64_t FIPS_service_indicator_get_counter(void);

#if defined(AWSLC_FIPS)
#define IS_FIPS_APPROVED_CALL_SERVICE(approved, func)                       \
  do {                                                                      \
    (approved) = NOT_APPROVED;                                              \
    uint64_t counter = FIPS_service_indicator_get_counter();                \
    func;                                                                   \
    if (FIPS_service_indicator_get_counter() != counter) {                  \
        (approved) = APPROVED;                                              \
    }                                                                       \
 }                                                                          \
 while(0)                                                                   \

#else
// Assume true when FIPS is not on, for easier consumer compatibility that have
// both FIPS and non-FIPS libraries.
#define IS_FIPS_APPROVED_CALL_SERVICE(approved, func)                       \
  do {                                                                      \
    (approved) = APPROVED;                                                  \
    func;                                                                   \
 }                                                                          \
 while(0)                                                                   \

#endif // AWSLC_FIPS

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // AWSLC_SERVICE_INDICATOR_H
