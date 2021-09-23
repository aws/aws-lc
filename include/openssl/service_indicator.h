// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#ifndef AWSLC_HEADER_SERVICE_INDICATOR_H
#define AWSLC_HEADER_SERVICE_INDICATOR_H

#if defined(__cplusplus)
extern "C" {
#endif

#define AWSLC_APPROVED                             1
#define AWSLC_NOT_APPROVED                         0

OPENSSL_EXPORT uint64_t FIPS_service_indicator_before_call(void);
OPENSSL_EXPORT uint64_t FIPS_service_indicator_after_call(void);
OPENSSL_EXPORT int FIPS_service_indicator_check_approved(int before, int after);

#if defined(AWSLC_FIPS)
#define CALL_SERVICE_AND_CHECK_APPROVED(approved, func)                     \
  do {                                                                      \
    (approved) = AWSLC_NOT_APPROVED;                                        \
    int before = FIPS_service_indicator_before_call();                      \
    func;                                                                   \
    int after = FIPS_service_indicator_after_call();                        \
    if (FIPS_service_indicator_check_approved(before, after)) {             \
        (approved) = AWSLC_APPROVED;                                        \
    }                                                                       \
 }                                                                          \
 while(0)                                                                   \

#else
// Assume true when FIPS is not on, for easier consumer compatibility that have
// both FIPS and non-FIPS libraries.
#define CALL_SERVICE_AND_CHECK_APPROVED(approved, func)                     \
  do {                                                                      \
    (approved) = AWSLC_APPROVED;                                            \
    func;                                                                   \
 }                                                                          \
 while(0)                                                                   \

#endif // AWSLC_FIPS

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // AWSLC_SERVICE_INDICATOR_H
