// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#ifndef AWSLC_HEADER_SERVICE_INDICATOR_H
#define AWSLC_HEADER_SERVICE_INDICATOR_H

#include <openssl/base.h>

#if defined(__cplusplus)
extern "C" {
#endif

#define AWSLC_APPROVED                             1
#define AWSLC_NOT_APPROVED                         0

// |FIPS_service_indicator_before_call| and |FIPS_service_indicator_after_call|
// both currently return the same local thread counter which is slowly
// incremented whenever approved services are called.
//
// |FIPS_service_indicator_before_call| is intended to be called right before
// an approved service, while |FIPS_service_indicator_after_call| should be
// called immediately after. If the values returned from these two functions are
// not equal, this means that the service called in between is deemed to be
// approved. If the values are still the same, this means the counter has not
// been incremented, and the service called is otherwise not approved for FIPS.
OPENSSL_EXPORT uint64_t FIPS_service_indicator_before_call(void);
OPENSSL_EXPORT uint64_t FIPS_service_indicator_after_call(void);

OPENSSL_EXPORT const char* awslc_version_string(void);

// |FIPS_service_indicator_check_approved| is intended to take in the before and
// after counter values. It will return |AWSLC_APPROVED| if the approval check
// was successful, and |AWSLC_NOT_APPROVED| if otherwise.
//
// Service indicator calls should not be used in non-FIPS builds. However, if
// used, the direct check to |FIPS_service_indicator_check_approved|
// will always indicate |AWSLC_APPROVED| in non-FIPS builds.
// It is recommended to use the macro |CALL_SERVICE_AND_CHECK_APPROVED| though,
// which will also always return |AWSLC_APPROVED| in non-FIPS builds.
OPENSSL_EXPORT int FIPS_service_indicator_check_approved(uint64_t before, uint64_t after);

#if defined(AWSLC_FIPS)
#define AWSLC_MODE_STRING "AWS-LC FIPS "

// This macro provides a bundled way to do an approval check and run the service.
// The |approved| value passed in will change to |AWSLC_APPROVED| and
// |AWSLC_NOT_APPROVED| accordingly to the approved state of the service ran.
// It is highly recommended that users of the service indicator use this macro
// when interacting with the service indicator.
#define CALL_SERVICE_AND_CHECK_APPROVED(approved, func)             \
  do {                                                              \
    (approved) = AWSLC_NOT_APPROVED;                                \
    int before = FIPS_service_indicator_before_call();              \
    func;                                                           \
    int after = FIPS_service_indicator_after_call();                \
    if (FIPS_service_indicator_check_approved(before, after)) {     \
        (approved) = AWSLC_APPROVED;                                \
    }                                                               \
 }                                                                  \
 while(0)                                                           \

#else

#define AWSLC_MODE_STRING "AWS-LC "

// Assume |AWSLC_APPROVED| when FIPS is not on, for easier consumer compatibility
// that have both FIPS and non-FIPS libraries.
#define CALL_SERVICE_AND_CHECK_APPROVED(approved, func)             \
  do {                                                              \
    (approved) = AWSLC_APPROVED;                                    \
    func;                                                           \
 }                                                                  \
 while(0)                                                           \

#endif // AWSLC_FIPS

#define AWSLC_VERSION_STRING AWSLC_MODE_STRING AWSLC_VERSION_NUMBER_STRING

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // AWSLC_SERVICE_INDICATOR_H
