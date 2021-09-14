// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#ifndef AWSLC_HEADER_SERVICE_INDICATOR_H
#define AWSLC_HEADER_SERVICE_INDICATOR_H

#if defined(__cplusplus)
extern "C" {
#endif

//#if defined(AWSLC_FIPS)

OPENSSL_EXPORT int awslc_fips_service_indicator_get_counter(void);
OPENSSL_EXPORT void awslc_fips_service_indicator_reset_counter(void);
OPENSSL_EXPORT int awslc_fips_check_service_approved(int counter);

// #else

// #endif

#if defined(__cplusplus)
}  // extern C

extern "C++" {

BSSL_NAMESPACE_BEGIN

BSSL_NAMESPACE_END

}  // extern C++

#endif

#endif  // AWSLC_SERVICE_INDICATOR_H
