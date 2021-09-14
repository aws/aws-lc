// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#ifndef AWSLC_HEADER_SERVICE_INDICATOR_H
#define AWSLC_HEADER_SERVICE_INDICATOR_H

#if defined(__cplusplus)
extern "C" {
#endif

struct fips_service_indicator_state {
  int counter;
  int serviceID;
};

OPENSSL_EXPORT int awslc_fips_service_indicator_get_counter(void);
OPENSSL_EXPORT struct fips_service_indicator_state *awslc_fips_service_indicator_get_state(void);
OPENSSL_EXPORT void awslc_fips_service_indicator_reset_state(void);
OPENSSL_EXPORT int awslc_fips_check_service_approved(int prev_counter, int service_id);


#if defined(__cplusplus)
}  // extern C
#endif

#if !defined(BORINGSSL_NO_CXX)
extern "C++" {

BSSL_NAMESPACE_BEGIN

BORINGSSL_MAKE_DELETER(fips_service_indicator_state, OPENSSL_free)

BSSL_NAMESPACE_END

}  // extern C++
#endif  // !BORINGSSL_NO_CXX

#endif  // AWSLC_SERVICE_INDICATOR_H
