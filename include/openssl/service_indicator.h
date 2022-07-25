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

#if defined(AWSLC_FIPS)

#define AWSLC_MODE_STRING "AWS-LC FIPS "

#else

#define AWSLC_MODE_STRING "AWS-LC "

#endif // AWSLC_FIPS

#define AWSLC_VERSION_STRING AWSLC_MODE_STRING AWSLC_VERSION_NUMBER_STRING

#if defined(__cplusplus)
}  // extern C

#if !defined(BORINGSSL_NO_CXX)

extern "C++" {

// CALL_SERVICE_AND_CHECK_APPROVED runs |func| and sets |approved| to one of the
// |FIPSStatus*| values, above, depending on whether |func| invoked an
// approved service. The result of |func| becomes the result of this macro.
// It is highly recommended that users of the service indicator use this macro
// when interacting with the service indicator.
#define CALL_SERVICE_AND_CHECK_APPROVED(approved, func)             \
  [&] {                                                             \
    bssl::FIPSIndicatorHelper fips_indicator_helper(&approved);     \
    return func;                                                    \
  }()

namespace bssl {

enum class FIPSStatus {
  NOT_APPROVED = 0,
  APPROVED = 1,
};

// FIPSIndicatorHelper records whether the service indicator counter advanced
// during its lifetime.
class FIPSIndicatorHelper {
 public:
  FIPSIndicatorHelper(FIPSStatus *result)
      : result_(result), before_(FIPS_service_indicator_before_call()) {
    *result_ = FIPSStatus::NOT_APPROVED;
  }

  ~FIPSIndicatorHelper() {
    uint64_t after = FIPS_service_indicator_after_call();
    if (after != before_) {
      *result_ = FIPSStatus::APPROVED;
    }
  }

  FIPSIndicatorHelper(const FIPSIndicatorHelper&) = delete;
  FIPSIndicatorHelper &operator=(const FIPSIndicatorHelper &) = delete;

 private:
  FIPSStatus *const result_;
  const uint64_t before_;
};

}  // namespace bssl
}  // extern "C++"

#endif  // !BORINGSSL_NO_CXX
#endif  // __cplusplus

#endif  // AWSLC_SERVICE_INDICATOR_H
