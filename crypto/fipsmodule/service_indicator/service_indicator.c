// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/crypto.h>
#include <openssl/service_indicator.h>

// #if defined(AWSLC_FIPS)

struct fips_service_indicator_state {
  int counter;
};

void awslc_fips_service_indicator_init_counter(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_COUNTER);
  if (!indicator) {
    indicator = OPENSSL_malloc(sizeof(struct fips_service_indicator_state));
    if (!indicator || !CRYPTO_set_thread_local(
        AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_COUNTER, indicator, OPENSSL_free)) {
      return;
    }
  }
  indicator->counter = 0;
}

int awslc_fips_service_indicator_get_counter(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_COUNTER);
  if (!indicator) {
    awslc_fips_service_indicator_init_counter();
    indicator = CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_COUNTER);
  }
  return indicator->counter;
}

void awslc_fips_service_indicator_reset_counter(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_COUNTER);
  if (!indicator) {
    awslc_fips_service_indicator_init_counter();
    indicator = CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_COUNTER);
  }
  indicator->counter = 0;
}

void awslc_fips_service_indicator_inc_counter(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_COUNTER);
  if (!indicator) {
    awslc_fips_service_indicator_init_counter();
    indicator = CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_COUNTER);
  }
  indicator->counter++;
}

int awslc_fips_check_service_approved(int counter) {
  if(awslc_fips_service_indicator_get_counter() > counter) {
    return 1;
  }
  return 0;
}

//#else
//
//void awslc_set_service_indicator_approved(void) {}
//
//void awslc_set_service_indicator_not_approved(void) {}
//
//#endif // defined(AWSLC_FIPS)
