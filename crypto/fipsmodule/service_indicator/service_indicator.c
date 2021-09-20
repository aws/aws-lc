// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/crypto.h>
#include <openssl/service_indicator.h>

#if defined(AWSLC_FIPS)
static int awslc_fips_service_indicator_init_state(void) {
  struct fips_service_indicator_state *indicator;
  indicator = OPENSSL_malloc(sizeof(struct fips_service_indicator_state));
  if (indicator == NULL || !CRYPTO_set_thread_local(
      AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE, indicator, OPENSSL_free)) {
    return 0;
  }
  indicator->counter = 0;
  indicator->service_id = FIPS_APPROVED_NO_STATE;
  return 1;
}

uint64_t awslc_fips_service_indicator_get_counter(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (indicator == NULL) {
    return 0;
  }
  return indicator->counter;
}

uint32_t awslc_fips_service_indicator_get_serviceID(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (indicator == NULL) {
    return FIPS_APPROVED_NO_STATE;
  }
  return indicator->service_id;
}

// Only to be used internally, it is not intended for the user to reset the state.
int awslc_fips_service_indicator_reset_state(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (indicator == NULL) {
    if(!awslc_fips_service_indicator_init_state()) {
      return 0;
    }
    indicator = CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  }
  indicator->counter = 0;
  indicator->service_id = FIPS_APPROVED_NO_STATE;
  return 1;
}

// Only to be used internally, it is not intended for the user to update the state.
void awslc_fips_service_indicator_update_state(enum fips_approved_algorithm_t service_id) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (indicator == NULL) {
    if(!awslc_fips_service_indicator_init_state()) {
      return;
    }
    indicator = CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  }
  indicator->counter++;
  indicator->service_id = service_id;
}

#else

uint64_t awslc_fips_service_indicator_get_counter(void) { return 0; }
uint32_t awslc_fips_service_indicator_get_serviceID(void) { return 0; }

#endif // AWSLC_FIPS
