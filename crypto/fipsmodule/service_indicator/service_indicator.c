// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/crypto.h>
#include <openssl/service_indicator.h>

#if defined(AWSLC_FIPS)
int awslc_fips_service_indicator_get_counter(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (!indicator) {
    if(!awslc_fips_service_indicator_init_state()) {
      return 0;
    }
    indicator = CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  }
  return indicator->counter;
}

int awslc_fips_service_indicator_get_serviceID(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (!indicator) {
    if(!awslc_fips_service_indicator_init_state()) {
      return 0;
    }
    indicator = CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  }
  return indicator->serviceID;
}

int awslc_fips_service_indicator_reset_state(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (!indicator) {
    if(!awslc_fips_service_indicator_init_state()) {
      return 0;
    }
    indicator = CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  }
  indicator->counter = 0;
  indicator->serviceID = FIPS_APPROVED_NO_STATE;
  return 1;
}

int awslc_fips_check_service_approved(int prev_counter, int service_id) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if(!indicator || service_id == FIPS_APPROVED_NO_STATE) {
    return 0;
  }

  if(indicator->serviceID == service_id && indicator->counter > prev_counter){
    return 1;
  }
  return 0;
}

int awslc_fips_service_indicator_init_state(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (!indicator) {
    indicator = OPENSSL_malloc(sizeof(struct fips_service_indicator_state));
    if(!indicator) {
      return 0;
    }
    OPENSSL_memset(indicator, 0, sizeof(struct fips_service_indicator_state));
    if (!CRYPTO_set_thread_local(
        AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE, indicator, OPENSSL_free)) {
      return 0;
    }
  }
  indicator->counter = 0;
  indicator->serviceID = FIPS_APPROVED_NO_STATE;
  return 1;
}

// Only to be used internally, it is not intended for the user to update the state.
void awslc_fips_service_indicator_update_state(enum fips_approved_algorithm_t service_id) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (!indicator) {
    if(!awslc_fips_service_indicator_init_state()) {
      return;
    }
    indicator = CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  }
  indicator->counter++;
  indicator->serviceID = service_id;
}

#else

int awslc_fips_service_indicator_get_counter(void) { return 0; }
int awslc_fips_service_indicator_get_serviceID(void) { return 0; }
int awslc_fips_service_indicator_reset_state(void)  { return 0; }
int awslc_fips_check_service_approved(int prev_counter, int service_id) { return 0; }

#endif // AWSLC_FIPS
