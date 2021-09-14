// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/crypto.h>
#include <openssl/service_indicator.h>

// #if defined(AWSLC_FIPS)

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
  indicator->serviceID = fips_approved_no_state;
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

struct fips_service_indicator_state *awslc_fips_service_indicator_get_state(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_COUNTER);
  if(!indicator) {
    return NULL;
  }
  struct fips_service_indicator_state *state = OPENSSL_malloc(sizeof(struct fips_service_indicator_state));
  memcpy(state, indicator, sizeof(struct fips_service_indicator_state));
  return state;
}

void awslc_fips_service_indicator_reset_state(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_COUNTER);
  if (!indicator) {
    awslc_fips_service_indicator_init_counter();
    indicator = CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_COUNTER);
  }
  indicator->counter = 0;
  indicator->serviceID = fips_approved_no_state;
}

// Only to be used internally, it is not intended for the user to update the counter.
void awslc_fips_service_indicator_update_state(int service_id) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_COUNTER);
  if (!indicator) {
    awslc_fips_service_indicator_init_counter();
    indicator = CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_COUNTER);
  }
  indicator->counter++;
  indicator->serviceID = service_id;
}

int awslc_fips_check_service_approved(int prev_counter, int service_id) {
  if(service_id == fips_approved_no_state) {
    return 0;
  }
  struct fips_service_indicator_state *state = awslc_fips_service_indicator_get_state();
  if(state->serviceID == service_id && state->counter > prev_counter){
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
