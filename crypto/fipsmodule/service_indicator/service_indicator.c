// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/crypto.h>
#include <openssl/service_indicator.h>

#if defined(AWSLC_FIPS)
static int FIPS_service_indicator_init_state(void) {
  struct fips_service_indicator_state *indicator;
  indicator = OPENSSL_malloc(sizeof(struct fips_service_indicator_state));
  if (indicator == NULL || !CRYPTO_set_thread_local(
      AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE, indicator, OPENSSL_free)) {
    return 0;
  }
  indicator->counter = 0;
  return 1;
}

static uint64_t FIPS_service_indicator_get_counter(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (indicator == NULL) {
    return 0;
  }
  return indicator->counter;
}

uint64_t FIPS_service_indicator_before_call(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (indicator == NULL) {
    if(!FIPS_service_indicator_init_state()) {
      return 0;
    }
  }
  return FIPS_service_indicator_get_counter();
}

uint64_t FIPS_service_indicator_after_call(void) {
  return FIPS_service_indicator_get_counter();
}

int FIPS_service_indicator_check_approved(int before, int after) {
  if(before != after) {
    return 1;
  }
  return 0;
}

// Only to be used internally after the FIPS power-on self-tests, it is not
// intended for the user to reset the state.
int FIPS_service_indicator_reset_state(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (indicator == NULL) {
    if(!FIPS_service_indicator_init_state()) {
      return 0;
    }
    indicator = CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  }
  indicator->counter = 0;
  return 1;
}

// Only to be used internally, it is not intended for the user to update the state.
void FIPS_service_indicator_update_state(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (indicator == NULL) {
    return;
  }
  indicator->counter++;
}

#else

uint64_t FIPS_service_indicator_before_call(void) { return 0; }
uint64_t FIPS_service_indicator_after_call(void) { return 0; }
int FIPS_service_indicator_check_approved(int before, int after) { return 0; }

#endif // AWSLC_FIPS

// hwaes_capable when enabled in x86 uses 9, 11, 13 for key rounds.
// hwaes_capable when enabled in ARM uses 10, 12, 14 for key rounds.
// When compiling with different ARM specific platforms, 9, 11, 13 are used for
// key rounds.
// TODO: narrow down when and which assembly/x86 ARM CPUs use [9,11,13] and [10,12,14]
void AES_verify_service_indicator(unsigned key_rounds) {
  switch (key_rounds) {
    case 9:
    case 10:
    case 11:
    case 12:
    case 13:
    case 14:
      FIPS_service_indicator_update_state();
      break;
    default:
      break;
  }
}

// AEAD APIs work with different parameters.
void AEAD_verify_service_indicator(size_t key_length) {
  switch (key_length) {
    case 16:
    case 32:
      FIPS_service_indicator_update_state();
      break;
    default:
      break;
  }
}

