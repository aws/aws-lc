// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/crypto.h>
#include <openssl/service_indicator.h>
#include "internal.h"

#if defined(AWSLC_FIPS)

// Should only be called once per thread. Only called when initializing the state
// in |FIPS_service_indicator_before_call|.
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
    return AWSLC_APPROVED;
  }
  return AWSLC_NOT_APPROVED;
}

void FIPS_service_indicator_update_state(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (indicator == NULL) {
    return;
  }
  indicator->counter++;
}

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

void AES_verify_service_indicator_with_ctx(EVP_CIPHER_CTX *ctx) {
  switch(EVP_CIPHER_CTX_mode(ctx)) {
    case EVP_CIPH_ECB_MODE:
    case EVP_CIPH_CBC_MODE:
    case EVP_CIPH_CTR_MODE:
      break;
    default:
      return;
  }
  switch (ctx->cipher->key_len) {
    case 16:
    case 24:
    case 32:
      FIPS_service_indicator_update_state();
      break;
    default:
      break;
  }
}

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

#else

uint64_t FIPS_service_indicator_before_call(void) { return 0; }
uint64_t FIPS_service_indicator_after_call(void) { return 0; }
int FIPS_service_indicator_check_approved(int before, int after) { return AWSLC_NOT_APPROVED; }

void AES_verify_service_indicator(unsigned key_rounds) { }
void AES_verify_service_indicator_with_ctx(EVP_CIPHER_CTX *ctx) { }
void AEAD_verify_service_indicator(size_t key_length) { }

#endif // AWSLC_FIPS



