// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/crypto.h>
#include <openssl/service_indicator.h>

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
  indicator->lock_state = STATE_UNLOCKED;
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
  if(indicator->lock_state == STATE_UNLOCKED) {
    indicator->counter++;
  }
}

void FIPS_service_indicator_lock_state(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (indicator == NULL) {
    return;
  }
  // This shouldn't overflow unless |FIPS_service_indicator_unlock_state| wasn't
  // correctly called after |FIPS_service_indicator_lock_state| in the same
  // function.
  indicator->lock_state++;
}

void FIPS_service_indicator_unlock_state(void) {
  struct fips_service_indicator_state *indicator =
      CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (indicator == NULL) {
    return;
  }
  // This shouldn't overflow unless |FIPS_service_indicator_lock_state| wasn't
  // correctly called before |FIPS_service_indicator_unlock_state| in the same
  // function.
  indicator->lock_state--;
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

void AES_CMAC_verify_service_indicator(const CMAC_CTX *ctx) {
  // Only 128 and 256 bit keys are approved for AES-CMAC.
  switch (ctx->cipher_ctx.key_len) {
    case 16:
    case 32:
      FIPS_service_indicator_update_state();
      break;
    default:
      break;
  }
}

void HMAC_verify_service_indicator(const EVP_MD *evp_md) {
  // HMAC with SHA1, SHA224, SHA256, SHA384, and SHA512 are approved.
  switch (evp_md->type){
    case NID_sha1:
    case NID_sha224:
    case NID_sha256:
    case NID_sha384:
    case NID_sha512:
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
void AEAD_verify_service_indicator(size_t key_length) { }

void AES_CMAC_verify_service_indicator(OPENSSL_UNUSED const CMAC_CTX *ctx) { }

void HMAC_verify_service_indicator(OPENSSL_UNUSED const EVP_MD *evp_md) { }

#endif // AWSLC_FIPS



