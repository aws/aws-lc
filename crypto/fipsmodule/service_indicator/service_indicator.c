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

void AES_verify_service_indicator(const EVP_CIPHER_CTX *ctx, const unsigned key_rounds) {
  if(ctx != NULL) {
    if (EVP_CIPHER_CTX_mode(ctx) == EVP_CIPH_ECB_MODE ||
        EVP_CIPHER_CTX_mode(ctx) == EVP_CIPH_CBC_MODE ||
        EVP_CIPHER_CTX_mode(ctx) == EVP_CIPH_CTR_MODE) {
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
  } else {
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
}

void AEAD_GCM_verify_service_indicator(const EVP_AEAD_CTX *ctx) {
  // Not the best way to write this, but the delocate parser for ARM/clang can't
  // recognize || if statements, or switch statements for this.
  // TODO: Update the delocate parser to be able to recognize a more readable
  // version of this.
  // We only have support for 128 bit and 256 bit keys for AES-GCM.
   if(EVP_AEAD_key_length(ctx->aead) == 16) {
    FIPS_service_indicator_update_state();
   } else if(EVP_AEAD_key_length(ctx->aead) == 32) {
    FIPS_service_indicator_update_state();
   }
}

void AEAD_CCM_verify_service_indicator(const EVP_AEAD_CTX *ctx) {
  // Only 128 bit keys with 32 bit tag lengths are approved for AES-CCM.
  if(EVP_AEAD_key_length(ctx->aead) == 16 && ctx->tag_len == 4) {
    FIPS_service_indicator_update_state();
  }
}

#else

uint64_t FIPS_service_indicator_before_call(void) { return 0; }
uint64_t FIPS_service_indicator_after_call(void) { return 0; }


// Service indicator check functions listed below are optimized to not do extra
// checks, when not in FIPS mode. Arguments must be cast to void to avoid
// unused warnings.

int FIPS_service_indicator_check_approved(int before, int after) {
  (void)before;
  (void)after;
  return AWSLC_APPROVED;
}

void AES_verify_service_indicator(const EVP_CIPHER_CTX *ctx, const unsigned key_rounds) {
  (void)ctx;
  (void)key_rounds;
}

void AEAD_GCM_verify_service_indicator(const EVP_AEAD_CTX *ctx) {
  (void)ctx;
}

void AEAD_CCM_verify_service_indicator(const EVP_AEAD_CTX *ctx) {
  (void)ctx;
}

#endif // AWSLC_FIPS



