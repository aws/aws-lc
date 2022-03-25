// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/crypto.h>
#include <openssl/service_indicator.h>
#include "internal.h"

const char* awslc_version_string(void) {
  return AWSLC_VERSION_STRING;
}

int is_fips_build(void) {
#if defined(AWSLC_FIPS)
  return 1;
#else
  return 0;
#endif
}

#if defined(AWSLC_FIPS)

// FIPS 140-3 requires that the module should provide the service indicator
// for approved services irrespective of whether the user queries it or not.
// Hence, it is lazily initialized in any call to an approved service.
static struct fips_service_indicator_state * FIPS_service_indicator_get(void) {
  struct fips_service_indicator_state *indicator = CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);
  if (indicator == NULL) {
    indicator = OPENSSL_malloc(sizeof(struct fips_service_indicator_state));
    if (indicator == NULL) {
      OPENSSL_PUT_ERROR(CRYPTO, ERR_R_MALLOC_FAILURE);
      return NULL;
    }
    indicator->lock_state = STATE_UNLOCKED;
    indicator->counter = 0;
    if (!CRYPTO_set_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE, indicator, OPENSSL_free)) {
      OPENSSL_PUT_ERROR(CRYPTO, ERR_R_INTERNAL_ERROR);
      return NULL;
    }
  }
  return indicator;
}

static uint64_t FIPS_service_indicator_get_counter(void) {
  struct fips_service_indicator_state *indicator = FIPS_service_indicator_get();
  if (indicator == NULL) {
    return 0;
  }
  return indicator->counter;
}

uint64_t FIPS_service_indicator_before_call(void) {
  return FIPS_service_indicator_get_counter();
}

uint64_t FIPS_service_indicator_after_call(void) {
  return FIPS_service_indicator_get_counter();
}

int FIPS_service_indicator_check_approved(uint64_t before, uint64_t after) {
  if(before != after) {
    return AWSLC_APPROVED;
  }
  return AWSLC_NOT_APPROVED;
}

// |FIPS_service_indicator_update_state|, |FIPS_service_indicator_lock_state|
// and |FIPS_service_indicator_unlock_state| should not under/overflow in normal
// operation. They are still checked and errors added to facilitate testing in
// service_indicator_test.cc This should only happen if lock/unlock are called
// in an incorrect order or multiple times in the same function.
void FIPS_service_indicator_update_state(void) {
  struct fips_service_indicator_state *indicator = FIPS_service_indicator_get();
  if (indicator == NULL) {
    return;
  }

  if(indicator->lock_state == STATE_UNLOCKED) {
    if(indicator->counter + 1 > indicator->counter) {
      indicator->counter++;
    } else {
      OPENSSL_PUT_ERROR(CRYPTO, ERR_R_OVERFLOW);
    }
  }
}

void FIPS_service_indicator_lock_state(void) {
  struct fips_service_indicator_state *indicator = FIPS_service_indicator_get();
  if (indicator == NULL) {
    return;
  }

  if (indicator->lock_state + 1 > indicator->lock_state) {
    indicator->lock_state++;
  } else {
    OPENSSL_PUT_ERROR(CRYPTO, ERR_R_OVERFLOW);
  }
}

void FIPS_service_indicator_unlock_state(void) {
  struct fips_service_indicator_state *indicator = FIPS_service_indicator_get();
  if (indicator == NULL) {
    return;
  }

  if (indicator->lock_state > 0) {
    indicator->lock_state--;
  } else {
    OPENSSL_PUT_ERROR(CRYPTO, ERR_R_OVERFLOW);
  }
}

void AES_verify_service_indicator(const EVP_CIPHER_CTX *ctx, const unsigned key_rounds) {
  if(ctx != NULL) {
    switch(EVP_CIPHER_CTX_nid(ctx)) {
      case NID_aes_128_ecb:
      case NID_aes_192_ecb:
      case NID_aes_256_ecb:

      case NID_aes_128_cbc:
      case NID_aes_192_cbc:
      case NID_aes_256_cbc:

      case NID_aes_128_ctr:
      case NID_aes_192_ctr:
      case NID_aes_256_ctr:
        FIPS_service_indicator_update_state();
        break;
      default:
        break;
    }
  } else {
    // hwaes_capable when enabled in x86 uses 9, 11, 13 for key rounds.
    // hwaes_capable when enabled in ARM uses 10, 12, 14 for key rounds.
    // When compiling with different ARM specific platforms, 9, 11, 13 are used
    // for key rounds.
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
  // We only have support for 128 bit and 256 bit keys for AES-GCM. AES-GCM is
  // approved only with an internal IV, see SP 800-38D Sec 8.2.2.
  // Not the best way to write this, but the delocate parser for ARM/clang can't
  // recognize || if statements, or switch statements for this.
  // TODO: Update the delocate parser to be able to recognize a more readable
  // version of this.
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

void EVP_PKEY_keygen_verify_service_indicator(const EVP_PKEY *pkey) {
   int ret = 0;
   if(pkey->type == EVP_PKEY_RSA || pkey->type== EVP_PKEY_RSA_PSS) {
     //  2048, 3072 and 4096 bit keys are approved for RSA key generation.
     switch (EVP_PKEY_size(pkey)) {
       case 256:
       case 384:
       case 512:
         ret = 1;
         break;
       default:
         break;
     }
  } else if(pkey->type == EVP_PKEY_EC) {
      // Curves P-224, P-256, P-384 and P-521 keys are approved for EC key
      // generation.
     int curve_name = EC_GROUP_get_curve_name(pkey->pkey.ec->group);
     switch (curve_name) {
       case NID_secp224r1:
       case NID_X9_62_prime256v1:
       case NID_secp384r1:
       case NID_secp521r1:
         ret = 1;
         break;
       default:
         break;
     }
   }
   if(ret) {
     FIPS_service_indicator_update_state();
   }
}

void DigestSign_verify_service_indicator(const EVP_MD_CTX *ctx) {
  if(ctx->pctx->pmeth->pkey_id == EVP_PKEY_RSA ||
      ctx->pctx->pmeth->pkey_id == EVP_PKEY_RSA_PSS) {
    // Hash digest used in the private key should be of the same type.
    const EVP_MD *pctx_md;
    if(EVP_PKEY_CTX_get_signature_md(ctx->pctx, &pctx_md) &&
        (EVP_MD_CTX_md(ctx)->type != pctx_md->type)) {
      return;
    }
    // SHA1 and 1024 bit keys are not approved for RSA signature generation.
    // SHA2-224, SHA2-256, SHA2-384, SHA2-512 with 2048, 3072 and 4096 bit keys
    // are approved for signature generation.
    if (EVP_PKEY_size(ctx->pctx->pkey) == 256 ||
        EVP_PKEY_size(ctx->pctx->pkey) == 384 ||
        EVP_PKEY_size(ctx->pctx->pkey) == 512) {
      switch (ctx->digest->type) {
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
  } else if(ctx->pctx->pmeth->pkey_id == EVP_PKEY_EC){
    // Not the best way to write this, but the delocate parser for ARM/clang
    // can't recognize || if statements for this. Moving the curve check before
    // the digest check also causes delocate parser failures.
    // TODO: Update the delocate parser to be able to recognize a more readable
    // version of this.
    //
    // SHA1 is not approved for ECDSA signature generation.
    // Curves P-224, P-256, P-384 and P-521 with SHA2-224, SHA2-256, SHA2-384
    // and SHA2-512 are approved for signature generation.
    int curve_name = EC_GROUP_get_curve_name(ctx->pctx->pkey->pkey.ec->group);
    switch (ctx->digest->type) {
        case NID_sha224:
        case NID_sha256:
        case NID_sha384:
        case NID_sha512:
          goto check_curve;
        default:
          return;
   }
   check_curve:
    switch(curve_name) {
        case NID_secp224r1:
        case NID_X9_62_prime256v1:
        case NID_secp384r1:
        case NID_secp521r1:
            FIPS_service_indicator_update_state();
            break;
        default:
          break;
    }
  }
}

void DigestVerify_verify_service_indicator(const EVP_MD_CTX *ctx) {
  if(ctx->pctx->pmeth->pkey_id == EVP_PKEY_RSA ||
      ctx->pctx->pmeth->pkey_id == EVP_PKEY_RSA_PSS) {
    // Hash digest used in the private key should be of the same type.
    const EVP_MD *pctx_md;
    if(EVP_PKEY_CTX_get_signature_md(ctx->pctx, &pctx_md) &&
        (EVP_MD_CTX_md(ctx)->type != pctx_md->type)) {
      return;
    }
    // SHA-1, SHA2-224, SHA2-256, SHA2-384, SHA2-512 with 1024, 2048, 3072 and
    // 4096 bit keys are approved for signature verification.
    if (EVP_PKEY_size(ctx->pctx->pkey) == 128 ||
        EVP_PKEY_size(ctx->pctx->pkey) == 256 ||
        EVP_PKEY_size(ctx->pctx->pkey) == 384 ||
        EVP_PKEY_size(ctx->pctx->pkey) == 512) {
      switch (ctx->digest->type) {
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
  } else if(ctx->pctx->pmeth->pkey_id == EVP_PKEY_EC) {
    // Not the best way to write this, but the delocate parser for ARM/clang
    // can't recognize || if statements for this. Moving the curve check before
    // the digest check also causes delocate parser failures.
    // TODO: Update the delocate parser to be able to recognize a more readable
    // version of this.
    //
    // Curves P-224, P-256, P-384 and P-521 with SHA-1, SHA2-224, SHA2-256,
    // SHA2-384 and SHA2-512 are approved for signature verification.
    int curve_name = EC_GROUP_get_curve_name(ctx->pctx->pkey->pkey.ec->group);
    switch (ctx->digest->type) {
        case NID_sha1:
        case NID_sha224:
        case NID_sha256:
        case NID_sha384:
        case NID_sha512:
          goto check_curve;
        default:
          return;
   }
   check_curve:
    switch(curve_name) {
        case NID_secp224r1:
        case NID_X9_62_prime256v1:
        case NID_secp384r1:
        case NID_secp521r1:
            FIPS_service_indicator_update_state();
            break;
        default:
          break;
    }
  }
}

void ECDH_verify_service_indicator(const EC_KEY *ec_key) {
  // ECDH with curves P-224, P-256, P-384 and P-521 is approved.
  // Not the best way to write this, but the delocate parser for ARM/clang can't
  // recognize || if statements, or switch statements for this.
  // TODO: Update the delocate parser to be able to recognize a more readable
  // version of this.
  int curve = ec_key->group->curve_name;
  if(curve == NID_secp224r1) {
    FIPS_service_indicator_update_state();
  }
  else if( curve == NID_X9_62_prime256v1) {
    FIPS_service_indicator_update_state();
  }
  else if(curve == NID_secp384r1) {
    FIPS_service_indicator_update_state();
  }
  else if(curve == NID_secp521r1) {
    FIPS_service_indicator_update_state();
  }
}


void TLSKDF_verify_service_indicator(const EVP_MD *dgst) {
  // HMAC-MD5, HMAC-SHA1, and HMAC-MD5/HMAC-SHA1 (both used concurrently) are
  // approved for use in the KDF in TLS 1.0/1.1.
  // HMAC-SHA{256, 384, 512} are approved for use in the KDF in TLS 1.2.
  // These Key Derivation functions are to be used in the context of the TLS
  // protocol.
  switch (dgst->type){
    case NID_md5:
    case NID_sha1:
    case NID_md5_sha1:
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


// Service indicator check functions listed below are optimized to not do extra
// checks, when not in FIPS mode. Arguments are cast with |OPENSSL_UNUSED| in an
// attempt to avoid unused warnings.

int FIPS_service_indicator_check_approved(OPENSSL_UNUSED uint64_t before,
                                          OPENSSL_UNUSED uint64_t after) {
  return AWSLC_APPROVED;
}

void AES_verify_service_indicator(OPENSSL_UNUSED const EVP_CIPHER_CTX *ctx,
                                  OPENSSL_UNUSED const unsigned key_rounds) { }

void AEAD_GCM_verify_service_indicator(OPENSSL_UNUSED const EVP_AEAD_CTX *ctx) { }

void AEAD_CCM_verify_service_indicator(OPENSSL_UNUSED const EVP_AEAD_CTX *ctx) { }

void AES_CMAC_verify_service_indicator(OPENSSL_UNUSED const CMAC_CTX *ctx) { }

void HMAC_verify_service_indicator(OPENSSL_UNUSED const EVP_MD *evp_md) { }

void EVP_PKEY_keygen_verify_service_indicator(OPENSSL_UNUSED const EVP_PKEY *pkey) { }

void DigestSign_verify_service_indicator(OPENSSL_UNUSED const EVP_MD_CTX *ctx) { }

void DigestVerify_verify_service_indicator(OPENSSL_UNUSED const EVP_MD_CTX *ctx) { }

void ECDH_verify_service_indicator(OPENSSL_UNUSED const EC_KEY *ec_key) { }

void TLSKDF_verify_service_indicator(OPENSSL_UNUSED const EVP_MD *dgst) { }

#endif // AWSLC_FIPS
