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
  struct fips_service_indicator_state *indicator =
    CRYPTO_get_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE);

  if (indicator == NULL) {

    indicator = OPENSSL_malloc(sizeof(struct fips_service_indicator_state));
    if (indicator == NULL) {
      OPENSSL_PUT_ERROR(CRYPTO, ERR_R_MALLOC_FAILURE);
      return NULL;
    }

    indicator->lock_state = STATE_UNLOCKED;
    indicator->counter = 0;

    if (!CRYPTO_set_thread_local(AWSLC_THREAD_LOCAL_FIPS_SERVICE_INDICATOR_STATE,
                                 indicator, OPENSSL_free)) {
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
  if (before != after) {
    return AWSLC_APPROVED;
  }
  return AWSLC_NOT_APPROVED;
}

void FIPS_service_indicator_update_state(void) {
  struct fips_service_indicator_state *indicator = FIPS_service_indicator_get();
  if (indicator == NULL) {
    return;
  }

  if (indicator->lock_state == STATE_UNLOCKED) {
    indicator->counter++;
  }
}

// |FIPS_service_indicator_lock_state| and |FIPS_service_indicator_unlock_state|
// should not under/overflow in normal operation. They are still checked and
// errors added to facilitate testing in service_indicator_test.cc This should
// only happen if lock/unlock are called in an incorrect order or multiple times
// in the same function.
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

void AES_verify_service_indicator(const EVP_CIPHER_CTX *ctx,
                                  const unsigned key_rounds) {
  if (ctx != NULL) {
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
  // Note: |EVP_AEAD_key_length| returns the length in bytes.
  size_t key_len = EVP_AEAD_key_length(ctx->aead);
  if (key_len == 16 || key_len == 32) {
    FIPS_service_indicator_update_state();
  }
}

void AEAD_CCM_verify_service_indicator(const EVP_AEAD_CTX *ctx) {
  // Only 128 bit keys with 32 bit tag lengths are approved for AES-CCM.
  // Note: |EVP_AEAD_key_length| returns the length in bytes.
  if (EVP_AEAD_key_length(ctx->aead) == 16 && ctx->tag_len == 4) {
    FIPS_service_indicator_update_state();
  }
}

void AES_CMAC_verify_service_indicator(const CMAC_CTX *ctx) {
  // Only 128 and 256 bit keys are approved for AES-CMAC.
  // Note: |key_len| is the length in bytes.
  size_t key_len = ctx->cipher_ctx.key_len;
  if (key_len == 16 || key_len == 32) {
    FIPS_service_indicator_update_state();
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

// Returns 1 if the curve corresponding to the given NID is FIPS approved, and
// 0 otherwise. Only P-224, P-256, P-384, and P-521 curves are FIPS approved.
static int is_ec_fips_approved(int curve_nid) {
  switch (curve_nid) {
    case NID_secp224r1:
    case NID_X9_62_prime256v1:
    case NID_secp384r1:
    case NID_secp521r1:
      return 1;
    default:
      return 0;
  }
}

// Updates the service indicator if the elliptic curve contained in |eckey|
// is FIPS approved, otherwise does nothing.
void EC_KEY_keygen_verify_service_indicator(EC_KEY *eckey) {
  int curve_nid = EC_GROUP_get_curve_name(eckey->group);
  if (is_ec_fips_approved(curve_nid)) {
    FIPS_service_indicator_update_state();
  }
}

void EVP_PKEY_keygen_verify_service_indicator(const EVP_PKEY *pkey) {
  if (pkey->type == EVP_PKEY_RSA || pkey->type== EVP_PKEY_RSA_PSS) {
    // 2048, 3072 and 4096 bit keys are approved for RSA key generation.
    // EVP_PKEY_size returns the size of the key in bytes.
    // Note: |EVP_PKEY_size| returns the length in bytes.
    size_t key_size = EVP_PKEY_size(pkey);
    switch (key_size) {
      case 256:
      case 384:
      case 512:
        FIPS_service_indicator_update_state();
        break;
      default:
        break;
    }
  } else if (pkey->type == EVP_PKEY_EC) {
    // Note: even though the function is called |EC_GROUP_get_curve_name|
    // it actually returns the NID of the curve rather than the name.
    int curve_nid = EC_GROUP_get_curve_name(pkey->pkey.ec->group);
    if (is_ec_fips_approved(curve_nid)) {
      FIPS_service_indicator_update_state();
    }
  }
}

// Returns 1 if the given message digest type is FIPS approved for signing, and
// 0 otherwise. Only SHA2-224, SHA2-256, SHA2-384, and SHA2-512 are approved.
static int is_md_fips_approved_for_signing(int md_type) {
  switch (md_type) {
    case NID_sha224:
    case NID_sha256:
    case NID_sha384:
    case NID_sha512:
      return 1;
    default:
      return 0;
  }
}

void DigestSign_verify_service_indicator(const EVP_MD_CTX *ctx) {
  int pkey_type = ctx->pctx->pmeth->pkey_id;

  if (pkey_type == EVP_PKEY_RSA || pkey_type == EVP_PKEY_RSA_PSS) {
    // Message digest used in the private key should be of the same type
    // as the given one, so we extract the MD type from the private key
    // and compare it with the type in |ctx|.
    const EVP_MD *pctx_md;
    if (!EVP_PKEY_CTX_get_signature_md(ctx->pctx, &pctx_md)) {
      OPENSSL_PUT_ERROR(CRYPTO, ERR_R_INTERNAL_ERROR);
      return;
    }
    int md_type = EVP_MD_CTX_type(ctx);
    if (pctx_md->type != md_type) {
      return;
    }

    // The approved RSA key sizes for signing are 2048, 3072 and 4096 bits.
    // Note: |EVP_PKEY_size| returns the size in bytes.
    size_t pkey_size = EVP_PKEY_size(ctx->pctx->pkey);

    // Check if the MD type and the RSA key size are approved.
    if (is_md_fips_approved_for_signing(md_type) &&
        (pkey_size == 256 || pkey_size == 384 || pkey_size == 512)) {

      FIPS_service_indicator_update_state();
    }
  } else if (pkey_type == EVP_PKEY_EC) {
    int md_type = EVP_MD_CTX_type(ctx);
    // Note: even though the function is called |EC_GROUP_get_curve_name|
    // it actually returns the NID of the curve rather than the name.
    int curve_nid = EC_GROUP_get_curve_name(ctx->pctx->pkey->pkey.ec->group);

    // Check if the MD type and the elliptic curve are approved.
    if (is_md_fips_approved_for_signing(md_type) &&
        is_ec_fips_approved(curve_nid)) {
      FIPS_service_indicator_update_state();
    }
  }
}

// Returns 1 if the given message digest type is FIPS approved for verifying,
// and 0 otherwise. Only SHA1, SHA2-224, SHA2-256, SHA2-384, and SHA2-512
// are approved.
static int is_md_fips_approved_for_verifying(int md_type) {
  switch (md_type) {
    case NID_sha1:
    case NID_sha224:
    case NID_sha256:
    case NID_sha384:
    case NID_sha512:
      return 1;
    default:
      return 0;
  }
}

void DigestVerify_verify_service_indicator(const EVP_MD_CTX *ctx) {
  int pkey_type = ctx->pctx->pmeth->pkey_id;

  if (pkey_type == EVP_PKEY_RSA || pkey_type == EVP_PKEY_RSA_PSS) {
    // Message digest used in the private key should be of the same type
    // as the given one, so we extract the MD type from the private key
    // and compare it with the type in |ctx|.
    const EVP_MD *pctx_md;
    if (!EVP_PKEY_CTX_get_signature_md(ctx->pctx, &pctx_md)) {
      OPENSSL_PUT_ERROR(CRYPTO, ERR_R_INTERNAL_ERROR);
      return;
    }
    int md_type = EVP_MD_CTX_type(ctx);
    if (pctx_md->type != md_type) {
      return;
    }

    // The approved RSA key sizes for verifying are 1024, 2048, 3072, 4096 bits.
    // Note: |EVP_PKEY_size| returns the size in bytes.
    size_t pkey_size = EVP_PKEY_size(ctx->pctx->pkey);

    // Check if the MD type and the RSA key size are approved.
    if (is_md_fips_approved_for_verifying(md_type) &&
        (pkey_size == 128 || pkey_size == 256 ||
         pkey_size == 384 || pkey_size == 512)) {

      FIPS_service_indicator_update_state();
    }
  } else if (pkey_type == EVP_PKEY_EC) {
    int md_type = EVP_MD_CTX_type(ctx);
    // Note: even though the function is called |EC_GROUP_get_curve_name|
    // it actually returns the NID of the curve rather than the name.
    int curve_nid = EC_GROUP_get_curve_name(ctx->pctx->pkey->pkey.ec->group);

    // Check if the MD type and the elliptic curve are approved.
    if (is_md_fips_approved_for_verifying(md_type) &&
        is_ec_fips_approved(curve_nid)) {
      FIPS_service_indicator_update_state();
    }
  }
}

void ECDH_verify_service_indicator(const EC_KEY *ec_key) {
  int curve_nid = ec_key->group->curve_name;

  if (is_ec_fips_approved(curve_nid)) {
    FIPS_service_indicator_update_state();
  }
}


void TLSKDF_verify_service_indicator(const EVP_MD *dgst) {
  // HMAC-MD5, HMAC-SHA1, and HMAC-MD5/HMAC-SHA1 (both used concurrently) are
  // approved for use in the KDF in TLS 1.0/1.1.
  // HMAC-SHA{256, 384, 512} are approved for use in the KDF in TLS 1.2.
  // These Key Derivation functions are to be used in the context of the TLS
  // protocol.
  switch (dgst->type) {
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

void EC_KEY_keygen_verify_service_indicator(OPENSSL_UNUSED EC_KEY *eckey) { }

#endif // AWSLC_FIPS
