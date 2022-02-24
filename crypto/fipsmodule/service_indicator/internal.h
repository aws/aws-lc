// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#ifndef AWSLC_HEADER_SERVICE_INDICATOR_INTERNAL_H
#define AWSLC_HEADER_SERVICE_INDICATOR_INTERNAL_H

#include <openssl/aead.h>
#include <openssl/service_indicator.h>

#if defined(AWSLC_FIPS)

#define STATE_UNLOCKED 0

struct fips_service_indicator_state {
  uint64_t lock_state;
  uint64_t counter;
};

// Only to be used internally, it is not intended for the user to update the
// state. This function is used to update the service indicator state, if the
// service is deemed to be approved.
void FIPS_service_indicator_update_state(void);

// Only to be used internally. Certain approved algorithms call upon other
// approved algorithms, and some services provide one-shot functions that call
// upon multiple functions that are approved themselves.
// These functions lock/unlock the counter state, so that nested calls of
// |FIPS_service_indicator_update_state| within don't update the counter
// unintentionally. The lock is implemented as a counter, as one-shot functions
// may call upon approved nested functions which have approved nested algorithms
// within them as well. The counter state can only be updated when the
// |lock_state| has a value of |STATE_UNLOCKED|.
// For the approval checks to work correctly, whenever
// |FIPS_service_indicator_lock_state| is called,
// |FIPS_service_indicator_unlock_state| must be called before exiting the
// function. This ensures that the counter is only updated when the most
// high level function that initially locked the state first, unlocks the
// |lock_state| back to |STATE_UNLOCKED|.
void FIPS_service_indicator_lock_state(void);
void FIPS_service_indicator_unlock_state(void);

#else

// Service indicator functions are not intended for use during non-FIPS mode.
// If these functions are run during non-FIPS mode, they will provide no
// operations.
OPENSSL_INLINE void FIPS_service_indicator_update_state(void) { }
OPENSSL_INLINE void FIPS_service_indicator_lock_state(void) { }
OPENSSL_INLINE void FIPS_service_indicator_unlock_state(void) { }

#endif // AWSLC_FIPS

// is_fips_build is similar to |FIPS_mode| but returns 1 including in the case
// of #if defined(OPENSSL_ASAN)
int is_fips_build(void);

// Service indicator check functions parameters are assumed to be not NULL.

void AES_verify_service_indicator(const EVP_CIPHER_CTX *ctx, const unsigned key_rounds);

void AEAD_GCM_verify_service_indicator(const EVP_AEAD_CTX *ctx);

void AEAD_CCM_verify_service_indicator(const EVP_AEAD_CTX *ctx);

void AES_CMAC_verify_service_indicator(const CMAC_CTX *ctx);

void HMAC_verify_service_indicator(const EVP_MD *evp_md);

void EVP_PKEY_keygen_verify_service_indicator(const EVP_PKEY *pkey);

void DigestSign_verify_service_indicator(const EVP_MD_CTX *ctx);

void DigestVerify_verify_service_indicator(const EVP_MD_CTX *ctx);

void ECDH_verify_service_indicator(const EC_KEY *ec_key);

void TLSKDF_verify_service_indicator(const EVP_MD *dgst);

#endif  // AWSLC_HEADER_SERVICE_INDICATOR_INTERNAL_H
