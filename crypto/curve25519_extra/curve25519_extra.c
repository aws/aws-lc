// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "../fipsmodule/service_indicator/internal.h"
#include "../fipsmodule/curve25519/internal.h"
#include "internal.h"

int ED25519ctx_sign(uint8_t out_sig[ED25519_SIGNATURE_LEN],
                    const uint8_t *message, size_t message_len,
                    const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
                    const uint8_t *context, size_t context_len) {
  FIPS_service_indicator_lock_state();
  boringssl_ensure_eddsa_self_test();
  int res = ED25519ctx_sign_no_self_test(out_sig, message, message_len,
                                         private_key, context, context_len);
  FIPS_service_indicator_unlock_state();
  return res;
}

int ED25519ctx_sign_no_self_test(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    const uint8_t *context, size_t context_len) {
  return ed25519_sign_internal(ED25519CTX_ALG, out_sig, message, message_len,
                               private_key, context, context_len);
}

int ED25519ctx_verify(const uint8_t *message, size_t message_len,
                      const uint8_t signature[ED25519_SIGNATURE_LEN],
                      const uint8_t public_key[ED25519_PUBLIC_KEY_LEN],
                      const uint8_t *context, size_t context_len) {
  FIPS_service_indicator_lock_state();
  boringssl_ensure_eddsa_self_test();
  int res = ED25519ctx_verify_no_self_test(message, message_len, signature,
                                           public_key, context, context_len);
  FIPS_service_indicator_unlock_state();
  return res;
}

int ED25519ctx_verify_no_self_test(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN], const uint8_t *context,
    size_t context_len) {
  return ed25519_verify_internal(ED25519CTX_ALG, message, message_len,
                                 signature, public_key, context, context_len);
}

int ED25519ph_sign(uint8_t out_sig[ED25519_SIGNATURE_LEN],
                   const uint8_t *message, size_t message_len,
                   const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
                   const uint8_t *context, size_t context_len) {
  FIPS_service_indicator_lock_state();
  boringssl_ensure_hasheddsa_self_test();
  int res = ED25519ph_sign_no_self_test(out_sig, message, message_len,
                                        private_key, context, context_len);
  FIPS_service_indicator_unlock_state();
  if (res) {
    FIPS_service_indicator_update_state();
  }
  return res;
}

int ED25519ph_sign_no_self_test(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    const uint8_t *context, size_t context_len) {
  uint8_t digest[SHA512_DIGEST_LENGTH] = {0};
  SHA512_CTX ctx;
  SHA512_Init(&ctx);
  SHA512_Update(&ctx, message, message_len);
  SHA512_Final(digest, &ctx);
  return ED25519ph_sign_digest_no_self_test(out_sig, digest, private_key,
                                            context, context_len);
}

int ED25519ph_sign_digest(uint8_t out_sig[ED25519_SIGNATURE_LEN],
                          const uint8_t digest[SHA512_DIGEST_LENGTH],
                          const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
                          const uint8_t *context, size_t context_len) {
  FIPS_service_indicator_lock_state();
  boringssl_ensure_hasheddsa_self_test();
  int res = ED25519ph_sign_digest_no_self_test(out_sig, digest, private_key,
                                               context, context_len);
  FIPS_service_indicator_unlock_state();
  if (res) {
    FIPS_service_indicator_update_state();
  }
  return res;
}

int ED25519ph_sign_digest_no_self_test(
    uint8_t out_sig[ED25519_SIGNATURE_LEN],
    const uint8_t digest[SHA512_DIGEST_LENGTH],
    const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    const uint8_t *context, size_t context_len) {
  return ed25519_sign_internal(ED25519PH_ALG, out_sig, digest,
                               SHA512_DIGEST_LENGTH, private_key, context,
                               context_len);
}

int ED25519ph_verify(const uint8_t *message, size_t message_len,
                     const uint8_t signature[ED25519_SIGNATURE_LEN],
                     const uint8_t public_key[ED25519_PUBLIC_KEY_LEN],
                     const uint8_t *context, size_t context_len) {
  FIPS_service_indicator_lock_state();
  boringssl_ensure_hasheddsa_self_test();
  int res = ED25519ph_verify_no_self_test(message, message_len, signature,
                                          public_key, context, context_len);
  FIPS_service_indicator_unlock_state();
  if (res) {
    FIPS_service_indicator_update_state();
  }
  return res;
}

int ED25519ph_verify_no_self_test(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN], const uint8_t *context,
    size_t context_len) {
  uint8_t digest[SHA512_DIGEST_LENGTH] = {0};
  SHA512_CTX ctx;
  SHA512_Init(&ctx);
  SHA512_Update(&ctx, message, message_len);
  SHA512_Final(digest, &ctx);
  return ED25519ph_verify_digest_no_self_test(digest, signature, public_key,
                                              context, context_len);
}

int ED25519ph_verify_digest(const uint8_t digest[SHA512_DIGEST_LENGTH],
                            const uint8_t signature[ED25519_SIGNATURE_LEN],
                            const uint8_t public_key[ED25519_PUBLIC_KEY_LEN],
                            const uint8_t *context, size_t context_len) {
  FIPS_service_indicator_lock_state();
  boringssl_ensure_hasheddsa_self_test();
  int res = ED25519ph_verify_digest_no_self_test(
      digest, signature, public_key, context, context_len);
  FIPS_service_indicator_unlock_state();
  if(res) {
    FIPS_service_indicator_update_state();
  }
  return res;
}

int ED25519ph_verify_digest_no_self_test(
    const uint8_t digest[SHA512_DIGEST_LENGTH],
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN], const uint8_t *context,
    size_t context_len) {
  return ed25519_verify_internal(ED25519PH_ALG, digest,
                                 SHA512_DIGEST_LENGTH, signature, public_key,
                                 context, context_len);
}
