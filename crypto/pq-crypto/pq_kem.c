// -----------------------------------------------------------------------------
// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// KEM Library
// Abstract: Post-Quantum Algorithm API
// -----------------------------------------------------------------------------

#include "pq_kem.h"
#include "pq_kem_params_size.h"
#include <openssl/P434_api.h>
#include "openssl/mem.h"

EVP_PQ_KEM_CTX *EVP_PQ_KEM_CTX_new(void) {
  return OPENSSL_malloc(sizeof(EVP_PQ_KEM_CTX));
}

int EVP_PQ_KEM_CTX_init(EVP_PQ_KEM_CTX *kem_ctx, const EVP_PQ_KEM *kem) {

  if (kem_ctx == NULL || kem == NULL) {
    return 0;
  }

  kem_ctx->kem = kem;

  kem_ctx->public_key    = OPENSSL_malloc(kem->public_key_length);
  kem_ctx->private_key   = OPENSSL_malloc(kem->private_key_length);
  kem_ctx->ciphertext    = OPENSSL_malloc(kem->ciphertext_length);
  kem_ctx->shared_secret = OPENSSL_malloc(kem->shared_secret_length);

  if (kem_ctx->public_key == NULL || kem_ctx->private_key == NULL ||
      kem_ctx->ciphertext == NULL || kem_ctx->shared_secret == NULL) {
    EVP_PQ_KEM_CTX_free(kem_ctx);
    return 0;
  }

  return 1;
}

void EVP_PQ_KEM_CTX_free(EVP_PQ_KEM_CTX *kem_ctx) {
  if (kem_ctx != NULL) {
    OPENSSL_free(kem_ctx->public_key);
    OPENSSL_free(kem_ctx->private_key);
    OPENSSL_free(kem_ctx->ciphertext);
    OPENSSL_free(kem_ctx->shared_secret);
    OPENSSL_free(kem_ctx);
  }
}
#include <stdio.h>
int EVP_PQ_KEM_generate_keypair(EVP_PQ_KEM_CTX *kem_ctx) {

  if (kem_ctx == NULL ||
      kem_ctx->kem == NULL ||
      kem_ctx->public_key == NULL ||
      kem_ctx->private_key == NULL ||
      kem_ctx->kem->generate_keypair == NULL) {
    return 0;
  }

  int ret = kem_ctx->kem->generate_keypair(kem_ctx->public_key,
                                           kem_ctx->private_key);
  // PQ KEM APIs defined by NIST return 0 on success.
  return (ret == 0 ? 1 : 0);
}

int EVP_PQ_KEM_encapsulate(EVP_PQ_KEM_CTX *kem_ctx) {

  if (kem_ctx == NULL ||
      kem_ctx->kem == NULL ||
      kem_ctx->public_key == NULL ||
      kem_ctx->ciphertext == NULL ||
      kem_ctx->shared_secret == NULL ||
      kem_ctx->kem->encapsulate == NULL) {
    return 0;
  }

  int ret = kem_ctx->kem->encapsulate(kem_ctx->ciphertext,
                                      kem_ctx->shared_secret,
                                      kem_ctx->public_key);
  // PQ KEM APIs defined by NIST return 0 on success.
  return (ret == 0 ? 1 : 0);
}

int EVP_PQ_KEM_decapsulate(EVP_PQ_KEM_CTX *kem_ctx) {

  if (kem_ctx == NULL ||
      kem_ctx->kem == NULL ||
      kem_ctx->private_key == NULL ||
      kem_ctx->ciphertext == NULL ||
      kem_ctx->shared_secret == NULL ||
      kem_ctx->kem->decapsulate == NULL) {
    return 0;
  }

  int ret = kem_ctx->kem->decapsulate(kem_ctx->shared_secret,
                                      kem_ctx->ciphertext,
                                      kem_ctx->private_key);
  // PQ KEM APIs defined by NIST return 0 on success.
  return (ret == 0 ? 1 : 0);
}

// Definitions of KEM specific EVP_PQ_KEM structs.
const EVP_PQ_KEM EVP_PQ_KEM_sike_p434_r3 = {
  .name = "SIKEp434r3-KEM",

  .public_key_length    = SIKE_P434_R3_PUBLIC_KEY_BYTES,
  .private_key_length   = SIKE_P434_R3_PRIVATE_KEY_BYTES,
  .ciphertext_length    = SIKE_P434_R3_CIPHERTEXT_BYTES,
  .shared_secret_length = SIKE_P434_R3_SHARED_SECRET_BYTES,

  .generate_keypair = crypto_kem_keypair_SIKEp434,
  .encapsulate      = crypto_kem_enc_SIKEp434,
  .decapsulate      = crypto_kem_dec_SIKEp434,
};
