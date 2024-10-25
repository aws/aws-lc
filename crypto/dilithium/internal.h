// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_HEADER_SIG_INTERNAL_H
#define AWSLC_HEADER_SIG_INTERNAL_H

#include <openssl/base.h>

#if defined(__cplusplus)
extern "C" {
#endif

// NISTDSA_METHOD structure and helper functions.
typedef struct {
  int (*keygen)(uint8_t *public_key,
                uint8_t *secret_key);

  int (*sign)(uint8_t *sig, size_t *sig_len,
              const uint8_t *message,
              size_t message_len,
              const uint8_t *ctx,
              size_t ctx_len,
              const uint8_t *secret_key);

  int (*verify)(const uint8_t *message,
                size_t message_len,
                const uint8_t *sig,
                size_t sig_len,
                const uint8_t *ctx,
                size_t ctx_len,
                const uint8_t *public_key);

} NISTDSA_METHOD;

  // NISTDSA structure and helper functions.
typedef struct {
  int nid;
  const uint8_t *oid;
  uint8_t oid_len;
  const char *comment;
  size_t public_key_len;
  size_t secret_key_len;
  size_t signature_len;
  size_t keygen_seed_len;
  size_t sign_seed_len;
  const NISTDSA_METHOD *method;
  const EVP_PKEY_ASN1_METHOD *asn1_method;
} NISTDSA;

  // NISTDSA_KEY structure and helper functions.
struct nistdsa_st {
  const NISTDSA *nistdsa;
  uint8_t *public_key;
  uint8_t *secret_key;
};

int EVP_PKEY_CTX_nistdsa_set_params(EVP_PKEY_CTX *ctx, int nid);
int EVP_PKEY_nistdsa_set_params(EVP_PKEY *pkey, int nid);
int NISTDSA_KEY_init(NISTDSA_KEY *key, const NISTDSA *nistdsa);
const NISTDSA * SIG_find_dsa_by_nid(int nid);
const NISTDSA *NISTDSA_KEY_get0_sig(NISTDSA_KEY* key);
NISTDSA_KEY *NISTDSA_KEY_new(void);
void NISTDSA_KEY_free(NISTDSA_KEY *key);

#if defined(__cplusplus)
}  // extern C
#endif

#endif // AWSLC_HEADER_DSA_TEST_INTERNAL_H
