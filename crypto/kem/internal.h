// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_HEADER_KEM_INTERNAL_H
#define AWSLC_HEADER_KEM_INTERNAL_H

#include <openssl/base.h>


#if defined(__cplusplus)
extern "C" {
#endif

// KEM_METHOD structure and helper functions.
typedef struct {
  int (*keygen)(uint8_t *public_key,
                uint8_t *secret_key);

  int (*encaps)(uint8_t *ciphertext,
                uint8_t *shared_secret,
                const uint8_t *public_key);

  int (*decaps)(uint8_t *shared_secret,
                const uint8_t *ciphertext,
                const uint8_t *secret_key);
} KEM_METHOD;

const KEM_METHOD *KEM_kyber512_method(void);
// const KEM_METHOD *KEM_kyber768_method(void);

// KEM structure and helper functions.
typedef struct {
  int nid;
  const uint8_t *oid;
  uint8_t oid_len;
  const char *comment;
  size_t public_key_len;
  size_t secret_key_len;
  size_t ciphertext_len;
  size_t shared_secret_len;
  const KEM_METHOD *method;
} KEM;

#define AWSLC_NUM_BUILT_IN_KEMS 1

struct built_in_kems {
  KEM kems[AWSLC_NUM_BUILT_IN_KEMS];
};

const struct built_in_kems *AWSLC_built_in_kems(void);
const KEM *KEM_find_kem_by_nid(int nid);

// KEM_KEY structure and helper functions.
struct kem_key_st {
  const KEM *kem;
  uint8_t *public_key;
  uint8_t *secret_key;
  uint8_t has_secret_key;
};

KEM_KEY *KEM_KEY_new(void);
int KEM_KEY_init(KEM_KEY *key, const KEM *kem);
void KEM_KEY_free(KEM_KEY *key);
const KEM *KEM_KEY_get0_kem(KEM_KEY* key);

// KEM_KEY_set_raw_public_key function allocates the public key buffer
// within the given |key| and copies the contents of |in| to it.
//
// NOTE: No checks are done in this function, the caller has to ensure that
//       the pointers are valid and buffers sizes are correct.
int KEM_KEY_set_raw_public_key(KEM_KEY *key, const uint8_t *in);

// KEM_KEY_set_raw_secret_key function allocates the secret key buffer
// within the given |key| and copies the contents of |in| to it.
//
// NOTE: No checks are done in this function, the caller has to ensure that
//       the pointers are valid and buffers sizes are correct.
int KEM_KEY_set_raw_secret_key(KEM_KEY *key, const uint8_t *in);

// KEM_KEY_set_raw_key function allocates the public and secret key buffers
// within the given |key| and copies the contents of |in_public| and
// |in_secret| to them.
//
// NOTE: No checks are done in this function, the caller has to ensure that
//       the pointers are valid and buffers sizes are correct.
int KEM_KEY_set_raw_key(KEM_KEY *key, const uint8_t *in_public,
                                      const uint8_t *in_secret);

#if defined(__cplusplus)
}  // extern C
#endif

#endif
