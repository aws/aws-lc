// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/err.h>
#include <openssl/mem.h>
#include <openssl/nid.h>

#include "../fipsmodule/delocate.h"
#include "../internal.h"
#include "internal.h"

#define AWSLC_NUM_BUILT_IN_KEMS 1

// TODO(awslc): placeholder OID, replace with the real one when available.
static const uint8_t kOIDKyber512[] = {0xff, 0xff, 0xff, 0xff};

static const KEM built_in_kems[AWSLC_NUM_BUILT_IN_KEMS] = {
  {
    NID_KYBER512,         // kem.nid
    kOIDKyber512,         // kem.oid
    sizeof(kOIDKyber512), // kem.oid_len
    "Kyber512",           // kem.comment
    800,                  // kem.public_key_len
    1632,                 // kem.secret_key_len
    768,                  // kem.ciphertext_len
    32,                   // kem.shared_secret_len
    &kem_kyber512_method, // kem.method
  },

  // Example how adding new KEM looks like:
  // {
  //   NID_KYBER768,         // kem.nid
  //   kOIDKyber768,         // kem.oid
  //   sizeof(kOIDKyber768), // kem.oid_len
  //   "Kyber7678,           // kem.comment
  //   1184,                 // kem.public_key_len
  //   2400,                 // kem.secret_key_len
  //   1088,                 // kem.ciphertext_len
  //   32,                   // kem.shared_secret_len
  //   &kem_kyber768_method, // kem.method
  // },
};

const KEM *KEM_find_kem_by_nid(int nid) {
  const KEM *ret = NULL;
  for (size_t i = 0; i < AWSLC_NUM_BUILT_IN_KEMS; i++) {
    if (built_in_kems[i].nid == nid) {
      ret = &built_in_kems[i];
      break;
    }
  }
  return ret;
}

KEM_KEY *KEM_KEY_new(void) {
  KEM_KEY *ret = OPENSSL_malloc(sizeof(KEM_KEY));
  if (ret == NULL) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_MALLOC_FAILURE);
    return NULL;
  }

  OPENSSL_memset(ret, 0, sizeof(KEM_KEY));
  return ret;
}

int KEM_KEY_init(KEM_KEY *key, const KEM *kem) {
  if (key == NULL || kem == NULL) {
    return 0;
  }
  // If the key is already initialized clear it.
  KEM_KEY_free(key);

  key->kem = kem;
  key->public_key = OPENSSL_malloc(kem->public_key_len);
  key->secret_key = OPENSSL_malloc(kem->secret_key_len);
  key->has_secret_key = 0;
  if (key->public_key == NULL || key->secret_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_MALLOC_FAILURE);
    KEM_KEY_free(key);
    return 0;
  }

  return 1;
}

void KEM_KEY_free(KEM_KEY *key) {
  if (key == NULL) {
    return;
  }
  key->kem = NULL;
  OPENSSL_free(key->public_key);
  OPENSSL_free(key->secret_key);
}

const KEM *KEM_KEY_get0_kem(KEM_KEY* key) {
  return key->kem;
}

int KEM_KEY_set_raw_public_key(KEM_KEY *key, const uint8_t *in) {
  key->public_key = OPENSSL_memdup(in, key->kem->public_key_len);
  if (key->public_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  return 1;
}

int KEM_KEY_set_raw_secret_key(KEM_KEY *key, const uint8_t *in) {
  key->secret_key = OPENSSL_memdup(in, key->kem->secret_key_len);
  if (key->secret_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_MALLOC_FAILURE);
    return 0;
  }
  key->has_secret_key = 1;

  return 1;
}

int KEM_KEY_set_raw_key(KEM_KEY *key, const uint8_t *in_public,
                                      const uint8_t *in_secret) {
  key->public_key = OPENSSL_memdup(in_public, key->kem->public_key_len);
  key->secret_key = OPENSSL_memdup(in_secret, key->kem->secret_key_len);
  if (key->public_key == NULL || key->secret_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_MALLOC_FAILURE);
    KEM_KEY_free(key);
    return 0;
  }
  key->has_secret_key = 1;

  return 1;
}
