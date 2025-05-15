// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>

#include "../../kyber/kem_kyber.h"
#include "../delocate.h"
#include "../ml_kem/ml_kem.h"
#include "internal.h"

// https://csrc.nist.gov/projects/computer-security-objects-register/algorithm-registration
// 2.16.840.1.101.3.4.4.1
static const uint8_t kOIDMLKEM512[]  = {0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x01};
// 2.16.840.1.101.3.4.4.2
static const uint8_t kOIDMLKEM768[]  = {0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x02};
// 2.16.840.1.101.3.4.4.3
static const uint8_t kOIDMLKEM1024[] = {0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x03};

static int ml_kem_1024_keygen_deterministic(uint8_t *public_key,
                                            size_t *public_len,
                                            uint8_t *secret_key,
                                            size_t *secret_len,
                                            const uint8_t *seed) {
  return ml_kem_1024_keypair_deterministic(public_key, public_len, secret_key, secret_len, seed) == 0;
}

static int ml_kem_1024_keygen(uint8_t *public_key,
                              size_t *public_len,
                              uint8_t *secret_key,
                              size_t *secret_len) {
  return ml_kem_1024_keypair(public_key, public_len, secret_key, secret_len) == 0;
}

static int ml_kem_1024_encaps_deterministic(uint8_t *ciphertext,
                                            size_t *ciphertext_len,
                                            uint8_t *shared_secret,
                                            size_t *shared_secret_len,
                                            const uint8_t *public_key,
                                            const uint8_t *seed) {
  return ml_kem_1024_encapsulate_deterministic(ciphertext, ciphertext_len, shared_secret, shared_secret_len, public_key, seed) == 0;
}

static int ml_kem_1024_encaps(uint8_t *ciphertext,
                              size_t *ciphertext_len,
                              uint8_t *shared_secret,
                              size_t *shared_secret_len,
                              const uint8_t *public_key) {
  return ml_kem_1024_encapsulate(ciphertext, ciphertext_len, shared_secret, shared_secret_len, public_key) == 0;
}

static int ml_kem_1024_decaps(uint8_t *shared_secret,
                              size_t *shared_secret_len,
                              const uint8_t *ciphertext,
                              const uint8_t *secret_key) {
  return ml_kem_1024_decapsulate(shared_secret, shared_secret_len, ciphertext, secret_key) == 0;
}

DEFINE_LOCAL_DATA(KEM_METHOD, kem_ml_kem_1024_method) {
  out->keygen_deterministic = ml_kem_1024_keygen_deterministic;
  out->keygen = ml_kem_1024_keygen;
  out->encaps_deterministic = ml_kem_1024_encaps_deterministic;
  out->encaps = ml_kem_1024_encaps;
  out->decaps = ml_kem_1024_decaps;
}

static int ml_kem_768_keygen_deterministic(uint8_t *public_key,
                                           size_t *public_len,
                                           uint8_t *secret_key,
                                           size_t *secret_len,
                                           const uint8_t *seed) {
  return ml_kem_768_keypair_deterministic(public_key, public_len, secret_key, secret_len, seed) == 0;
}

static int ml_kem_768_keygen(uint8_t *public_key,
                             size_t *public_len,
                             uint8_t *secret_key,
                             size_t *secret_len) {
  return ml_kem_768_keypair(public_key, public_len, secret_key, secret_len) == 0;
}

static int ml_kem_768_encaps_deterministic(uint8_t *ciphertext,
                                           size_t *ciphertext_len,
                                           uint8_t *shared_secret,
                                           size_t *shared_secret_len,
                                           const uint8_t *public_key,
                                           const uint8_t *seed) {
  return ml_kem_768_encapsulate_deterministic(ciphertext, ciphertext_len, shared_secret, shared_secret_len, public_key, seed) == 0;
}

static int ml_kem_768_encaps(uint8_t *ciphertext,
                             size_t *ciphertext_len,
                             uint8_t *shared_secret,
                             size_t *shared_secret_len,
                             const uint8_t *public_key) {
  return ml_kem_768_encapsulate(ciphertext, ciphertext_len, shared_secret, shared_secret_len, public_key) == 0;
}

static int ml_kem_768_decaps(uint8_t *shared_secret,
                             size_t *shared_secret_len,
                             const uint8_t *ciphertext,
                             const uint8_t *secret_key) {
  return ml_kem_768_decapsulate(shared_secret, shared_secret_len, ciphertext, secret_key) == 0;
}

DEFINE_LOCAL_DATA(KEM_METHOD, kem_ml_kem_768_method) {
  out->keygen_deterministic = ml_kem_768_keygen_deterministic;
  out->keygen = ml_kem_768_keygen;
  out->encaps_deterministic = ml_kem_768_encaps_deterministic;
  out->encaps = ml_kem_768_encaps;
  out->decaps = ml_kem_768_decaps;
}

static int ml_kem_512_keygen_deterministic(uint8_t *public_key,
                                           size_t *public_len,
                                           uint8_t *secret_key,
                                           size_t *secret_len,
                                           const uint8_t *seed) {
  return ml_kem_512_keypair_deterministic(public_key, public_len, secret_key, secret_len, seed) == 0;
}

static int ml_kem_512_keygen(uint8_t *public_key,
                             size_t *public_len,
                             uint8_t *secret_key,
                             size_t *secret_len) {
  return ml_kem_512_keypair(public_key, public_len, secret_key, secret_len) == 0;
}

static int ml_kem_512_encaps_deterministic(uint8_t *ciphertext,
                                           size_t *ciphertext_len,
                                           uint8_t *shared_secret,
                                           size_t *shared_secret_len,
                                           const uint8_t *public_key,
                                           const uint8_t *seed) {
  return ml_kem_512_encapsulate_deterministic(ciphertext, ciphertext_len, shared_secret, shared_secret_len, public_key, seed) == 0;
}

static int ml_kem_512_encaps(uint8_t *ciphertext,
                             size_t *ciphertext_len,
                             uint8_t *shared_secret,
                             size_t *shared_secret_len,
                             const uint8_t *public_key) {
  return ml_kem_512_encapsulate(ciphertext, ciphertext_len, shared_secret, shared_secret_len, public_key) == 0;
}

static int ml_kem_512_decaps(uint8_t *shared_secret,
                             size_t *shared_secret_len,
                             const uint8_t *ciphertext,
                             const uint8_t *secret_key) {
  return ml_kem_512_decapsulate(shared_secret, shared_secret_len, ciphertext, secret_key) == 0;
}

DEFINE_LOCAL_DATA(KEM_METHOD, kem_ml_kem_512_method) {
  out->keygen_deterministic = ml_kem_512_keygen_deterministic;
  out->keygen = ml_kem_512_keygen;
  out->encaps_deterministic = ml_kem_512_encaps_deterministic;
  out->encaps = ml_kem_512_encaps;
  out->decaps = ml_kem_512_decaps;
}

DEFINE_LOCAL_DATA(KEM, KEM_ml_kem_512) {
  out->nid = NID_MLKEM512;
  out->oid = kOIDMLKEM512;
  out->oid_len = sizeof(kOIDMLKEM512);
  out->comment = "MLKEM512 ";
  out->public_key_len = MLKEM512_PUBLIC_KEY_BYTES;
  out->secret_key_len = MLKEM512_SECRET_KEY_BYTES;
  out->ciphertext_len = MLKEM512_CIPHERTEXT_BYTES;
  out->shared_secret_len = MLKEM512_SHARED_SECRET_LEN;
  out->keygen_seed_len = MLKEM512_KEYGEN_SEED_LEN;
  out->encaps_seed_len = MLKEM512_ENCAPS_SEED_LEN;
  out->method = kem_ml_kem_512_method();
}

DEFINE_LOCAL_DATA(KEM, KEM_ml_kem_768) {
  out->nid = NID_MLKEM768;
  out->oid = kOIDMLKEM768;
  out->oid_len = sizeof(kOIDMLKEM768);
  out->comment = "MLKEM768 ";
  out->public_key_len = MLKEM768_PUBLIC_KEY_BYTES;
  out->secret_key_len = MLKEM768_SECRET_KEY_BYTES;
  out->ciphertext_len = MLKEM768_CIPHERTEXT_BYTES;
  out->shared_secret_len = MLKEM768_SHARED_SECRET_LEN;
  out->keygen_seed_len = MLKEM768_KEYGEN_SEED_LEN;
  out->encaps_seed_len = MLKEM768_ENCAPS_SEED_LEN;
  out->method = kem_ml_kem_768_method();
}

DEFINE_LOCAL_DATA(KEM, KEM_ml_kem_1024) {
  out->nid = NID_MLKEM1024;
  out->oid = kOIDMLKEM1024;
  out->oid_len = sizeof(kOIDMLKEM1024);
  out->comment = "MLKEM1024 ";
  out->public_key_len = MLKEM1024_PUBLIC_KEY_BYTES;
  out->secret_key_len = MLKEM1024_SECRET_KEY_BYTES;
  out->ciphertext_len = MLKEM1024_CIPHERTEXT_BYTES;
  out->shared_secret_len = MLKEM1024_SHARED_SECRET_LEN;
  out->keygen_seed_len = MLKEM1024_KEYGEN_SEED_LEN;
  out->encaps_seed_len = MLKEM1024_ENCAPS_SEED_LEN;
  out->method = kem_ml_kem_1024_method();
}

const KEM *KEM_find_kem_by_nid(int nid) {
  switch (nid) {
    case NID_MLKEM512:
      return KEM_ml_kem_512();
    case NID_MLKEM768:
      return KEM_ml_kem_768();
    case NID_MLKEM1024:
      return KEM_ml_kem_1024();
    // Try legacy KEMs.
    case NID_KYBER512_R3:
      return get_legacy_kem_kyber512_r3();
    case NID_KYBER768_R3:
      return get_legacy_kem_kyber768_r3();
    case NID_KYBER1024_R3:
      return get_legacy_kem_kyber1024_r3();
    default:
      return NULL;
  }
}

KEM_KEY *KEM_KEY_new(void) {
  KEM_KEY *ret = OPENSSL_zalloc(sizeof(KEM_KEY));
  if (ret == NULL) {
    return NULL;
  }

  return ret;
}

static void KEM_KEY_clear(KEM_KEY *key) {
  key->kem = NULL;
  OPENSSL_free(key->public_key);
  OPENSSL_free(key->secret_key);
  key->public_key = NULL;
  key->secret_key = NULL;
}

int KEM_KEY_init(KEM_KEY *key, const KEM *kem) {
  if (key == NULL || kem == NULL) {
    return 0;
  }
  // If the key is already initialized clear it.
  KEM_KEY_clear(key);

  key->kem = kem;
  key->public_key = OPENSSL_malloc(kem->public_key_len);
  key->secret_key = OPENSSL_malloc(kem->secret_key_len);
  if (key->public_key == NULL || key->secret_key == NULL) {
    KEM_KEY_clear(key);
    return 0;
  }

  return 1;
}

void KEM_KEY_free(KEM_KEY *key) {
  if (key == NULL) {
    return;
  }
  KEM_KEY_clear(key);
  OPENSSL_free(key);
}

const KEM *KEM_KEY_get0_kem(KEM_KEY* key) {
  return key->kem;
}

int KEM_KEY_set_raw_public_key(KEM_KEY *key, const uint8_t *in) {
  key->public_key = OPENSSL_memdup(in, key->kem->public_key_len);
  if (key->public_key == NULL) {
    return 0;
  }

  return 1;
}

int KEM_KEY_set_raw_secret_key(KEM_KEY *key, const uint8_t *in) {
  key->secret_key = OPENSSL_memdup(in, key->kem->secret_key_len);
  if (key->secret_key == NULL) {
    return 0;
  }

  return 1;
}

int KEM_KEY_set_raw_key(KEM_KEY *key, const uint8_t *in_public,
                                      const uint8_t *in_secret) {
  key->public_key = OPENSSL_memdup(in_public, key->kem->public_key_len);
  key->secret_key = OPENSSL_memdup(in_secret, key->kem->secret_key_len);
  if (key->public_key == NULL || key->secret_key == NULL) {
    KEM_KEY_clear(key);
    return 0;
  }

  return 1;
}
