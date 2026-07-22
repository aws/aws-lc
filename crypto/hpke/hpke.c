// Copyright (c) 2020, Google Inc.
// SPDX-License-Identifier: ISC

#include <openssl/hpke.h>

#include <assert.h>
#include <string.h>

#include <openssl/aead.h>
#include <openssl/bytestring.h>
#include <openssl/curve25519.h>
#include <openssl/digest.h>
#include <openssl/err.h>
#include <openssl/evp_errors.h>
#include <openssl/hkdf.h>
#include <openssl/mem.h>
#include <openssl/rand.h>
#include <openssl/sha.h>

#include "../internal.h"
#include "../fipsmodule/ml_kem/ml_kem.h"


// This file implements RFC 9180 and draft-ietf-hpke-pq-04.

#define MAX_SEED_LEN 64
#define MAX_SHARED_SECRET_LEN SHA256_DIGEST_LENGTH

struct evp_hpke_kem_st {
  uint16_t id;
  size_t public_key_len;
  size_t private_key_len;
  size_t seed_len;
  size_t enc_len;
  int (*init_key)(EVP_HPKE_KEY *key, const uint8_t *priv_key,
                  size_t priv_key_len);
  int (*generate_key)(EVP_HPKE_KEY *key);
  int (*encap_with_seed)(const EVP_HPKE_KEM *kem, uint8_t *out_shared_secret,
                         size_t *out_shared_secret_len, uint8_t *out_enc,
                         size_t *out_enc_len, size_t max_enc,
                         const uint8_t *peer_public_key,
                         size_t peer_public_key_len, const uint8_t *seed,
                         size_t seed_len);
  int (*decap)(const EVP_HPKE_KEY *key, uint8_t *out_shared_secret,
               size_t *out_shared_secret_len, const uint8_t *enc,
               size_t enc_len);
  int (*auth_encap_with_seed)(const EVP_HPKE_KEY *key,
                              uint8_t *out_shared_secret,
                              size_t *out_shared_secret_len, uint8_t *out_enc,
                              size_t *out_enc_len, size_t max_enc,
                              const uint8_t *peer_public_key,
                              size_t peer_public_key_len, const uint8_t *seed,
                              size_t seed_len);
  int (*auth_decap)(const EVP_HPKE_KEY *key, uint8_t *out_shared_secret,
                    size_t *out_shared_secret_len, const uint8_t *enc,
                    size_t enc_len, const uint8_t *peer_public_key,
                    size_t peer_public_key_len);
};

struct evp_hpke_kdf_st {
  uint16_t id;
  // We only support HKDF-based KDFs.
  const EVP_MD *(*hkdf_md_func)(void);
};

struct evp_hpke_aead_st {
  uint16_t id;
  const EVP_AEAD *(*aead_func)(void);
};


// Low-level labeled KDF functions.

static const char kHpkeVersionId[] = "HPKE-v1";

static int add_label_string(CBB *cbb, const char *label) {
  return CBB_add_bytes(cbb, (const uint8_t *)label, strlen(label));
}

static int hpke_labeled_extract(const EVP_MD *hkdf_md, uint8_t *out_key,
                                size_t *out_len, const uint8_t *salt,
                                size_t salt_len, const uint8_t *suite_id,
                                size_t suite_id_len, const char *label,
                                const uint8_t *ikm, size_t ikm_len) {
  // labeledIKM = concat("HPKE-v1", suite_id, label, IKM)
  CBB labeled_ikm;
  int ok = CBB_init(&labeled_ikm, 0) &&
           add_label_string(&labeled_ikm, kHpkeVersionId) &&
           CBB_add_bytes(&labeled_ikm, suite_id, suite_id_len) &&
           add_label_string(&labeled_ikm, label) &&
           CBB_add_bytes(&labeled_ikm, ikm, ikm_len) &&
           HKDF_extract(out_key, out_len, hkdf_md, CBB_data(&labeled_ikm),
                        CBB_len(&labeled_ikm), salt, salt_len);
  CBB_cleanup(&labeled_ikm);
  return ok;
}

static int hpke_labeled_expand(const EVP_MD *hkdf_md, uint8_t *out_key,
                               size_t out_len, const uint8_t *prk,
                               size_t prk_len, const uint8_t *suite_id,
                               size_t suite_id_len, const char *label,
                               const uint8_t *info, size_t info_len) {
  // labeledInfo = concat(I2OSP(L, 2), "HPKE-v1", suite_id, label, info)
  CBB labeled_info;
  int ok = CBB_init(&labeled_info, 0) &&
           CBB_add_u16(&labeled_info, out_len) &&
           add_label_string(&labeled_info, kHpkeVersionId) &&
           CBB_add_bytes(&labeled_info, suite_id, suite_id_len) &&
           add_label_string(&labeled_info, label) &&
           CBB_add_bytes(&labeled_info, info, info_len) &&
           HKDF_expand(out_key, out_len, hkdf_md, prk, prk_len,
                       CBB_data(&labeled_info), CBB_len(&labeled_info));
  CBB_cleanup(&labeled_info);
  return ok;
}


// KEM implementations.

// dhkem_extract_and_expand implements the ExtractAndExpand operation in the
// DHKEM construction. See section 4.1 of RFC 9180.
static int dhkem_extract_and_expand(uint16_t kem_id, const EVP_MD *hkdf_md,
                                    uint8_t *out_key, size_t out_len,
                                    const uint8_t *dh, size_t dh_len,
                                    const uint8_t *kem_context,
                                    size_t kem_context_len) {
  // concat("KEM", I2OSP(kem_id, 2))
  uint8_t suite_id[5] = {'K', 'E', 'M', kem_id >> 8, kem_id & 0xff};
  uint8_t prk[EVP_MAX_MD_SIZE];
  size_t prk_len;
  int ret = hpke_labeled_extract(hkdf_md, prk, &prk_len, NULL, 0, suite_id,
                              sizeof(suite_id), "eae_prk", dh, dh_len) &&
         hpke_labeled_expand(hkdf_md, out_key, out_len, prk, prk_len, suite_id,
                             sizeof(suite_id), "shared_secret", kem_context,
                             kem_context_len);
  OPENSSL_cleanse(prk, sizeof(prk));
  return ret;
}

static int x25519_init_key(EVP_HPKE_KEY *key, const uint8_t *priv_key,
                           size_t priv_key_len) {
  if (priv_key_len != X25519_PRIVATE_KEY_LEN) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  key->private_key = OPENSSL_memdup(priv_key, X25519_PRIVATE_KEY_LEN);
  if (key->private_key == NULL) {
    return 0;
  }
  key->public_key = OPENSSL_malloc(X25519_PUBLIC_VALUE_LEN);
  if (key->public_key == NULL) {
    OPENSSL_free(key->private_key);
    key->private_key = NULL;
    return 0;
  }
  X25519_public_from_private(key->public_key, priv_key);
  return 1;
}

static int x25519_generate_key(EVP_HPKE_KEY *key) {
  key->private_key = OPENSSL_malloc(X25519_PRIVATE_KEY_LEN);
  key->public_key = OPENSSL_malloc(X25519_PUBLIC_VALUE_LEN);
  if (key->private_key == NULL || key->public_key == NULL) {
    OPENSSL_free(key->private_key);
    OPENSSL_free(key->public_key);
    key->private_key = NULL;
    key->public_key = NULL;
    return 0;
  }
  X25519_keypair(key->public_key, key->private_key);
  return 1;
}

static int x25519_encap_with_seed(
    const EVP_HPKE_KEM *kem, uint8_t *out_shared_secret,
    size_t *out_shared_secret_len, uint8_t *out_enc, size_t *out_enc_len,
    size_t max_enc, const uint8_t *peer_public_key, size_t peer_public_key_len,
    const uint8_t *seed, size_t seed_len) {
  if (max_enc < X25519_PUBLIC_VALUE_LEN) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }
  if (seed_len != X25519_PRIVATE_KEY_LEN) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }
  X25519_public_from_private(out_enc, seed);

  uint8_t dh[X25519_SHARED_KEY_LEN];
  if (peer_public_key_len != X25519_PUBLIC_VALUE_LEN ||
      !X25519(dh, seed, peer_public_key)) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }

  uint8_t kem_context[2 * X25519_PUBLIC_VALUE_LEN];
  OPENSSL_memcpy(kem_context, out_enc, X25519_PUBLIC_VALUE_LEN);
  OPENSSL_memcpy(kem_context + X25519_PUBLIC_VALUE_LEN, peer_public_key,
                 X25519_PUBLIC_VALUE_LEN);
  if (!dhkem_extract_and_expand(kem->id, EVP_sha256(), out_shared_secret,
                                SHA256_DIGEST_LENGTH, dh, sizeof(dh),
                                kem_context, sizeof(kem_context))) {
    return 0;
  }

  *out_enc_len = X25519_PUBLIC_VALUE_LEN;
  *out_shared_secret_len = SHA256_DIGEST_LENGTH;
  return 1;
}

static int x25519_decap(const EVP_HPKE_KEY *key, uint8_t *out_shared_secret,
                        size_t *out_shared_secret_len, const uint8_t *enc,
                        size_t enc_len) {
  uint8_t dh[X25519_SHARED_KEY_LEN];
  if (enc_len != X25519_PUBLIC_VALUE_LEN ||
      !X25519(dh, key->private_key, enc)) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }

  uint8_t kem_context[2 * X25519_PUBLIC_VALUE_LEN];
  OPENSSL_memcpy(kem_context, enc, X25519_PUBLIC_VALUE_LEN);
  OPENSSL_memcpy(kem_context + X25519_PUBLIC_VALUE_LEN, key->public_key,
                 X25519_PUBLIC_VALUE_LEN);
  if (!dhkem_extract_and_expand(key->kem->id, EVP_sha256(), out_shared_secret,
                                SHA256_DIGEST_LENGTH, dh, sizeof(dh),
                                kem_context, sizeof(kem_context))) {
    return 0;
  }

  *out_shared_secret_len = SHA256_DIGEST_LENGTH;
  return 1;
}

static int x25519_auth_encap_with_seed(
    const EVP_HPKE_KEY *key, uint8_t *out_shared_secret,
    size_t *out_shared_secret_len, uint8_t *out_enc, size_t *out_enc_len,
    size_t max_enc, const uint8_t *peer_public_key, size_t peer_public_key_len,
    const uint8_t *seed, size_t seed_len) {
  if (max_enc < X25519_PUBLIC_VALUE_LEN) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }
  if (seed_len != X25519_PRIVATE_KEY_LEN) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }
  X25519_public_from_private(out_enc, seed);

  uint8_t dh[2 * X25519_SHARED_KEY_LEN];
  if (peer_public_key_len != X25519_PUBLIC_VALUE_LEN ||
      !X25519(dh, seed, peer_public_key) ||
      !X25519(dh + X25519_SHARED_KEY_LEN, key->private_key, peer_public_key)) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }

  uint8_t kem_context[3 * X25519_PUBLIC_VALUE_LEN];
  OPENSSL_memcpy(kem_context, out_enc, X25519_PUBLIC_VALUE_LEN);
  OPENSSL_memcpy(kem_context + X25519_PUBLIC_VALUE_LEN, peer_public_key,
                 X25519_PUBLIC_VALUE_LEN);
  OPENSSL_memcpy(kem_context + 2 * X25519_PUBLIC_VALUE_LEN, key->public_key,
                 X25519_PUBLIC_VALUE_LEN);
  if (!dhkem_extract_and_expand(key->kem->id, EVP_sha256(), out_shared_secret,
                                SHA256_DIGEST_LENGTH, dh, sizeof(dh),
                                kem_context, sizeof(kem_context))) {
    return 0;
  }

  *out_enc_len = X25519_PUBLIC_VALUE_LEN;
  *out_shared_secret_len = SHA256_DIGEST_LENGTH;
  return 1;
}

static int x25519_auth_decap(const EVP_HPKE_KEY *key,
                             uint8_t *out_shared_secret,
                             size_t *out_shared_secret_len, const uint8_t *enc,
                             size_t enc_len, const uint8_t *peer_public_key,
                             size_t peer_public_key_len) {
  uint8_t dh[2 * X25519_SHARED_KEY_LEN];
  if (enc_len != X25519_PUBLIC_VALUE_LEN ||
      peer_public_key_len != X25519_PUBLIC_VALUE_LEN ||
      !X25519(dh, key->private_key, enc) ||
      !X25519(dh + X25519_SHARED_KEY_LEN, key->private_key, peer_public_key)) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }

  uint8_t kem_context[3 * X25519_PUBLIC_VALUE_LEN];
  OPENSSL_memcpy(kem_context, enc, X25519_PUBLIC_VALUE_LEN);
  OPENSSL_memcpy(kem_context + X25519_PUBLIC_VALUE_LEN, key->public_key,
                 X25519_PUBLIC_VALUE_LEN);
  OPENSSL_memcpy(kem_context + 2 * X25519_PUBLIC_VALUE_LEN, peer_public_key,
                 X25519_PUBLIC_VALUE_LEN);
  if (!dhkem_extract_and_expand(key->kem->id, EVP_sha256(), out_shared_secret,
                                SHA256_DIGEST_LENGTH, dh, sizeof(dh),
                                kem_context, sizeof(kem_context))) {
    return 0;
  }

  *out_shared_secret_len = SHA256_DIGEST_LENGTH;
  return 1;
}

const EVP_HPKE_KEM *EVP_hpke_x25519_hkdf_sha256(void) {
  static const EVP_HPKE_KEM kKEM = {
      /*id=*/EVP_HPKE_DHKEM_X25519_HKDF_SHA256,
      /*public_key_len=*/X25519_PUBLIC_VALUE_LEN,
      /*private_key_len=*/X25519_PRIVATE_KEY_LEN,
      /*seed_len=*/X25519_PRIVATE_KEY_LEN,
      /*enc_len=*/X25519_PUBLIC_VALUE_LEN,
      x25519_init_key,
      x25519_generate_key,
      x25519_encap_with_seed,
      x25519_decap,
      x25519_auth_encap_with_seed,
      x25519_auth_decap,
  };
  return &kKEM;
}


// ML-KEM KEM implementations (draft-ietf-hpke-pq-04).

static int mlkem512_init_key(EVP_HPKE_KEY *key, const uint8_t *priv_key,
                             size_t priv_key_len) {
  if (priv_key_len != MLKEM512_SECRET_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }
  if (ml_kem_512_check_sk(priv_key, priv_key_len) != 0) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }
  key->private_key = OPENSSL_memdup(priv_key, MLKEM512_SECRET_KEY_BYTES);
  if (key->private_key == NULL) {
    return 0;
  }
  size_t pk_offset = MLKEM512_SECRET_KEY_BYTES - MLKEM512_PUBLIC_KEY_BYTES - 64;
  key->public_key = OPENSSL_memdup(priv_key + pk_offset,
                                   MLKEM512_PUBLIC_KEY_BYTES);
  if (key->public_key == NULL) {
    OPENSSL_free(key->private_key);
    key->private_key = NULL;
    return 0;
  }
  return 1;
}

static int mlkem512_generate_key(EVP_HPKE_KEY *key) {
  key->public_key = OPENSSL_malloc(MLKEM512_PUBLIC_KEY_BYTES);
  key->private_key = OPENSSL_malloc(MLKEM512_SECRET_KEY_BYTES);
  if (key->public_key == NULL || key->private_key == NULL) {
    OPENSSL_free(key->public_key);
    OPENSSL_free(key->private_key);
    key->public_key = NULL;
    key->private_key = NULL;
    return 0;
  }
  size_t pk_len = MLKEM512_PUBLIC_KEY_BYTES;
  size_t sk_len = MLKEM512_SECRET_KEY_BYTES;
  if (ml_kem_512_keypair(key->public_key, &pk_len,
                         key->private_key, &sk_len) != 0) {
    OPENSSL_free(key->public_key);
    OPENSSL_free(key->private_key);
    key->public_key = NULL;
    key->private_key = NULL;
    return 0;
  }
  return 1;
}

static int mlkem512_encap_with_seed(
    const EVP_HPKE_KEM *kem, uint8_t *out_shared_secret,
    size_t *out_shared_secret_len, uint8_t *out_enc, size_t *out_enc_len,
    size_t max_enc, const uint8_t *peer_public_key, size_t peer_public_key_len,
    const uint8_t *seed, size_t seed_len) {
  if (max_enc < MLKEM512_CIPHERTEXT_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }
  if (peer_public_key_len != MLKEM512_PUBLIC_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }
  if (seed_len != MLKEM512_ENCAPS_SEED_LEN) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  size_t ct_len = MLKEM512_CIPHERTEXT_BYTES;
  size_t ss_len = MLKEM512_SHARED_SECRET_LEN;
  if (ml_kem_512_encapsulate_deterministic(out_enc, &ct_len,
                                           out_shared_secret, &ss_len,
                                           peer_public_key, seed) != 0) {
    return 0;
  }

  *out_enc_len = ct_len;
  *out_shared_secret_len = ss_len;
  return 1;
}

static int mlkem512_decap(const EVP_HPKE_KEY *key, uint8_t *out_shared_secret,
                          size_t *out_shared_secret_len, const uint8_t *enc,
                          size_t enc_len) {
  if (enc_len != MLKEM512_CIPHERTEXT_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }

  size_t ss_len = MLKEM512_SHARED_SECRET_LEN;
  if (ml_kem_512_decapsulate(out_shared_secret, &ss_len,
                             enc, key->private_key) != 0) {
    return 0;
  }

  *out_shared_secret_len = ss_len;
  return 1;
}

const EVP_HPKE_KEM *EVP_hpke_mlkem512(void) {
  static const EVP_HPKE_KEM kKEM = {
      /*id=*/EVP_HPKE_KEM_MLKEM512,
      /*public_key_len=*/MLKEM512_PUBLIC_KEY_BYTES,
      /*private_key_len=*/MLKEM512_SECRET_KEY_BYTES,
      /*seed_len=*/MLKEM512_ENCAPS_SEED_LEN,
      /*enc_len=*/MLKEM512_CIPHERTEXT_BYTES,
      mlkem512_init_key,
      mlkem512_generate_key,
      mlkem512_encap_with_seed,
      mlkem512_decap,
      NULL,
      NULL,
  };
  return &kKEM;
}


static int mlkem768_init_key(EVP_HPKE_KEY *key, const uint8_t *priv_key,
                             size_t priv_key_len) {
  if (priv_key_len != MLKEM768_SECRET_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }
  if (ml_kem_768_check_sk(priv_key, priv_key_len) != 0) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }
  key->private_key = OPENSSL_memdup(priv_key, MLKEM768_SECRET_KEY_BYTES);
  if (key->private_key == NULL) {
    return 0;
  }
  size_t pk_offset = MLKEM768_SECRET_KEY_BYTES - MLKEM768_PUBLIC_KEY_BYTES - 64;
  key->public_key = OPENSSL_memdup(priv_key + pk_offset,
                                   MLKEM768_PUBLIC_KEY_BYTES);
  if (key->public_key == NULL) {
    OPENSSL_free(key->private_key);
    key->private_key = NULL;
    return 0;
  }
  return 1;
}

static int mlkem768_generate_key(EVP_HPKE_KEY *key) {
  key->public_key = OPENSSL_malloc(MLKEM768_PUBLIC_KEY_BYTES);
  key->private_key = OPENSSL_malloc(MLKEM768_SECRET_KEY_BYTES);
  if (key->public_key == NULL || key->private_key == NULL) {
    OPENSSL_free(key->public_key);
    OPENSSL_free(key->private_key);
    key->public_key = NULL;
    key->private_key = NULL;
    return 0;
  }
  size_t pk_len = MLKEM768_PUBLIC_KEY_BYTES;
  size_t sk_len = MLKEM768_SECRET_KEY_BYTES;
  if (ml_kem_768_keypair(key->public_key, &pk_len,
                         key->private_key, &sk_len) != 0) {
    OPENSSL_free(key->public_key);
    OPENSSL_free(key->private_key);
    key->public_key = NULL;
    key->private_key = NULL;
    return 0;
  }
  return 1;
}

static int mlkem768_encap_with_seed(
    const EVP_HPKE_KEM *kem, uint8_t *out_shared_secret,
    size_t *out_shared_secret_len, uint8_t *out_enc, size_t *out_enc_len,
    size_t max_enc, const uint8_t *peer_public_key, size_t peer_public_key_len,
    const uint8_t *seed, size_t seed_len) {
  if (max_enc < MLKEM768_CIPHERTEXT_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }
  if (peer_public_key_len != MLKEM768_PUBLIC_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }
  if (seed_len != MLKEM768_ENCAPS_SEED_LEN) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  size_t ct_len = MLKEM768_CIPHERTEXT_BYTES;
  size_t ss_len = MLKEM768_SHARED_SECRET_LEN;
  if (ml_kem_768_encapsulate_deterministic(out_enc, &ct_len,
                                           out_shared_secret, &ss_len,
                                           peer_public_key, seed) != 0) {
    return 0;
  }

  *out_enc_len = ct_len;
  *out_shared_secret_len = ss_len;
  return 1;
}

static int mlkem768_decap(const EVP_HPKE_KEY *key, uint8_t *out_shared_secret,
                          size_t *out_shared_secret_len, const uint8_t *enc,
                          size_t enc_len) {
  if (enc_len != MLKEM768_CIPHERTEXT_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }

  size_t ss_len = MLKEM768_SHARED_SECRET_LEN;
  if (ml_kem_768_decapsulate(out_shared_secret, &ss_len,
                             enc, key->private_key) != 0) {
    return 0;
  }

  *out_shared_secret_len = ss_len;
  return 1;
}

const EVP_HPKE_KEM *EVP_hpke_mlkem768(void) {
  static const EVP_HPKE_KEM kKEM = {
      /*id=*/EVP_HPKE_KEM_MLKEM768,
      /*public_key_len=*/MLKEM768_PUBLIC_KEY_BYTES,
      /*private_key_len=*/MLKEM768_SECRET_KEY_BYTES,
      /*seed_len=*/MLKEM768_ENCAPS_SEED_LEN,
      /*enc_len=*/MLKEM768_CIPHERTEXT_BYTES,
      mlkem768_init_key,
      mlkem768_generate_key,
      mlkem768_encap_with_seed,
      mlkem768_decap,
      NULL,
      NULL,
  };
  return &kKEM;
}


static int mlkem1024_init_key(EVP_HPKE_KEY *key, const uint8_t *priv_key,
                              size_t priv_key_len) {
  if (priv_key_len != MLKEM1024_SECRET_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }
  if (ml_kem_1024_check_sk(priv_key, priv_key_len) != 0) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }
  key->private_key = OPENSSL_memdup(priv_key, MLKEM1024_SECRET_KEY_BYTES);
  if (key->private_key == NULL) {
    return 0;
  }
  size_t pk_offset =
      MLKEM1024_SECRET_KEY_BYTES - MLKEM1024_PUBLIC_KEY_BYTES - 64;
  key->public_key = OPENSSL_memdup(priv_key + pk_offset,
                                   MLKEM1024_PUBLIC_KEY_BYTES);
  if (key->public_key == NULL) {
    OPENSSL_free(key->private_key);
    key->private_key = NULL;
    return 0;
  }
  return 1;
}

static int mlkem1024_generate_key(EVP_HPKE_KEY *key) {
  key->public_key = OPENSSL_malloc(MLKEM1024_PUBLIC_KEY_BYTES);
  key->private_key = OPENSSL_malloc(MLKEM1024_SECRET_KEY_BYTES);
  if (key->public_key == NULL || key->private_key == NULL) {
    OPENSSL_free(key->public_key);
    OPENSSL_free(key->private_key);
    key->public_key = NULL;
    key->private_key = NULL;
    return 0;
  }
  size_t pk_len = MLKEM1024_PUBLIC_KEY_BYTES;
  size_t sk_len = MLKEM1024_SECRET_KEY_BYTES;
  if (ml_kem_1024_keypair(key->public_key, &pk_len,
                          key->private_key, &sk_len) != 0) {
    OPENSSL_free(key->public_key);
    OPENSSL_free(key->private_key);
    key->public_key = NULL;
    key->private_key = NULL;
    return 0;
  }
  return 1;
}

static int mlkem1024_encap_with_seed(
    const EVP_HPKE_KEM *kem, uint8_t *out_shared_secret,
    size_t *out_shared_secret_len, uint8_t *out_enc, size_t *out_enc_len,
    size_t max_enc, const uint8_t *peer_public_key, size_t peer_public_key_len,
    const uint8_t *seed, size_t seed_len) {
  if (max_enc < MLKEM1024_CIPHERTEXT_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }
  if (peer_public_key_len != MLKEM1024_PUBLIC_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }
  if (seed_len != MLKEM1024_ENCAPS_SEED_LEN) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  size_t ct_len = MLKEM1024_CIPHERTEXT_BYTES;
  size_t ss_len = MLKEM1024_SHARED_SECRET_LEN;
  if (ml_kem_1024_encapsulate_deterministic(out_enc, &ct_len,
                                            out_shared_secret, &ss_len,
                                            peer_public_key, seed) != 0) {
    return 0;
  }

  *out_enc_len = ct_len;
  *out_shared_secret_len = ss_len;
  return 1;
}

static int mlkem1024_decap(const EVP_HPKE_KEY *key, uint8_t *out_shared_secret,
                           size_t *out_shared_secret_len, const uint8_t *enc,
                           size_t enc_len) {
  if (enc_len != MLKEM1024_CIPHERTEXT_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }

  size_t ss_len = MLKEM1024_SHARED_SECRET_LEN;
  if (ml_kem_1024_decapsulate(out_shared_secret, &ss_len,
                              enc, key->private_key) != 0) {
    return 0;
  }

  *out_shared_secret_len = ss_len;
  return 1;
}

const EVP_HPKE_KEM *EVP_hpke_mlkem1024(void) {
  static const EVP_HPKE_KEM kKEM = {
      /*id=*/EVP_HPKE_KEM_MLKEM1024,
      /*public_key_len=*/MLKEM1024_PUBLIC_KEY_BYTES,
      /*private_key_len=*/MLKEM1024_SECRET_KEY_BYTES,
      /*seed_len=*/MLKEM1024_ENCAPS_SEED_LEN,
      /*enc_len=*/MLKEM1024_CIPHERTEXT_BYTES,
      mlkem1024_init_key,
      mlkem1024_generate_key,
      mlkem1024_encap_with_seed,
      mlkem1024_decap,
      NULL,
      NULL,
  };
  return &kKEM;
}


uint16_t EVP_HPKE_KEM_id(const EVP_HPKE_KEM *kem) { return kem->id; }

size_t EVP_HPKE_KEM_public_key_len(const EVP_HPKE_KEM *kem) {
  return kem->public_key_len;
}

size_t EVP_HPKE_KEM_private_key_len(const EVP_HPKE_KEM *kem) {
  return kem->private_key_len;
}

size_t EVP_HPKE_KEM_enc_len(const EVP_HPKE_KEM *kem) { return kem->enc_len; }

void EVP_HPKE_KEY_zero(EVP_HPKE_KEY *key) {
  OPENSSL_memset(key, 0, sizeof(EVP_HPKE_KEY));
}

void EVP_HPKE_KEY_cleanup(EVP_HPKE_KEY *key) {
  if (key->private_key != NULL) {
    if (key->kem != NULL) {
      OPENSSL_cleanse(key->private_key, key->kem->private_key_len);
    }
    OPENSSL_free(key->private_key);
    key->private_key = NULL;
  }
  if (key->public_key != NULL) {
    OPENSSL_free(key->public_key);
    key->public_key = NULL;
  }
}

EVP_HPKE_KEY *EVP_HPKE_KEY_new(void) {
  EVP_HPKE_KEY *key = OPENSSL_malloc(sizeof(EVP_HPKE_KEY));
  if (key == NULL) {
    return NULL;
  }
  EVP_HPKE_KEY_zero(key);
  return key;
}

void EVP_HPKE_KEY_free(EVP_HPKE_KEY *key) {
  if (key != NULL) {
    EVP_HPKE_KEY_cleanup(key);
    OPENSSL_free(key);
  }
}

int EVP_HPKE_KEY_copy(EVP_HPKE_KEY *dst, const EVP_HPKE_KEY *src) {
  EVP_HPKE_KEY_cleanup(dst);
  dst->kem = src->kem;
  dst->private_key = NULL;
  dst->public_key = NULL;
  if (src->kem == NULL) {
    return 1;
  }
  dst->private_key = OPENSSL_memdup(src->private_key, src->kem->private_key_len);
  if (dst->private_key == NULL) {
    dst->kem = NULL;
    return 0;
  }
  dst->public_key = OPENSSL_memdup(src->public_key, src->kem->public_key_len);
  if (dst->public_key == NULL) {
    OPENSSL_free(dst->private_key);
    dst->private_key = NULL;
    dst->kem = NULL;
    return 0;
  }
  return 1;
}

void EVP_HPKE_KEY_move(EVP_HPKE_KEY *out, EVP_HPKE_KEY *in) {
  EVP_HPKE_KEY_cleanup(out);
  out->kem = in->kem;
  out->private_key = in->private_key;
  out->public_key = in->public_key;
  EVP_HPKE_KEY_zero(in);
}

int EVP_HPKE_KEY_init(EVP_HPKE_KEY *key, const EVP_HPKE_KEM *kem,
                      const uint8_t *priv_key, size_t priv_key_len) {
  EVP_HPKE_KEY_zero(key);
  key->kem = kem;
  if (!kem->init_key(key, priv_key, priv_key_len)) {
    key->kem = NULL;
    return 0;
  }
  return 1;
}

int EVP_HPKE_KEY_generate(EVP_HPKE_KEY *key, const EVP_HPKE_KEM *kem) {
  EVP_HPKE_KEY_zero(key);
  key->kem = kem;
  if (!kem->generate_key(key)) {
    key->kem = NULL;
    return 0;
  }
  return 1;
}

const EVP_HPKE_KEM *EVP_HPKE_KEY_kem(const EVP_HPKE_KEY *key) {
  return key->kem;
}

int EVP_HPKE_KEY_public_key(const EVP_HPKE_KEY *key, uint8_t *out,
                            size_t *out_len, size_t max_out) {
  if (max_out < key->kem->public_key_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }
  OPENSSL_memcpy(out, key->public_key, key->kem->public_key_len);
  *out_len = key->kem->public_key_len;
  return 1;
}

int EVP_HPKE_KEY_private_key(const EVP_HPKE_KEY *key, uint8_t *out,
                            size_t *out_len, size_t max_out) {
  if (max_out < key->kem->private_key_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }
  OPENSSL_memcpy(out, key->private_key, key->kem->private_key_len);
  *out_len = key->kem->private_key_len;
  return 1;
}


// Supported KDFs and AEADs.

const EVP_HPKE_KDF *EVP_hpke_hkdf_sha256(void) {
  static const EVP_HPKE_KDF kKDF = {EVP_HPKE_HKDF_SHA256, &EVP_sha256};
  return &kKDF;
}

const EVP_HPKE_KDF *EVP_hpke_hkdf_sha384(void) {
  static const EVP_HPKE_KDF kKDF = {EVP_HPKE_HKDF_SHA384, &EVP_sha384};
  return &kKDF;
}

uint16_t EVP_HPKE_KDF_id(const EVP_HPKE_KDF *kdf) { return kdf->id; }

const EVP_MD *EVP_HPKE_KDF_hkdf_md(const EVP_HPKE_KDF *kdf) {
  return kdf->hkdf_md_func();
}

const EVP_HPKE_AEAD *EVP_hpke_aes_128_gcm(void) {
  static const EVP_HPKE_AEAD kAEAD = {EVP_HPKE_AES_128_GCM,
                                      &EVP_aead_aes_128_gcm};
  return &kAEAD;
}

const EVP_HPKE_AEAD *EVP_hpke_aes_256_gcm(void) {
  static const EVP_HPKE_AEAD kAEAD = {EVP_HPKE_AES_256_GCM,
                                      &EVP_aead_aes_256_gcm};
  return &kAEAD;
}

const EVP_HPKE_AEAD *EVP_hpke_chacha20_poly1305(void) {
  static const EVP_HPKE_AEAD kAEAD = {EVP_HPKE_CHACHA20_POLY1305,
                                      &EVP_aead_chacha20_poly1305};
  return &kAEAD;
}

uint16_t EVP_HPKE_AEAD_id(const EVP_HPKE_AEAD *aead) { return aead->id; }

const EVP_AEAD *EVP_HPKE_AEAD_aead(const EVP_HPKE_AEAD *aead) {
  return aead->aead_func();
}


// HPKE implementation.

// This is strlen("HPKE") + 3 * sizeof(uint16_t).
#define HPKE_SUITE_ID_LEN 10

// The suite_id for non-KEM pieces of HPKE is defined as concat("HPKE",
// I2OSP(kem_id, 2), I2OSP(kdf_id, 2), I2OSP(aead_id, 2)).
static int hpke_build_suite_id(const EVP_HPKE_CTX *ctx,
                               uint8_t out[HPKE_SUITE_ID_LEN]) {
  CBB cbb;
  CBB_init_fixed(&cbb, out, HPKE_SUITE_ID_LEN);
  return add_label_string(&cbb, "HPKE") &&   //
         CBB_add_u16(&cbb, ctx->kem->id) &&  //
         CBB_add_u16(&cbb, ctx->kdf->id) &&  //
         CBB_add_u16(&cbb, ctx->aead->id);
}

#define HPKE_MODE_BASE 0
#define HPKE_MODE_AUTH 2

static int hpke_key_schedule(EVP_HPKE_CTX *ctx, uint8_t mode,
                             const uint8_t *shared_secret,
                             size_t shared_secret_len, const uint8_t *info,
                             size_t info_len) {
  uint8_t suite_id[HPKE_SUITE_ID_LEN];
  if (!hpke_build_suite_id(ctx, suite_id)) {
    return 0;
  }

  // psk_id_hash = LabeledExtract("", "psk_id_hash", psk_id)
  // TODO(davidben): Precompute this value and store it with the EVP_HPKE_KDF.
  const EVP_MD *hkdf_md = ctx->kdf->hkdf_md_func();
  uint8_t psk_id_hash[EVP_MAX_MD_SIZE];
  size_t psk_id_hash_len;
  if (!hpke_labeled_extract(hkdf_md, psk_id_hash, &psk_id_hash_len, NULL, 0,
                            suite_id, sizeof(suite_id), "psk_id_hash", NULL,
                            0)) {
    return 0;
  }

  // info_hash = LabeledExtract("", "info_hash", info)
  uint8_t info_hash[EVP_MAX_MD_SIZE];
  size_t info_hash_len;
  if (!hpke_labeled_extract(hkdf_md, info_hash, &info_hash_len, NULL, 0,
                            suite_id, sizeof(suite_id), "info_hash", info,
                            info_len)) {
    return 0;
  }

  // key_schedule_context = concat(mode, psk_id_hash, info_hash)
  uint8_t context[sizeof(uint8_t) + 2 * EVP_MAX_MD_SIZE];
  size_t context_len;
  CBB context_cbb;
  CBB_init_fixed(&context_cbb, context, sizeof(context));
  if (!CBB_add_u8(&context_cbb, mode) ||
      !CBB_add_bytes(&context_cbb, psk_id_hash, psk_id_hash_len) ||
      !CBB_add_bytes(&context_cbb, info_hash, info_hash_len) ||
      !CBB_finish(&context_cbb, NULL, &context_len)) {
    return 0;
  }

  // secret = LabeledExtract(shared_secret, "secret", psk)
  uint8_t secret[EVP_MAX_MD_SIZE];
  size_t secret_len;
  if (!hpke_labeled_extract(hkdf_md, secret, &secret_len, shared_secret,
                            shared_secret_len, suite_id, sizeof(suite_id),
                            "secret", NULL, 0)) {
    return 0;
  }

  // key = LabeledExpand(secret, "key", key_schedule_context, Nk)
  const EVP_AEAD *aead = EVP_HPKE_AEAD_aead(ctx->aead);
  uint8_t key[EVP_AEAD_MAX_KEY_LENGTH];
  const size_t kKeyLen = EVP_AEAD_key_length(aead);
  if (!hpke_labeled_expand(hkdf_md, key, kKeyLen, secret, secret_len, suite_id,
                           sizeof(suite_id), "key", context, context_len) ||
      !EVP_AEAD_CTX_init(&ctx->aead_ctx, aead, key, kKeyLen,
                         EVP_AEAD_DEFAULT_TAG_LENGTH, NULL)) {
    return 0;
  }

  // base_nonce = LabeledExpand(secret, "base_nonce", key_schedule_context, Nn)
  if (!hpke_labeled_expand(hkdf_md, ctx->base_nonce,
                           EVP_AEAD_nonce_length(aead), secret, secret_len,
                           suite_id, sizeof(suite_id), "base_nonce", context,
                           context_len)) {
    return 0;
  }

  // exporter_secret = LabeledExpand(secret, "exp", key_schedule_context, Nh)
  if (!hpke_labeled_expand(hkdf_md, ctx->exporter_secret, EVP_MD_size(hkdf_md),
                           secret, secret_len, suite_id, sizeof(suite_id),
                           "exp", context, context_len)) {
    return 0;
  }

  return 1;
}

void EVP_HPKE_CTX_zero(EVP_HPKE_CTX *ctx) {
  OPENSSL_memset(ctx, 0, sizeof(EVP_HPKE_CTX));
  EVP_AEAD_CTX_zero(&ctx->aead_ctx);
}

void EVP_HPKE_CTX_cleanup(EVP_HPKE_CTX *ctx) {
  EVP_AEAD_CTX_cleanup(&ctx->aead_ctx);
}

EVP_HPKE_CTX *EVP_HPKE_CTX_new(void) {
  EVP_HPKE_CTX *ctx = OPENSSL_zalloc(sizeof(EVP_HPKE_CTX));
  if (ctx == NULL) {
    return NULL;
  }
  return ctx;
}

void EVP_HPKE_CTX_free(EVP_HPKE_CTX *ctx) {
  if (ctx != NULL) {
    EVP_HPKE_CTX_cleanup(ctx);
    OPENSSL_free(ctx);
  }
}

int EVP_HPKE_CTX_setup_sender(EVP_HPKE_CTX *ctx, uint8_t *out_enc,
                              size_t *out_enc_len, size_t max_enc,
                              const EVP_HPKE_KEM *kem, const EVP_HPKE_KDF *kdf,
                              const EVP_HPKE_AEAD *aead,
                              const uint8_t *peer_public_key,
                              size_t peer_public_key_len, const uint8_t *info,
                              size_t info_len) {
  uint8_t seed[MAX_SEED_LEN];
  AWSLC_ABORT_IF_NOT_ONE(RAND_bytes(seed, kem->seed_len));
  return EVP_HPKE_CTX_setup_sender_with_seed_for_testing(
      ctx, out_enc, out_enc_len, max_enc, kem, kdf, aead, peer_public_key,
      peer_public_key_len, info, info_len, seed, kem->seed_len);
}

int EVP_HPKE_CTX_setup_sender_with_seed_for_testing(
    EVP_HPKE_CTX *ctx, uint8_t *out_enc, size_t *out_enc_len, size_t max_enc,
    const EVP_HPKE_KEM *kem, const EVP_HPKE_KDF *kdf, const EVP_HPKE_AEAD *aead,
    const uint8_t *peer_public_key, size_t peer_public_key_len,
    const uint8_t *info, size_t info_len, const uint8_t *seed,
    size_t seed_len) {
  EVP_HPKE_CTX_zero(ctx);
  ctx->is_sender = 1;
  ctx->kem = kem;
  ctx->kdf = kdf;
  ctx->aead = aead;
  uint8_t shared_secret[MAX_SHARED_SECRET_LEN];
  size_t shared_secret_len;
  if (!kem->encap_with_seed(kem, shared_secret, &shared_secret_len, out_enc,
                            out_enc_len, max_enc, peer_public_key,
                            peer_public_key_len, seed, seed_len) ||
      !hpke_key_schedule(ctx, HPKE_MODE_BASE, shared_secret, shared_secret_len,
                         info, info_len)) {
    EVP_HPKE_CTX_cleanup(ctx);
    return 0;
  }
  return 1;
}

int EVP_HPKE_CTX_setup_recipient(EVP_HPKE_CTX *ctx, const EVP_HPKE_KEY *key,
                                 const EVP_HPKE_KDF *kdf,
                                 const EVP_HPKE_AEAD *aead, const uint8_t *enc,
                                 size_t enc_len, const uint8_t *info,
                                 size_t info_len) {
  EVP_HPKE_CTX_zero(ctx);
  ctx->is_sender = 0;
  ctx->kem = key->kem;
  ctx->kdf = kdf;
  ctx->aead = aead;
  uint8_t shared_secret[MAX_SHARED_SECRET_LEN];
  size_t shared_secret_len;
  if (!key->kem->decap(key, shared_secret, &shared_secret_len, enc, enc_len) ||
      !hpke_key_schedule(ctx, HPKE_MODE_BASE, shared_secret, shared_secret_len,
                         info, info_len)) {
    EVP_HPKE_CTX_cleanup(ctx);
    return 0;
  }
  return 1;
}


int EVP_HPKE_CTX_setup_auth_sender(
    EVP_HPKE_CTX *ctx, uint8_t *out_enc, size_t *out_enc_len, size_t max_enc,
    const EVP_HPKE_KEY *key, const EVP_HPKE_KDF *kdf, const EVP_HPKE_AEAD *aead,
    const uint8_t *peer_public_key, size_t peer_public_key_len,
    const uint8_t *info, size_t info_len) {
  uint8_t seed[MAX_SEED_LEN];
  AWSLC_ABORT_IF_NOT_ONE(RAND_bytes(seed, key->kem->seed_len));
  return EVP_HPKE_CTX_setup_auth_sender_with_seed_for_testing(
      ctx, out_enc, out_enc_len, max_enc, key, kdf, aead, peer_public_key,
      peer_public_key_len, info, info_len, seed, key->kem->seed_len);
}

int EVP_HPKE_CTX_setup_auth_sender_with_seed_for_testing(
    EVP_HPKE_CTX *ctx, uint8_t *out_enc, size_t *out_enc_len, size_t max_enc,
    const EVP_HPKE_KEY *key, const EVP_HPKE_KDF *kdf, const EVP_HPKE_AEAD *aead,
    const uint8_t *peer_public_key, size_t peer_public_key_len,
    const uint8_t *info, size_t info_len, const uint8_t *seed,
    size_t seed_len) {
  if (key->kem->auth_encap_with_seed == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATION_NOT_SUPPORTED_FOR_THIS_KEYTYPE);
    return 0;
  }

  EVP_HPKE_CTX_zero(ctx);
  ctx->is_sender = 1;
  ctx->kem = key->kem;
  ctx->kdf = kdf;
  ctx->aead = aead;
  uint8_t shared_secret[MAX_SHARED_SECRET_LEN];
  size_t shared_secret_len;
  if (!key->kem->auth_encap_with_seed(
          key, shared_secret, &shared_secret_len, out_enc, out_enc_len, max_enc,
          peer_public_key, peer_public_key_len, seed, seed_len) ||
      !hpke_key_schedule(ctx, HPKE_MODE_AUTH, shared_secret, shared_secret_len,
                         info, info_len)) {
    EVP_HPKE_CTX_cleanup(ctx);
    return 0;
  }
  return 1;
}

int EVP_HPKE_CTX_setup_auth_recipient(
    EVP_HPKE_CTX *ctx, const EVP_HPKE_KEY *key, const EVP_HPKE_KDF *kdf,
    const EVP_HPKE_AEAD *aead, const uint8_t *enc, size_t enc_len,
    const uint8_t *info, size_t info_len, const uint8_t *peer_public_key,
    size_t peer_public_key_len) {
  if (key->kem->auth_decap == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATION_NOT_SUPPORTED_FOR_THIS_KEYTYPE);
    return 0;
  }

  EVP_HPKE_CTX_zero(ctx);
  ctx->is_sender = 0;
  ctx->kem = key->kem;
  ctx->kdf = kdf;
  ctx->aead = aead;
  uint8_t shared_secret[MAX_SHARED_SECRET_LEN];
  size_t shared_secret_len;
  if (!key->kem->auth_decap(key, shared_secret, &shared_secret_len, enc,
                            enc_len, peer_public_key, peer_public_key_len) ||
      !hpke_key_schedule(ctx, HPKE_MODE_AUTH, shared_secret, shared_secret_len,
                         info, info_len)) {
    EVP_HPKE_CTX_cleanup(ctx);
    return 0;
  }
  return 1;
}

static void hpke_nonce(const EVP_HPKE_CTX *ctx, uint8_t *out_nonce,
                       size_t nonce_len) {
  assert(nonce_len >= 8);

  // Write padded big-endian bytes of |ctx->seq| to |out_nonce|.
  OPENSSL_memset(out_nonce, 0, nonce_len);
  uint64_t seq_copy = ctx->seq;
  for (size_t i = 0; i < 8; i++) {
    out_nonce[nonce_len - i - 1] = seq_copy & 0xff;
    seq_copy >>= 8;
  }

  // XOR the encoded sequence with the |ctx->base_nonce|.
  for (size_t i = 0; i < nonce_len; i++) {
    out_nonce[i] ^= ctx->base_nonce[i];
  }
}

int EVP_HPKE_CTX_open(EVP_HPKE_CTX *ctx, uint8_t *out, size_t *out_len,
                      size_t max_out_len, const uint8_t *in, size_t in_len,
                      const uint8_t *ad, size_t ad_len) {
  if (ctx->is_sender) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_SHOULD_NOT_HAVE_BEEN_CALLED);
    return 0;
  }
  if (ctx->seq == UINT64_MAX) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_OVERFLOW);
    return 0;
  }

  uint8_t nonce[EVP_AEAD_MAX_NONCE_LENGTH];
  const size_t nonce_len = EVP_AEAD_nonce_length(ctx->aead_ctx.aead);
  hpke_nonce(ctx, nonce, nonce_len);

  if (!EVP_AEAD_CTX_open(&ctx->aead_ctx, out, out_len, max_out_len, nonce,
                         nonce_len, in, in_len, ad, ad_len)) {
    return 0;
  }
  ctx->seq++;
  return 1;
}

int EVP_HPKE_CTX_seal(EVP_HPKE_CTX *ctx, uint8_t *out, size_t *out_len,
                      size_t max_out_len, const uint8_t *in, size_t in_len,
                      const uint8_t *ad, size_t ad_len) {
  if (!ctx->is_sender) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_SHOULD_NOT_HAVE_BEEN_CALLED);
    return 0;
  }
  if (ctx->seq == UINT64_MAX) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_OVERFLOW);
    return 0;
  }

  uint8_t nonce[EVP_AEAD_MAX_NONCE_LENGTH];
  const size_t nonce_len = EVP_AEAD_nonce_length(ctx->aead_ctx.aead);
  hpke_nonce(ctx, nonce, nonce_len);

  if (!EVP_AEAD_CTX_seal(&ctx->aead_ctx, out, out_len, max_out_len, nonce,
                         nonce_len, in, in_len, ad, ad_len)) {
    return 0;
  }
  ctx->seq++;
  return 1;
}

int EVP_HPKE_CTX_export(const EVP_HPKE_CTX *ctx, uint8_t *out,
                        size_t secret_len, const uint8_t *context,
                        size_t context_len) {
  uint8_t suite_id[HPKE_SUITE_ID_LEN];
  if (!hpke_build_suite_id(ctx, suite_id)) {
    return 0;
  }
  const EVP_MD *hkdf_md = ctx->kdf->hkdf_md_func();
  if (!hpke_labeled_expand(hkdf_md, out, secret_len, ctx->exporter_secret,
                           EVP_MD_size(hkdf_md), suite_id, sizeof(suite_id),
                           "sec", context, context_len)) {
    return 0;
  }
  return 1;
}

size_t EVP_HPKE_CTX_max_overhead(const EVP_HPKE_CTX *ctx) {
  assert(ctx->is_sender);
  return EVP_AEAD_max_overhead(EVP_AEAD_CTX_aead(&ctx->aead_ctx));
}

const EVP_HPKE_KEM *EVP_HPKE_CTX_kem(const EVP_HPKE_CTX *ctx) {
  return ctx->kem;
}

const EVP_HPKE_AEAD *EVP_HPKE_CTX_aead(const EVP_HPKE_CTX *ctx) {
  return ctx->aead;
}

const EVP_HPKE_KDF *EVP_HPKE_CTX_kdf(const EVP_HPKE_CTX *ctx) {
  return ctx->kdf;
}
