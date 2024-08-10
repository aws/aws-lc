// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "pqt_kem.h"

#include <openssl/bn.h>
#include <openssl/digest.h>
#include <openssl/ecdh.h>
#include <openssl/hkdf.h>
#include <openssl/nid.h>
#include <openssl/rand.h>

// |nistp_internal_keygen_deterministic| needs this for montgomery reduction.
#include "../fipsmodule/ec/internal.h"
// For definition of |KEM_METHOD|.
#include "../kem/internal.h"

// Max length of [pq shared secret] + [t shared secret]
#define PQT_MAX_CONCAT_SHARED_SECRET_BYTES \
  (MLKEM1024IPD_SHARED_SECRET_LEN + T384_SHARED_SECRET_LEN)
// Max length of [t ciphertext] + [t public key]
#define PQT_MAX_SALT_BYTES (T384_CIPHERTEXT_BYTES + T384_PUBLIC_KEY_BYTES)

// KDF Labels
#define PQT_LABEL_LEN (9)
static const uint8_t PQT25519_LABEL[PQT_LABEL_LEN] = {'P', 'Q', 'T', '2', '5',
                                                      '5', '-', 'v', '1'};
static const uint8_t PQT256_LABEL[PQT_LABEL_LEN] = {'P', 'Q', 'T', '2', '5',
                                                    '6', '-', 'v', '1'};
static const uint8_t PQT384_LABEL[PQT_LABEL_LEN] = {'P', 'Q', 'T', '3', '8',
                                                    '4', '-', 'v', '1'};


// 1. T KEM Wrappers
// -----------------
// All wrappers return one on success and zero on error.
//
// WARNING: These are internal functions and should not be used outside the PQ/T
// KEM construction.

// 1.1 X25519 Wrappers
// -------------------

// Deterministically generate an X25519 keypair.
//
// The public key and secret key format matches RFC 9180.
//
// Returns 1 on success and 0 otherwise.
static int t25519_keygen_deterministic(uint8_t *public_key, uint8_t *secret_key,
                                       const uint8_t *seed) {
  OPENSSL_memcpy(secret_key, seed, T25519_SECRET_KEY_BYTES);
  X25519_public_from_private(public_key, secret_key);
  return 1;
}

// Encapsulate to a X25519 public key.
//
// Similar to DHKEM.Encap in RFC 9180, except it returns the raw dh value
// instead of HKDF-ing it with the ciphertext and public key.
//
// Returns 1 on success and 0 otherwise.
static int t25519_encaps_deterministic(uint8_t *ciphertext,
                                       uint8_t *shared_secret,
                                       const uint8_t *public_key,
                                       const uint8_t *seed) {
  X25519_public_from_private(ciphertext, seed);
  return X25519(shared_secret, seed, public_key);
}

// Decapsulate to a X25519 secret key.
//
// Similar to DHKEM.Decap in RFC 9180, except it returns the raw dh value
// instead of HKDF-ing it with the ciphertext and public key.
//
// Returns 1 on success and 0 otherwise.
static int t25519_decaps(uint8_t *shared_secret, const uint8_t *ciphertext,
                         const uint8_t *secret_key) {
  return X25519(shared_secret, secret_key, ciphertext);
}

const KEM_METHOD kemlike_t25519_method = {t25519_keygen_deterministic, NULL,
                                          t25519_encaps_deterministic, NULL,
                                          t25519_decaps};
const KEM kemlike_t25519 = {
    0,
    0,
    1,
    "KEM-like X25519",
    T25519_PUBLIC_KEY_BYTES,
    T25519_SECRET_KEY_BYTES,
    T25519_CIPHERTEXT_BYTES,
    T25519_SHARED_SECRET_LEN,
    T25519_KEYGEN_SEED_LEN,
    T25519_ENCAPS_SEED_LEN,
    &kemlike_t25519_method,
};

// 1.2 NIST-P Helper Functions
// ---------------------------
//
// NOTE: These helpers are not maximally performant. They make lots of
// unnecessary heap allocations which can be avoided by adding new EC functions.

// Deterministically generate an EC key.
//
// Uses a seed of length [group order] + [128 extra bits] to deterministically
// generate a key. The extra bits ensure that the bias is negligible. With 128
// extra bits, the bias is <=2^(-128). This method is described in Section
// A.2.1 of FIPS 186-5 and Section 5.6.1.2.1 of NIST.SP.800-56Ar3.
//
// It does NOT match DeriveKeyPair in RFC 9180 which does rejection sampling.
//
// Returns a newly allocated EC_KEY on success, and NULL otherwise.
static EC_KEY *nistp_internal_keygen_deterministic(const EC_GROUP *group,
                                                   const uint8_t *seed,
                                                   size_t seed_len) {
  // Ensure that the seed is long enough.
  if ((seed_len * 8) !=
      ((size_t)EC_GROUP_order_bits(group) + (NISTP_EXTRA_BYTES * 8))) {
    return NULL;
  }

  EC_KEY *ret = NULL;

  // Convert seed into an integer mod order, per Section A.4.1 in FIPS 186-5.
  // We can skip the bias calculation since we already verified that
  // |seed_len| is large enough per Table A.2 of FIPS 186-5. Use Montgomery
  // reduction like |EC_KEY_derive_from_secret|.
  BIGNUM *secret_key_num = BN_bin2bn(seed, seed_len, NULL);
  BN_CTX *ctx = BN_CTX_new();
  EC_KEY *eckey = EC_KEY_new();
  EC_POINT *public_key_point = EC_POINT_new(group);
  if ((secret_key_num == NULL) || (ctx == NULL) || (eckey == NULL) ||
      (public_key_point == NULL) ||
      !BN_from_montgomery(secret_key_num, secret_key_num, &group->order, ctx) ||
      !BN_to_montgomery(secret_key_num, secret_key_num, &group->order, ctx) ||
      // Construct an EC_KEY struct and verify that it passes FIPS checks
      !EC_POINT_mul(group, public_key_point, secret_key_num, NULL, NULL, ctx) ||
      !EC_KEY_set_group(eckey, group) ||
      !EC_KEY_set_private_key(eckey, secret_key_num) ||
      !EC_KEY_set_public_key(eckey, public_key_point) ||
      !EC_KEY_check_fips(eckey)) {
    goto end;
  }
  ret = eckey;
end:
  BN_free(secret_key_num);
  BN_CTX_free(ctx);
  EC_POINT_free(public_key_point);
  if (ret == NULL) {
    EC_KEY_free(eckey);
  }
  return ret;
}

// NIST-P secret keys are scalars. This function writes the secret key to
// |secret_key| as a big-endian integer, padded with zeros to length
// |secret_key_len|.
//
// It matches SerializePrivateKey in RFC 9180.
static int nistp_serialize_secret_key(uint8_t *secret_key,
                                      size_t secret_key_len,
                                      const EC_KEY *eckey) {
  return BN_bn2bin_padded(secret_key, secret_key_len,
                          EC_KEY_get0_private_key(eckey));
}

// This function parses the |secret_key| buffer back into a scalar, checks
// that it is not zero, and returns a freshly allocated |EC_KEY| on success,
// and NULL on error.
//
// It matches DeserializePrivateKey in RFC 9180.
static EC_KEY *nistp_deserialize_secret_key(const uint8_t *secret_key,
                                            size_t secret_key_len,
                                            const EC_GROUP *group) {
  BIGNUM *secret_key_num = BN_bin2bn(secret_key, secret_key_len, NULL);
  EC_KEY *eckey = EC_KEY_new();
  if ((secret_key_num == NULL) || (eckey == NULL) ||
      !EC_KEY_set_group(eckey, group) ||
      !EC_KEY_set_private_key(eckey, secret_key_num)) {
    BN_free(secret_key_num);
    EC_KEY_free(eckey);
    return NULL;
  }

  BN_free(secret_key_num);
  return eckey;
}

// NIST-P public keys are elliptic curve points. This function writes the public
// key to |public_key| as an uncompressed point, to length |secret_key_len|.
//
// It matches SerializePublicKey in RFC 9180.
static int nistp_serialize_public_key(uint8_t *public_key,
                                      size_t public_key_len,
                                      const EC_KEY *eckey) {
  return (EC_POINT_point2oct(EC_KEY_get0_group(eckey),
                             EC_KEY_get0_public_key(eckey),
                             POINT_CONVERSION_UNCOMPRESSED, public_key,
                             public_key_len, NULL) == public_key_len);
}

// This function parses the |public_key| buffer back into an elliptic curve
// point, and returns a freshly allocated |EC_KEY| on success, and NULL on
// error. It does not perform validity checks on the public key.
//
// Its API matches DeserializePrivateKey in RFC 9180.
static EC_KEY *nistp_deserialize_public_key_unchecked(const uint8_t *public_key,
                                                      size_t public_key_len,
                                                      const EC_GROUP *group) {
  EC_POINT *point = EC_POINT_new(group);
  EC_KEY *eckey = EC_KEY_new();
  if ((point == NULL) || (eckey == NULL) ||
      !EC_POINT_oct2point(group, point, public_key, public_key_len, NULL) ||
      !EC_KEY_set_group(eckey, group) || !EC_KEY_set_public_key(eckey, point)) {
    EC_POINT_free(point);
    EC_KEY_free(eckey);
    return NULL;
  }
  EC_POINT_free(point);
  return eckey;
}

// Deterministically generate a NIST-P keypair.
//
// The public key and secret key format matches RFC 9180. See docstring of
// |nistp_internal_keygen_deterministic| for implementation details.
//
// Returns 1 on success and 0 otherwise.
static int nistp_keygen_deterministic(const EC_GROUP *group,
                                      uint8_t *public_key,
                                      size_t public_key_len,
                                      uint8_t *secret_key,
                                      size_t secret_key_len,
                                      const uint8_t *seed, size_t seed_len) {
  int ret = 0;
  EC_KEY *eckey = nistp_internal_keygen_deterministic(group, seed, seed_len);
  if ((eckey == NULL) ||
      !nistp_serialize_secret_key(secret_key, secret_key_len, eckey) ||
      !nistp_serialize_public_key(public_key, public_key_len, eckey)) {
    goto end;
  }
  ret = 1;
end:
  EC_KEY_free(eckey);
  return ret;
}

// Encapsulate to a NIST-P public key.
//
// Similar to DHKEM.Encap in RFC 9180, except it returns the raw dh value
// instead of HKDF-ing it with the ciphertext and public key.
//
// Returns 1 on success and 0 otherwise.
static int nistp_encaps_deterministic(
    const EC_GROUP *group, uint8_t *ciphertext, size_t ciphertext_len,
    uint8_t *shared_secret, size_t shared_secret_len, const uint8_t *public_key,
    size_t public_key_len, const uint8_t *seed, size_t seed_len) {
  EC_KEY *eckey = nistp_internal_keygen_deterministic(group, seed, seed_len);
  EC_KEY *peer_eckey = NULL;
  int ret = 0;
  if ((eckey == NULL) ||
      !nistp_serialize_public_key(ciphertext, ciphertext_len, eckey)) {
    goto end;
  }
  // Unchecked deserialization is okay, since |ECDH_compute_key_fips| performs
  // the necessary |EC_KEY_check_fips|.
  peer_eckey =
      nistp_deserialize_public_key_unchecked(public_key, public_key_len, group);
  if ((peer_eckey == NULL) ||
      !ECDH_compute_key_fips(shared_secret, shared_secret_len,
                             EC_KEY_get0_public_key(peer_eckey), eckey)) {
    goto end;
  }
  ret = 1;
end:
  EC_KEY_free(eckey);
  EC_KEY_free(peer_eckey);
  return ret;
}

// Decapsulate to a NIST-P secret key.
//
// Similar to DHKEM.Decap in RFC 9180, except it returns the raw dh value
// instead of HKDF-ing it with the ciphertext and public key.
//
// Returns 1 on success and 0 otherwise.
static int nistp_decaps(const EC_GROUP *group, uint8_t *shared_secret,
                        size_t shared_secret_len, const uint8_t *ciphertext,
                        size_t ciphertext_len, const uint8_t *secret_key,
                        size_t secret_key_len) {
  int ret = 0;
  EC_KEY *eckey =
      nistp_deserialize_secret_key(secret_key, secret_key_len, group);
  // Unchecked deserialization is okay, since |ECDH_compute_key_fips| performs
  // the necessary |EC_KEY_check_fips|.
  EC_KEY *peer_eckey =
      nistp_deserialize_public_key_unchecked(ciphertext, ciphertext_len, group);
  if ((eckey == NULL) || (peer_eckey == NULL) ||
      !ECDH_compute_key_fips(shared_secret, shared_secret_len,
                             EC_KEY_get0_public_key(peer_eckey), eckey)) {
    goto end;
  }
  ret = 1;
end:
  EC_KEY_free(eckey);
  EC_KEY_free(peer_eckey);
  return ret;
}

// 1.3 P256 Wrappers
// -----------------

static int t256_keygen_deterministic(uint8_t *public_key, uint8_t *secret_key,
                                     const uint8_t *seed) {
  return nistp_keygen_deterministic(
      EC_group_p256(), public_key, T256_PUBLIC_KEY_BYTES, secret_key,
      T256_SECRET_KEY_BYTES, seed, T256_KEYGEN_SEED_LEN);
}
static int t256_encaps_deterministic(uint8_t *ciphertext,
                                     uint8_t *shared_secret,
                                     const uint8_t *public_key,
                                     const uint8_t *seed) {
  return nistp_encaps_deterministic(
      EC_group_p256(), ciphertext, T256_CIPHERTEXT_BYTES, shared_secret,
      T256_SHARED_SECRET_LEN, public_key, T256_PUBLIC_KEY_BYTES, seed,
      T256_ENCAPS_SEED_LEN);
}

static int t256_decaps(uint8_t *shared_secret, const uint8_t *ciphertext,
                       const uint8_t *secret_key) {
  return nistp_decaps(EC_group_p256(), shared_secret, T256_SHARED_SECRET_LEN,
                      ciphertext, T256_CIPHERTEXT_BYTES, secret_key,
                      T256_SECRET_KEY_BYTES);
}

const KEM_METHOD kemlike_t256_method = {t256_keygen_deterministic, NULL,
                                        t256_encaps_deterministic, NULL,
                                        t256_decaps};
const KEM kemlike_t256 = {
    0,
    0,
    1,
    "KEM-like T256",
    T256_PUBLIC_KEY_BYTES,
    T256_SECRET_KEY_BYTES,
    T256_CIPHERTEXT_BYTES,
    T256_SHARED_SECRET_LEN,
    T256_KEYGEN_SEED_LEN,
    T256_ENCAPS_SEED_LEN,
    &kemlike_t256_method,
};

// 1.4 P384 Wrappers
// -----------------

static int t384_keygen_deterministic(uint8_t *public_key, uint8_t *secret_key,
                                     const uint8_t *seed) {
  return nistp_keygen_deterministic(
      EC_group_p384(), public_key, T384_PUBLIC_KEY_BYTES, secret_key,
      T384_SECRET_KEY_BYTES, seed, T384_KEYGEN_SEED_LEN);
}

static int t384_encaps_deterministic(uint8_t *ciphertext,
                                     uint8_t *shared_secret,
                                     const uint8_t *public_key,
                                     const uint8_t *seed) {
  return nistp_encaps_deterministic(
      EC_group_p384(), ciphertext, T384_CIPHERTEXT_BYTES, shared_secret,
      T384_SHARED_SECRET_LEN, public_key, T384_PUBLIC_KEY_BYTES, seed,
      T384_ENCAPS_SEED_LEN);
}

static int t384_decaps(uint8_t *shared_secret, const uint8_t *ciphertext,
                       const uint8_t *secret_key) {
  return nistp_decaps(EC_group_p384(), shared_secret, T384_SHARED_SECRET_LEN,
                      ciphertext, T384_CIPHERTEXT_BYTES, secret_key,
                      T384_SECRET_KEY_BYTES);
}

const KEM_METHOD kemlike_t384_method = {t384_keygen_deterministic, NULL,
                                        t384_encaps_deterministic, NULL,
                                        t384_decaps};
const KEM kemlike_t384 = {
    0,
    0,
    1,
    "KEM-like T384",
    T384_PUBLIC_KEY_BYTES,
    T384_SECRET_KEY_BYTES,
    T384_CIPHERTEXT_BYTES,
    T384_SHARED_SECRET_LEN,
    T384_KEYGEN_SEED_LEN,
    T384_ENCAPS_SEED_LEN,
    &kemlike_t384_method,
};

// 2. Combiner Implementation
// --------------------------

// Computes HKDF(key = combined_shared_secrets,
//               salt = t_public_key || t_ciphertext,
//               label)
// using |digest|, and outputs 32 bytes to |shared_secret|.
// Returns 1 on success and 0 otherwise.
static int pqt_combiner(const EVP_MD *digest, const uint8_t *label,
                        uint8_t *shared_secret,
                        const uint8_t *concat_shared_secrets,
                        size_t concat_shared_secrets_len,
                        const uint8_t *t_public_key, size_t t_public_key_len,
                        const uint8_t *t_ciphertext, size_t t_ciphertext_len) {
  uint8_t salt[PQT_MAX_SALT_BYTES] = {0};
  size_t salt_len = t_ciphertext_len + t_public_key_len;
  OPENSSL_memcpy(salt, t_public_key, t_public_key_len);
  OPENSSL_memcpy(salt + t_public_key_len, t_ciphertext, t_ciphertext_len);
  return HKDF(shared_secret, PQT_SHARED_SECRET_LEN, digest,
              concat_shared_secrets, concat_shared_secrets_len, salt, salt_len,
              label, PQT_LABEL_LEN);
}

// 3. Keygen Implementation
// -------------------------

static int pqt_keygen_deterministic(const KEM *pq, const KEM *t,
                                    uint8_t *public_key, uint8_t *secret_key,
                                    const uint8_t *seed) {
  if (!pq->method->keygen_deterministic(public_key, secret_key, seed) ||
      !t->method->keygen_deterministic(public_key + pq->public_key_len,
                                       secret_key + pq->secret_key_len,
                                       seed + pq->keygen_seed_len)) {
    return 0;
  }
  // Append [t public key] to the end of the secret key
  OPENSSL_memcpy(secret_key + pq->secret_key_len + t->secret_key_len,
                 public_key + pq->public_key_len, t->public_key_len);
  return 1;
}

// 4. Encaps Implementation
// ------------------------

static int pqt_encaps_deterministic(const KEM *pq, const KEM *t,
                                    const EVP_MD *digest, const uint8_t *label,
                                    uint8_t *ciphertext, uint8_t *shared_secret,
                                    const uint8_t *public_key,
                                    const uint8_t *seed) {
  int ret = 0;
  uint8_t concat_ss[PQT_MAX_CONCAT_SHARED_SECRET_BYTES] = {0};
  if (!pq->method->encaps_deterministic(ciphertext, concat_ss, public_key,
                                        seed) ||
      !t->method->encaps_deterministic(
          ciphertext + pq->ciphertext_len, concat_ss + pq->shared_secret_len,
          public_key + pq->public_key_len, seed + pq->encaps_seed_len)) {
    goto end;
  }
  ret = pqt_combiner(digest, label, shared_secret, concat_ss,
                     pq->shared_secret_len + t->shared_secret_len,
                     public_key + pq->public_key_len, t->public_key_len,
                     ciphertext + pq->ciphertext_len, t->ciphertext_len);
end:
  OPENSSL_cleanse(concat_ss, PQT_MAX_CONCAT_SHARED_SECRET_BYTES);
  return ret;
}

// 5. Decaps Implementation
// ------------------------

static int pqt_decaps(const KEM *pq, const KEM *t, const EVP_MD *digest,
                      const uint8_t *label, uint8_t *shared_secret,
                      const uint8_t *ciphertext, const uint8_t *secret_key) {
  int ret = 0;
  uint8_t concat_ss[PQT_MAX_CONCAT_SHARED_SECRET_BYTES] = {0};
  if (!pq->method->decaps(concat_ss, ciphertext, secret_key) ||
      !t->method->decaps(concat_ss + pq->shared_secret_len,
                         ciphertext + pq->ciphertext_len,
                         secret_key + pq->secret_key_len)) {
    goto end;
  }
  // Recover [t public key] from the end of secret key.
  const uint8_t *t_public_key =
      secret_key + pq->secret_key_len + t->secret_key_len;
  ret = pqt_combiner(digest, label, shared_secret, concat_ss,
                     pq->shared_secret_len + t->shared_secret_len, t_public_key,
                     t->public_key_len, ciphertext + pq->ciphertext_len,
                     t->ciphertext_len);
end:
  OPENSSL_cleanse(concat_ss, PQT_MAX_CONCAT_SHARED_SECRET_BYTES);
  return ret;
}

// 6. Instantiations
// -----------------

// 6.1 PQT25519
// ------------

int pqt25519_keygen_deterministic(uint8_t *public_key, uint8_t *secret_key,
                                  const uint8_t *seed) {
  return pqt_keygen_deterministic(KEM_find_kem_by_nid(NID_MLKEM768IPD),
                                  &kemlike_t25519, public_key, secret_key,
                                  seed);
}

int pqt25519_keygen(uint8_t *public_key, uint8_t *secret_key) {
  uint8_t seed[PQT25519_KEYGEN_SEED_LEN];
  RAND_bytes(seed, PQT25519_KEYGEN_SEED_LEN);
  return pqt25519_keygen_deterministic(public_key, secret_key, seed);
}

int pqt25519_encaps_deterministic(uint8_t *ciphertext, uint8_t *shared_secret,
                                  const uint8_t *public_key,
                                  const uint8_t *seed) {
  return pqt_encaps_deterministic(
      KEM_find_kem_by_nid(NID_MLKEM768IPD), &kemlike_t25519, PQT25519_DIGEST(),
      PQT25519_LABEL, ciphertext, shared_secret, public_key, seed);
}

int pqt25519_encaps(uint8_t *ciphertext, uint8_t *shared_secret,
                    const uint8_t *public_key) {
  uint8_t seed[PQT25519_ENCAPS_SEED_LEN];
  RAND_bytes(seed, PQT25519_ENCAPS_SEED_LEN);
  return pqt25519_encaps_deterministic(ciphertext, shared_secret, public_key,
                                       seed);
}

int pqt25519_decaps(uint8_t *shared_secret, const uint8_t *ciphertext,
                    const uint8_t *secret_key) {
  return pqt_decaps(KEM_find_kem_by_nid(NID_MLKEM768IPD), &kemlike_t25519,
                    PQT25519_DIGEST(), PQT25519_LABEL, shared_secret,
                    ciphertext, secret_key);
}

// 6.2 PQT256
// ----------

int pqt256_keygen_deterministic(uint8_t *public_key, uint8_t *secret_key,
                                const uint8_t *seed) {
  return pqt_keygen_deterministic(KEM_find_kem_by_nid(NID_MLKEM768IPD),
                                  &kemlike_t256, public_key, secret_key, seed);
}

int pqt256_keygen(uint8_t *public_key, uint8_t *secret_key) {
  uint8_t seed[PQT256_KEYGEN_SEED_LEN];
  RAND_bytes(seed, PQT256_KEYGEN_SEED_LEN);
  return pqt256_keygen_deterministic(public_key, secret_key, seed);
}

int pqt256_encaps_deterministic(uint8_t *ciphertext, uint8_t *shared_secret,
                                const uint8_t *public_key,
                                const uint8_t *seed) {
  return pqt_encaps_deterministic(KEM_find_kem_by_nid(NID_MLKEM768IPD),
                                  &kemlike_t256, PQT256_DIGEST(), PQT256_LABEL,
                                  ciphertext, shared_secret, public_key, seed);
}

int pqt256_encaps(uint8_t *ciphertext, uint8_t *shared_secret,
                  const uint8_t *public_key) {
  uint8_t seed[PQT256_ENCAPS_SEED_LEN];
  RAND_bytes(seed, PQT256_ENCAPS_SEED_LEN);
  return pqt256_encaps_deterministic(ciphertext, shared_secret, public_key,
                                     seed);
}

int pqt256_decaps(uint8_t *shared_secret, const uint8_t *ciphertext,
                  const uint8_t *secret_key) {
  return pqt_decaps(KEM_find_kem_by_nid(NID_MLKEM768IPD), &kemlike_t256,
                    PQT256_DIGEST(), PQT256_LABEL, shared_secret, ciphertext,
                    secret_key);
}

// 6.3 PQT384
// ----------

int pqt384_keygen_deterministic(uint8_t *public_key, uint8_t *secret_key,
                                const uint8_t *seed) {
  return pqt_keygen_deterministic(KEM_find_kem_by_nid(NID_MLKEM1024IPD),
                                  &kemlike_t384, public_key, secret_key, seed);
}

int pqt384_keygen(uint8_t *public_key, uint8_t *secret_key) {
  uint8_t seed[PQT384_KEYGEN_SEED_LEN];
  RAND_bytes(seed, PQT384_KEYGEN_SEED_LEN);
  return pqt384_keygen_deterministic(public_key, secret_key, seed);
}

int pqt384_encaps_deterministic(uint8_t *ciphertext, uint8_t *shared_secret,
                                const uint8_t *public_key,
                                const uint8_t *seed) {
  return pqt_encaps_deterministic(KEM_find_kem_by_nid(NID_MLKEM1024IPD),
                                  &kemlike_t384, PQT384_DIGEST(), PQT384_LABEL,
                                  ciphertext, shared_secret, public_key, seed);
}

int pqt384_encaps(uint8_t *ciphertext, uint8_t *shared_secret,
                  const uint8_t *public_key) {
  uint8_t seed[PQT384_ENCAPS_SEED_LEN];
  RAND_bytes(seed, PQT384_ENCAPS_SEED_LEN);
  return pqt384_encaps_deterministic(ciphertext, shared_secret, public_key,
                                     seed);
}

int pqt384_decaps(uint8_t *shared_secret, const uint8_t *ciphertext,
                  const uint8_t *secret_key) {
  return pqt_decaps(KEM_find_kem_by_nid(NID_MLKEM1024IPD), &kemlike_t384,
                    PQT384_DIGEST(), PQT384_LABEL, shared_secret, ciphertext,
                    secret_key);
}
