// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "pqt_kem.h"

#include <openssl/digest.h>
#include <openssl/ecdh.h>
#include <openssl/hkdf.h>
#include <openssl/rand.h>
#include "openssl/bn.h"

// |nistp_internal_keygen_deterministic| needs this for montgomery reduction.
#include "../fipsmodule/ec/internal.h"

#include "../internal.h"

// HKDF Labels
#define PQT25519_LABEL "PQT255-v1"
#define PQT256_LABEL "PQT256-v1"
#define PQT384_LABEL "PQT384-v1"
#define PQT_LABEL_LEN 9

// 1. PQ KEM Wrappers
// ------------------
// All wrappers return one on success and zero on error.
// ml_kem_* functions, imported from Kyber upstream, return 0 on success.

// 1.1 ML-KEM-768 Wrappers
// -----------------------

static int pq768_keygen_deterministic(uint8_t *public_key, uint8_t *secret_key,
                                      const uint8_t *seed) {
  return (ml_kem_768_ipd_keypair_deterministic(public_key, secret_key, seed) ==
          0);
}

static int pq768_encaps_deterministic(uint8_t *ciphertext,
                                      uint8_t *shared_secret,
                                      const uint8_t *public_key,
                                      const uint8_t *seed) {
  return (ml_kem_768_ipd_encapsulate_deterministic(ciphertext, shared_secret,
                                                   public_key, seed) == 0);
}

static int pq768_decaps(uint8_t *shared_secret, const uint8_t *ciphertext,
                        const uint8_t *secret_key) {
  return (ml_kem_768_ipd_decapsulate(shared_secret, ciphertext, secret_key) ==
          0);
}

// 1.2 ML-KEM-1024 Wrappers
// ------------------------

static int pq1024_keygen_deterministic(uint8_t *public_key, uint8_t *secret_key,
                                       const uint8_t *seed) {
  return (ml_kem_1024_ipd_keypair_deterministic(public_key, secret_key, seed) ==
          0);
}

static int pq1024_encaps_deterministic(uint8_t *ciphertext,
                                       uint8_t *shared_secret,
                                       const uint8_t *public_key,
                                       const uint8_t *seed) {
  return (ml_kem_1024_ipd_encapsulate_deterministic(ciphertext, shared_secret,
                                                    public_key, seed) == 0);
}

static int pq1024_decaps(uint8_t *shared_secret, const uint8_t *ciphertext,
                         const uint8_t *secret_key) {
  return (ml_kem_1024_ipd_decapsulate(shared_secret, ciphertext, secret_key) ==
          0);
}

// 2. T KEM Wrappers
// -----------------
// All wrappers return one on success and zero on error.
//
// WARNING: These are internal functions and should not be used outside the PQ/T
// KEM construction.

// 2.1 X25518 Wrappers
// -------------------

static int t25519_keygen_deterministic(uint8_t *public_key, uint8_t *secret_key,
                                       const uint8_t *seed) {
  OPENSSL_memcpy(secret_key, seed, T25519_SECRET_KEY_BYTES);
  X25519_public_from_private(public_key, secret_key);
  return 1;
}

static int t25519_encaps_deterministic(uint8_t *ciphertext,
                                       uint8_t *shared_secret,
                                       const uint8_t *public_key,
                                       const uint8_t *seed) {
  X25519_public_from_private(ciphertext, seed);
  return X25519(shared_secret, seed, public_key);
}

static int t25519_decaps(uint8_t *shared_secret, const uint8_t *ciphertext,
                         const uint8_t *secret_key) {
  return X25519(shared_secret, secret_key, ciphertext);
}

// 2.2 NIST-P Helper Functions
// ---------------------------
//
// NOTE: These helpers are not maximally performant.
// 1. They make lots of unnecessary heap allocations which can be avoided by
//    adding new EC functions.
// 2. They do lots of expensive |EC_KEY_check_fips| checks, which be avoided by
//    careful refactoring.

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

  BN_CTX *ctx = BN_CTX_new();
  if (ctx == NULL) {
    return NULL;
  }
  // Convert seed into an integer mod order, per Section A.4.1 in FIPS 186-5.
  // We can skip the bias calculation since we already verified that
  // |seed_len| is large enough per Table A.2 of FIPS 186-5. Use Montgomery
  // reduction like |EC_KEY_derive_from_secret|.
  BIGNUM *secret_key_num = BN_bin2bn(seed, seed_len, NULL);
  if ((secret_key_num == NULL) ||
      !BN_from_montgomery(secret_key_num, secret_key_num, &group->order, ctx) ||
      !BN_to_montgomery(secret_key_num, secret_key_num, &group->order, ctx)) {
    BN_CTX_free(ctx);
    BN_free(secret_key_num);
    return NULL;
  }
  // Construct an EC_KEY struct and verify that it passes FIPS checks
  EC_KEY *eckey = EC_KEY_new();
  EC_POINT *public_key_point = EC_POINT_new(group);
  if ((eckey == NULL) || (public_key_point == NULL) ||
      !EC_POINT_mul(group, public_key_point, secret_key_num, NULL, NULL, ctx) ||
      !EC_KEY_set_group(eckey, group) ||
      !EC_KEY_set_private_key(eckey, secret_key_num) ||
      !EC_KEY_set_public_key(eckey, public_key_point) ||
      !EC_KEY_check_fips(eckey)) {
    BN_CTX_free(ctx);
    BN_free(secret_key_num);
    EC_POINT_free(public_key_point);
    EC_KEY_free(eckey);
    return NULL;
  }
  BN_CTX_free(ctx);
  BN_free(secret_key_num);
  EC_POINT_free(public_key_point);
  return eckey;
}

// NIST-P secret keys are scalars. This function does validity checks on the
// provided |eckey|, then writes the secret key to |secret_key| as a
// big-endian integer, padded with zeros to length |secret_key_len|.
//
// It matches SerializePrivateKey in RFC 9180.
static int nistp_serialize_secret_key(uint8_t *secret_key,
                                      size_t secret_key_len,
                                      const EC_KEY *eckey) {
  if (!EC_KEY_check_fips(eckey)) {
    return 0;
  }
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

// NIST-P public keys are elliptic curve points. This function does validity
// checks on the provided |eckey|, then writes the public key to |public_key|
// as an uncompressed point, to length |secret_key_len|.
//
// It matches SerializePublicKey in RFC 9180.
static int nistp_serialize_public_key(uint8_t *public_key,
                                      size_t public_key_len,
                                      const EC_KEY *eckey) {
  if (!EC_KEY_check_fips(eckey) ||
      (EC_POINT_point2oct(EC_KEY_get0_group(eckey),
                          EC_KEY_get0_public_key(eckey),
                          POINT_CONVERSION_UNCOMPRESSED, public_key,
                          public_key_len, NULL) != public_key_len)) {
    return 0;
  }
  return 1;
}

// This function parses the |public_key| buffer back into an elliptic curve
// point, checks that it is not zero, and returns a freshly allocated |EC_KEY|
// on success, and NULL on error.
//
// It matches DeserializePrivateKey in RFC 9180.
static EC_KEY *nistp_deserialize_public_key(const uint8_t *public_key,
                                            size_t public_key_len,
                                            const EC_GROUP *group) {
  EC_POINT *point = EC_POINT_new(group);
  EC_KEY *eckey = EC_KEY_new();
  if ((point == NULL) || (eckey == NULL) ||
      !EC_POINT_oct2point(group, point, public_key, public_key_len, NULL) ||
      !EC_KEY_set_group(eckey, group) || !EC_KEY_set_public_key(eckey, point) ||
      !EC_KEY_check_fips(eckey)) {
    EC_POINT_free(point);
    EC_KEY_free(eckey);
    return NULL;
  }

  EC_POINT_free(point);
  return eckey;
}

static int nistp_keygen_deterministic(const EC_GROUP *group,
                                      uint8_t *public_key,
                                      size_t public_key_len,
                                      uint8_t *secret_key,
                                      size_t secret_key_len,
                                      const uint8_t *seed, size_t seed_len) {
  EC_KEY *eckey = nistp_internal_keygen_deterministic(group, seed, seed_len);
  if ((eckey == NULL) ||
      !nistp_serialize_secret_key(secret_key, secret_key_len, eckey) ||
      !nistp_serialize_public_key(public_key, public_key_len, eckey)) {
    EC_KEY_free(eckey);
    return 0;
  }
  EC_KEY_free(eckey);
  return 1;
}

static int nistp_encaps_deterministic(
    const EC_GROUP *group, uint8_t *ciphertext, size_t ciphertext_len,
    uint8_t *shared_secret, size_t shared_secret_len, const uint8_t *public_key,
    size_t public_key_len, const uint8_t *seed, size_t seed_len) {
  EC_KEY *eckey = nistp_internal_keygen_deterministic(group, seed, seed_len);
  if ((eckey == NULL) ||
      !nistp_serialize_public_key(ciphertext, ciphertext_len, eckey)) {
    EC_KEY_free(eckey);
    return 0;
  }
  EC_KEY *peer_eckey =
      nistp_deserialize_public_key(public_key, public_key_len, group);
  if ((peer_eckey == NULL) ||
      !ECDH_compute_key_fips(shared_secret, shared_secret_len,
                             EC_KEY_get0_public_key(peer_eckey), eckey)) {
    EC_KEY_free(eckey);
    EC_KEY_free(peer_eckey);
    return 0;
  }
  EC_KEY_free(eckey);
  EC_KEY_free(peer_eckey);
  return 1;
}

static int nistp_decaps(const EC_GROUP *group, uint8_t *shared_secret,
                        size_t shared_secret_len, const uint8_t *ciphertext,
                        size_t ciphertext_len, const uint8_t *secret_key,
                        size_t secret_key_len) {
  EC_KEY *eckey =
      nistp_deserialize_secret_key(secret_key, secret_key_len, group);
  EC_KEY *peer_eckey =
      nistp_deserialize_public_key(ciphertext, ciphertext_len, group);
  if ((eckey == NULL) || (peer_eckey == NULL) ||
      !ECDH_compute_key_fips(shared_secret, shared_secret_len,
                             EC_KEY_get0_public_key(peer_eckey), eckey)) {
    EC_KEY_free(eckey);
    EC_KEY_free(peer_eckey);
    return 0;
  }
  EC_KEY_free(eckey);
  EC_KEY_free(peer_eckey);
  return 1;
}

// 2.3 P256 Wrappers
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

// 2.4 P384 Wrappers
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

// 3. Combiner Implementation
// --------------------------

// Computes HKDF(key = t_ss || pq_ss, salt = t_ct || t_pk, fixed label)
// Returns 1 on success and 0 otherwise.
#define GenerateCombiner(pqparam, tparam, evpdigest)                           \
  static int pqt##tparam##_combiner(                                           \
      uint8_t *shared_secret,                                                  \
      const uint8_t concat_shared_secrets[T##tparam##_SHARED_SECRET_LEN +      \
                                          PQ##pqparam##_SHARED_SECRET_LEN],    \
      const uint8_t *t_ciphertext, const uint8_t *t_public_key) {              \
    const EVP_MD *digest = evpdigest();                                        \
    uint8_t salt[T##tparam##_CIPHERTEXT_BYTES + T##tparam##_PUBLIC_KEY_BYTES]; \
    size_t salt_len =                                                          \
        T##tparam##_CIPHERTEXT_BYTES + T##tparam##_PUBLIC_KEY_BYTES;           \
    OPENSSL_memcpy(salt, t_public_key, T##tparam##_PUBLIC_KEY_BYTES);          \
    OPENSSL_memcpy(salt + T##tparam##_PUBLIC_KEY_BYTES, t_ciphertext,          \
                   T##tparam##_CIPHERTEXT_BYTES);                              \
                                                                               \
    uint8_t info[PQT_LABEL_LEN] = PQT##tparam##_LABEL;                         \
    size_t info_len = PQT_LABEL_LEN;                                           \
                                                                               \
    return HKDF(                                                               \
        shared_secret, PQT_SHARED_SECRET_LEN, digest, concat_shared_secrets,   \
        T##tparam##_SHARED_SECRET_LEN + PQ##pqparam##_SHARED_SECRET_LEN, salt, \
        salt_len, info, info_len);                                             \
  }


// 4. Keygen Implementation
// ------------------------

#define GenerateKeyGen(pqparam, tparam)                                      \
  int pqt##tparam##_keygen_deterministic(                                    \
      uint8_t *public_key, uint8_t *secret_key, const uint8_t *seed) {       \
    uint8_t *pq_public_key = public_key;                                     \
    uint8_t *t_public_key = public_key + PQ##pqparam##_PUBLIC_KEY_BYTES;     \
    uint8_t *pq_secret_key = secret_key;                                     \
    uint8_t *t_secret_key = secret_key + PQ##pqparam##_SECRET_KEY_BYTES;     \
    const uint8_t *pq_seed = seed;                                           \
    const uint8_t *t_seed = seed + PQ##pqparam##_KEYGEN_SEED_LEN;            \
                                                                             \
    if (!pq##pqparam##_keygen_deterministic(pq_public_key, pq_secret_key,    \
                                            pq_seed)) {                      \
      return 0;                                                              \
    }                                                                        \
    if (!t##tparam##_keygen_deterministic(t_public_key, t_secret_key,        \
                                          t_seed)) {                         \
      return 0;                                                              \
    }                                                                        \
                                                                             \
    /* Append the T public key at the end of the secret key, for easy access \
     */                                                                      \
    OPENSSL_memcpy(secret_key + PQ##pqparam##_SECRET_KEY_BYTES +             \
                       T##tparam##_SECRET_KEY_BYTES,                         \
                   t_public_key, T##tparam##_PUBLIC_KEY_BYTES);              \
                                                                             \
    return 1;                                                                \
  }                                                                          \
  int pqt##tparam##_keygen(uint8_t *public_key, uint8_t *secret_key) {       \
    uint8_t seed[PQT##tparam##_KEYGEN_SEED_LEN];                             \
    RAND_bytes(seed, PQT##tparam##_KEYGEN_SEED_LEN);                         \
    return pqt##tparam##_keygen_deterministic(public_key, secret_key, seed); \
  }

// 5. Encaps Implementation
// ------------------------

#define GenerateEncaps(pqparam, tparam)                                        \
  int pqt##tparam##_encaps_deterministic(                                      \
      uint8_t *ciphertext, uint8_t *shared_secret, const uint8_t *public_key,  \
      const uint8_t *seed) {                                                   \
    uint8_t *pq_ciphertext = ciphertext;                                       \
    uint8_t *t_ciphertext = ciphertext + PQ##pqparam##_CIPHERTEXT_BYTES;       \
    const uint8_t *pq_public_key = public_key;                                 \
    const uint8_t *t_public_key = public_key + PQ##pqparam##_PUBLIC_KEY_BYTES; \
    const uint8_t *pq_seed = seed;                                             \
    const uint8_t *t_seed = seed + PQ##pqparam##_ENCAPS_SEED_LEN;              \
                                                                               \
    /* Create a buffer to hold concatenated shared secrets */                  \
    uint8_t concat_shared_secrets[T##tparam##_SHARED_SECRET_LEN +              \
                                  PQ##pqparam##_SHARED_SECRET_LEN] = {0};      \
    uint8_t *t_shared_secret = concat_shared_secrets;                          \
    uint8_t *pq_shared_secret =                                                \
        concat_shared_secrets + T##tparam##_SHARED_SECRET_LEN;                 \
                                                                               \
    if (!pq##pqparam##_encaps_deterministic(pq_ciphertext, pq_shared_secret,   \
                                            pq_public_key, pq_seed)) {         \
      return 0;                                                                \
    }                                                                          \
    if (!t##tparam##_encaps_deterministic(t_ciphertext, t_shared_secret,       \
                                          t_public_key, t_seed)) {             \
      return 0;                                                                \
    }                                                                          \
                                                                               \
    return pqt##tparam##_combiner(shared_secret, concat_shared_secrets,        \
                                  t_ciphertext, t_public_key);                 \
  }                                                                            \
  int pqt##tparam##_encaps(uint8_t *ciphertext, uint8_t *shared_secret,        \
                           const uint8_t *public_key) {                        \
    uint8_t seed[PQT##tparam##_ENCAPS_SEED_LEN];                               \
    RAND_bytes(seed, PQT##tparam##_ENCAPS_SEED_LEN);                           \
    return pqt##tparam##_encaps_deterministic(ciphertext, shared_secret,       \
                                              public_key, seed);               \
  }

// 6. Decaps Implementation
// ------------------------

#define GenerateDecaps(pqparam, tparam)                                        \
  int pqt##tparam##_decaps(uint8_t *shared_secret, const uint8_t *ciphertext,  \
                           const uint8_t *secret_key) {                        \
    const uint8_t *pq_ciphertext = ciphertext;                                 \
    const uint8_t *t_ciphertext = ciphertext + PQ##pqparam##_CIPHERTEXT_BYTES; \
    const uint8_t *pq_secret_key = secret_key;                                 \
    const uint8_t *t_secret_key = secret_key + PQ##pqparam##_SECRET_KEY_BYTES; \
                                                                               \
    /* Recover the T public key from the secret key */                         \
    const uint8_t *t_public_key = secret_key +                                 \
                                  PQ##pqparam##_SECRET_KEY_BYTES +             \
                                  T##tparam##_SECRET_KEY_BYTES;                \
                                                                               \
    /* Create a buffer to hold concatenated shared secrets */                  \
    uint8_t concat_shared_secrets[T##tparam##_SHARED_SECRET_LEN +              \
                                  PQ##pqparam##_SHARED_SECRET_LEN] = {0};      \
    uint8_t *t_shared_secret = concat_shared_secrets;                          \
    uint8_t *pq_shared_secret =                                                \
        concat_shared_secrets + T##tparam##_SHARED_SECRET_LEN;                 \
                                                                               \
    if (!pq##pqparam##_decaps(pq_shared_secret, pq_ciphertext,                 \
                              pq_secret_key)) {                                \
      return 0;                                                                \
    }                                                                          \
    if (!t##tparam##_decaps(t_shared_secret, t_ciphertext, t_secret_key)) {    \
      return 0;                                                                \
    }                                                                          \
                                                                               \
    return pqt##tparam##_combiner(shared_secret, concat_shared_secrets,        \
                                  t_ciphertext, t_public_key);                 \
  }

// 7. Instantiate Implementations
// ------------------------------

GenerateCombiner(768, 25519, PQT25519_DIGEST)
GenerateKeyGen(768, 25519)
GenerateEncaps(768, 25519)
GenerateDecaps(768, 25519)

GenerateCombiner(768, 256, PQT256_DIGEST)
GenerateKeyGen(768, 256)
GenerateEncaps(768, 256)
GenerateDecaps(768, 256)

GenerateCombiner(1024, 384, PQT384_DIGEST)
GenerateKeyGen(1024, 384)
GenerateEncaps(1024, 384)
GenerateDecaps(1024, 384)
