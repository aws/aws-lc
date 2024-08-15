#ifndef PARAMS_H
#define PARAMS_H

#include <openssl/base.h>
#include <assert.h>

// The only defined parameters are those that don't depend
// on the parameter set. All other parameters are specified
// in ml_kem_params structure that is unique for each parameter
// set (ML-KEM 512/768/1024).
#define KYBER_N 256
#define KYBER_Q 3329

#define KYBER_SYMBYTES 32   /* size in bytes of hashes, and seeds */
#define KYBER_SSBYTES  32   /* size in bytes of shared key */

#define KYBER_POLYBYTES		384

#define KYBER_ETA2 2

#define KYBER_INDCPA_MSGBYTES       (KYBER_SYMBYTES)

// Structure for ML-KEM parameters that depend on the parameter set.
typedef struct {
  size_t k;
  size_t eta1;
  size_t poly_compressed_bytes;
  size_t poly_vec_bytes;
  size_t poly_vec_compressed_bytes;
  size_t indcpa_public_key_bytes;
  size_t indcpa_secret_key_bytes;
  size_t indcpa_bytes;
  size_t public_key_bytes;
  size_t secret_key_bytes;
  size_t ciphertext_bytes;
} ml_kem_params;

static void ml_kem_params_init(ml_kem_params *params, size_t k) {
  assert((k == 2) || (k == 3) || (k == 4));

  size_t eta1 = (k == 2) ? 3 : 2;
  size_t poly_compressed_bytes = (k == 4) ? 160 : 128;
  size_t poly_vec_bytes = k * KYBER_POLYBYTES;
  size_t poly_vec_compressed_bytes = (k == 4) ? (352 * k) : (320 * k);
  size_t indcpa_public_key_bytes = poly_vec_bytes + KYBER_SYMBYTES;
  size_t indcpa_secret_key_bytes = poly_vec_bytes;
  size_t indcpa_bytes = poly_vec_compressed_bytes + poly_compressed_bytes;
  size_t public_key_bytes = indcpa_public_key_bytes;
  size_t secret_key_bytes = indcpa_secret_key_bytes + indcpa_public_key_bytes + 2*KYBER_SYMBYTES;
  size_t ciphertext_bytes = indcpa_bytes;

  params->k = k;
  params->eta1 = eta1;
  params->poly_compressed_bytes = poly_compressed_bytes;
  params->poly_vec_bytes = poly_vec_bytes;
  params->poly_vec_compressed_bytes = poly_vec_compressed_bytes;
  params->indcpa_public_key_bytes = indcpa_public_key_bytes;
  params->indcpa_secret_key_bytes = indcpa_secret_key_bytes;
  params->indcpa_bytes = indcpa_bytes;
  params->public_key_bytes = public_key_bytes;
  params->secret_key_bytes = secret_key_bytes;
  params->ciphertext_bytes = ciphertext_bytes;
}

OPENSSL_UNUSED static void ml_kem_512_params_init(ml_kem_params *params) {
  ml_kem_params_init(params, 2);
}
OPENSSL_UNUSED static void ml_kem_768_params_init(ml_kem_params *params) {
  ml_kem_params_init(params, 3);
}
OPENSSL_UNUSED static void ml_kem_1024_params_init(ml_kem_params *params) {
  ml_kem_params_init(params, 4);
}

// We define max values for some parameters because they are used
// for static allocation.
#define KYBER_K_MAX (4)
#define KYBER_ETA1_MAX (3)
#define KYBER_POLYCOMPRESSEDBYTES_MAX    (160)
#define KYBER_POLYVECCOMPRESSEDBYTES_MAX (4 * 352)

#define KYBER_INDCPA_BYTES_MAX    (KYBER_POLYVECCOMPRESSEDBYTES_MAX + KYBER_POLYCOMPRESSEDBYTES_MAX)
#define KYBER_CIPHERTEXTBYTES_MAX (KYBER_INDCPA_BYTES_MAX)

#define KYBER_NAMESPACE(s) ml_kem_##s##_ref

#endif
