#ifndef ML_KEM_PARAMS_H
#define ML_KEM_PARAMS_H

#include <openssl/base.h>

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

// We define max values for some parameters because they are used
// for static allocation.
#define KYBER_K_MAX (4)
#define KYBER_ETA1_MAX (3)
#define KYBER_POLYCOMPRESSEDBYTES_MAX    (160)
#define KYBER_POLYVECCOMPRESSEDBYTES_MAX (4 * 352)

#define KYBER_INDCPA_BYTES_MAX    (KYBER_POLYVECCOMPRESSEDBYTES_MAX + KYBER_POLYCOMPRESSEDBYTES_MAX)
#define KYBER_CIPHERTEXTBYTES_MAX (KYBER_INDCPA_BYTES_MAX)

#define KYBER_NAMESPACE(s) ml_kem_##s##_ref

void ml_kem_512_params_init(ml_kem_params *params);
void ml_kem_768_params_init(ml_kem_params *params);
void ml_kem_1024_params_init(ml_kem_params *params);

#endif
