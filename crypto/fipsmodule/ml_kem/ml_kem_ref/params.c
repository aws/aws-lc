#include <openssl/base.h>

#include "params.h"

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

void ml_kem_512_params_init(ml_kem_params *params) {
  ml_kem_params_init(params, 2);
}
void ml_kem_768_params_init(ml_kem_params *params) {
  ml_kem_params_init(params, 3);
}
void ml_kem_1024_params_init(ml_kem_params *params) {
  ml_kem_params_init(params, 4);
}

