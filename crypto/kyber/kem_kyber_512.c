#include "../evp_extra/internal.h"
#include "../fipsmodule/evp/internal.h"
#include "kem_kyber.h"
#include "pqcrystals-kyber_kyber512_ref/api.h"

// Note: These methods currently default to using the reference code for Kyber.
// In a future where AWS-LC has optimized options available, those can be
// conditionally (or based on compile-time flags) called here, depending on
// platform support.

#define SUCCESS (1)
#define FAILURE (0)

int kyber512_keypair(uint8_t *public_key, uint8_t *secret_key) {
  return pqcrystals_kyber512_ref_keypair(public_key, secret_key);
}

int kyber512_encapsulate_init(void *ctx,
                              void *prov_key,
                              const OSSL_PARAM params[]) {
  // No initialization needed
  return SUCCESS;
}

int kyber512_encapsulate(void *ctx,
                         unsigned char *out,
                         size_t *out_len,
                         unsigned char *secret,
                         size_t *secret_len) {
  *out_len = KYBER512_KEM_CIPHERTEXT_BYTES;
  *secret_len = KYBER512_KEM_SHARED_SECRET_BYTES;
  if (out == NULL) { // Caller is performing a size check
    return SUCCESS;
  }

  if (ctx == NULL) {
    return FAILURE;
  }

  EVP_PKEY *pkey = ((EVP_PKEY_CTX *)ctx)->pkey;
  if (pkey != NULL &&
      pkey->type == NID_KYBER512 &&
      pkey->pkey.ptr != NULL) {
    KYBER512_KEY *key = pkey->pkey.ptr;
    pqcrystals_kyber512_ref_enc(out, secret, key->pub); // always returns 0
    return SUCCESS;
  }
  return FAILURE;
}

int kyber512_decapsulate_init(void *ctx,
                              void *prov_key,
                              const OSSL_PARAM params[]) {
  // No initialization needed
  return SUCCESS;
}

int kyber512_decapsulate(void *ctx,
                         unsigned char *out,
                         size_t *out_len,
                         const unsigned char *in,
                         size_t in_len)
{
  *out_len = KYBER512_KEM_SHARED_SECRET_BYTES;
  if (out == NULL) { // Caller is performing a size check
    return SUCCESS;
  }

  if (ctx == NULL) {
    return FAILURE;
  }

  EVP_PKEY *pkey = ((EVP_PKEY_CTX *)ctx)->pkey;
  if (pkey != NULL &&
      pkey->type == NID_KYBER512 &&
      pkey->pkey.ptr != NULL) {
    KYBER512_KEY *key = pkey->pkey.ptr;
    if (key->has_private) {
      pqcrystals_kyber512_ref_dec(out, in, key->priv); // always returns 0
      return SUCCESS;
    }
  }
  return FAILURE;
}

const EVP_KEM EVP_KEM_kyber512 = {
    .name_id = NID_KYBER512,
    .type_name = "KYBER512",
    .description = "Kyber512 KEM",
    .encapsulate_init = kyber512_encapsulate_init,
    .encapsulate = kyber512_encapsulate,
    .decapsulate_init = kyber512_decapsulate_init,
    .decapsulate = kyber512_decapsulate,
};
