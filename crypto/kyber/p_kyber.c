#include <openssl/evp.h>

#include <openssl/err.h>
#include <openssl/mem.h>

#include "../fipsmodule/evp/internal.h"
#include "../evp_extra/internal.h"
#include "kem_kyber.h"

static int pkey_kyber512_keygen(EVP_PKEY_CTX *ctx, EVP_PKEY *pkey) {
  KYBER_512_KEY *key = OPENSSL_malloc(sizeof(KYBER_512_KEY));
  if (key == NULL) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  if (!EVP_PKEY_set_type(pkey, EVP_PKEY_KYBER512)) {
    OPENSSL_free(key);
    return 0;
  }

  kyber_512_keypair(key->pub, key->priv);
  key->has_private = 1;

  OPENSSL_free(pkey->pkey.ptr);
  pkey->pkey.ptr = key;
  return 1;
}

const EVP_PKEY_METHOD kyber512_pkey_meth = {
    EVP_PKEY_KYBER512,
    NULL /* init */,
    NULL /* copy */,
    NULL /* cleanup */,
    pkey_kyber512_keygen,
    NULL /* sign_init */,
    NULL /* sign */,
    NULL /* sign_message */,
    NULL /* verify_init */,
    NULL /* verify */,
    NULL /* verify_message */,
    NULL /* verify_recover */,
    NULL /* encrypt */,
    NULL /* decrypt */,
    NULL /* derive */,
    NULL /* paramgen */,
    NULL /* ctrl */,
};
