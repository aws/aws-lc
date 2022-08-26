#include <openssl/evp.h>

#include <openssl/err.h>
#include <openssl/mem.h>

#include "../fipsmodule/evp/internal.h"
#include "../evp_extra/internal.h"
#include "kem_kyber.h"

static int pkey_kyber512_keygen(EVP_PKEY_CTX *ctx, EVP_PKEY *pkey) {
  KYBER512_KEY *key = OPENSSL_malloc(sizeof(KYBER512_KEY));
  if (key == NULL) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  if (!EVP_PKEY_set_type(pkey, EVP_PKEY_KYBER512)) {
    OPENSSL_free(key);
    return 0;
  }

  kyber512_keypair(key->pub, key->priv);
  key->has_private = 1;

  OPENSSL_free(pkey->pkey.ptr);
  pkey->pkey.ptr = key;
  ctx->pkey = pkey;

  return 1;
}

static int pkey_kyber512_encapsulate(EVP_PKEY_CTX *ctx,
                                     uint8_t *ciphertext,
                                     size_t  *ciphertext_len,
                                     uint8_t *shared_secret,
                                     size_t  *shared_secret_len) {
  *ciphertext_len    = KYBER512_CIPHERTEXT_BYTES;
  *shared_secret_len = KYBER512_SHARED_SECRET_BYTES;
  if (ciphertext == NULL) { // Caller is getting parameter values.
    return 1;
  }

  if (ctx == NULL ||
      ctx->pkey == NULL ||
      ctx->pkey->pkey.ptr == NULL ||
      ctx->pkey->type != EVP_PKEY_KYBER512) {
      return 0;
  }

  KYBER512_KEY *key = ctx->pkey->pkey.ptr;
  kyber512_encapsulate(ciphertext, shared_secret, key->pub);

  return 1;
}

static int pkey_kyber512_decapsulate(EVP_PKEY_CTX *ctx,
                                     uint8_t *shared_secret,
                                     size_t  *shared_secret_len,
                                     uint8_t *ciphertext,
                                     size_t   ciphertext_len) {
  *shared_secret_len = KYBER512_SHARED_SECRET_BYTES;
  if (shared_secret == NULL) { // Caller is getting parameter values.
    return 1;
  }

  if (ctx == NULL ||
      ctx->pkey == NULL ||
      ctx->pkey->pkey.ptr == NULL ||
      ctx->pkey->type != EVP_PKEY_KYBER512) {
      return 0;
  }

  KYBER512_KEY *key = ctx->pkey->pkey.ptr;
  if (!key->has_private) {
    return 0;
  }

  kyber512_decapsulate(shared_secret, ciphertext, key->priv);
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
    pkey_kyber512_encapsulate,
    pkey_kyber512_decapsulate,
};
