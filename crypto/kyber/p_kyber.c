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
  // Caller is getting parameter values.
  if (ciphertext == NULL) {
    *ciphertext_len = KYBER512_CIPHERTEXT_BYTES;
    *shared_secret_len = KYBER512_SHARED_SECRET_BYTES;
    return 1;
  }

  // The output buffers need to be large enough.
  if (*ciphertext_len < KYBER512_CIPHERTEXT_BYTES ||
      *shared_secret_len < KYBER512_SHARED_SECRET_BYTES) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
      return 0;
  }

  // Check that the context is properly configured.
  if (ctx == NULL ||
      ctx->pkey == NULL ||
      ctx->pkey->pkey.ptr == NULL ||
      ctx->pkey->type != EVP_PKEY_KYBER512) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATON_NOT_INITIALIZED);
      return 0;
  }

  KYBER512_KEY *key = (KYBER512_KEY*)ctx->pkey->pkey.ptr;
  kyber512_encapsulate(ciphertext, shared_secret, key->pub);

  // The size of the ciphertext and the shared secret
  // that has been writen to the output buffers.
  *ciphertext_len = KYBER512_CIPHERTEXT_BYTES;
  *shared_secret_len = KYBER512_SHARED_SECRET_BYTES;

  return 1;
}

static int pkey_kyber512_decapsulate(EVP_PKEY_CTX *ctx,
                                     uint8_t *shared_secret,
                                     size_t  *shared_secret_len,
                                     const uint8_t *ciphertext,
                                     size_t   ciphertext_len) {
  // Caller is getting parameter values.
  if (shared_secret == NULL) {
    *shared_secret_len = KYBER512_SHARED_SECRET_BYTES;
    return 1;
  }

  // The input and output buffers need to be large enough.
  if (*shared_secret_len < KYBER512_SHARED_SECRET_BYTES ||
      ciphertext_len < KYBER512_CIPHERTEXT_BYTES) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
      return 0;
  }

  // Check that the context is properly configured.
  if (ctx == NULL ||
      ctx->pkey == NULL ||
      ctx->pkey->pkey.ptr == NULL ||
      ctx->pkey->type != EVP_PKEY_KYBER512) {
      OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATON_NOT_INITIALIZED);
      return 0;
  }

  KYBER512_KEY *key = (KYBER512_KEY*)ctx->pkey->pkey.ptr;
  if (!key->has_private) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NO_KEY_SET);
    return 0;
  }

  kyber512_decapsulate(shared_secret, ciphertext, key->priv);

  // The size of the shared secret that has been writen to the output buffer.
  *shared_secret_len = KYBER512_SHARED_SECRET_BYTES;

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
