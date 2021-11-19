#include <openssl/evp.h>

#include <openssl/bytestring.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include "../fipsmodule/evp/internal.h"
#include "../internal.h"
#include "../evp_extra/internal.h"


static void kyber512_free(EVP_PKEY *pkey) {
  OPENSSL_free(pkey->pkey.ptr);
  pkey->pkey.ptr = NULL;
}

static int kyber512_set_priv_raw(EVP_PKEY *pkey, const uint8_t *in, size_t len) {
  if (len != KYBER512_SECRETKEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_KEYBITS);
    return 0;
  }

  KYBER_512_KEY *key = OPENSSL_malloc(sizeof(KYBER_512_KEY));
  if (key == NULL) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  OPENSSL_memcpy(key->priv, in, len);
  key->has_private = 1;

  kyber512_free(pkey);
  pkey->pkey.ptr = key;
  return 1;
}

static int kyber512_set_pub_raw(EVP_PKEY *pkey, const uint8_t *in, size_t len) {
  if (len != KYBER512_PUBLICKEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_KEYBITS);
    return 0;
  }

  KYBER_512_KEY *key = OPENSSL_malloc(sizeof(KYBER_512_KEY));
  if (key == NULL) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  OPENSSL_memcpy(key->pub, in, len);
  key->has_private = 0;

  kyber512_free(pkey);
  pkey->pkey.ptr = key;
  return 1;
}

static int kyber512_get_priv_raw(const EVP_PKEY *pkey, uint8_t *out,
                                size_t *out_len) {
  const KYBER_512_KEY *key = pkey->pkey.ptr;
  if (!key->has_private) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NOT_A_PRIVATE_KEY);
    return 0;
  }

  if (out == NULL) {
    *out_len = KYBER512_SECRETKEY_BYTES;
    return 1;
  }

  if (*out_len < KYBER512_SECRETKEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
    return 0;
  }

  OPENSSL_memcpy(out, key->priv, KYBER512_SECRETKEY_BYTES);
  *out_len = KYBER512_SECRETKEY_BYTES;
  return 1;
}

static int kyber512_get_pub_raw(const EVP_PKEY *pkey, uint8_t *out,
                               size_t *out_len) {
  const KYBER_512_KEY *key = pkey->pkey.ptr;
  if (out == NULL) {
    *out_len = KYBER512_PUBLICKEY_BYTES;
    return 1;
  }

  if (*out_len < KYBER512_PUBLICKEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
    return 0;
  }

  OPENSSL_memcpy(out, key->pub, KYBER512_PUBLICKEY_BYTES);
  *out_len = KYBER512_PUBLICKEY_BYTES;
  return 1;
}

static int kyber512_pub_cmp(const EVP_PKEY *a, const EVP_PKEY *b) {
  const KYBER_512_KEY *a_key = a->pkey.ptr;
  const KYBER_512_KEY *b_key = b->pkey.ptr;
  return OPENSSL_memcmp(a_key->pub, b_key->pub, KYBER512_PUBLICKEY_BYTES) == 0;
}

static int kyber512_size(const EVP_PKEY *pkey) {
  return KYBER512_PUBLICKEY_BYTES + KYBER512_SECRETKEY_BYTES;
}

static int kyber512_bits(const EVP_PKEY *pkey) {
  return 8 * (KYBER512_PUBLICKEY_BYTES + KYBER512_SECRETKEY_BYTES);
}

const EVP_PKEY_ASN1_METHOD kyber512_asn1_meth = {
    EVP_PKEY_KYBER512,
    {},
    0,
    NULL,
    NULL,
    kyber512_pub_cmp,
    NULL,
    NULL,
    kyber512_set_priv_raw,
    kyber512_set_pub_raw,
    kyber512_get_priv_raw,
    kyber512_get_pub_raw,
    NULL /* pkey_opaque */,
    kyber512_size,
    kyber512_bits,
    NULL /* param_missing */,
    NULL /* param_copy */,
    NULL /* param_cmp */,
    kyber512_free,
};
