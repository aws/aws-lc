#include <openssl/evp.h>

#include <openssl/bytestring.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include "../evp_extra/internal.h"
#include "../fipsmodule/evp/internal.h"
#include "../internal.h"
#include "kem_kyber.h"


static void kyber768_free(EVP_PKEY *pkey) {
  OPENSSL_free(pkey->pkey.ptr);
  pkey->pkey.ptr = NULL;
}

static int kyber768_set_priv_raw(EVP_PKEY *pkey, const uint8_t *in, size_t len) {
  if (len != KYBER768_SECRET_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_KEYBITS);
    return 0;
  }

  KYBER768_KEY *key = OPENSSL_malloc(sizeof(KYBER768_KEY));
  if (key == NULL) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  OPENSSL_STATIC_ASSERT(sizeof(key->priv) >= KYBER768_SECRET_KEY_BYTES,
                        not_enough_space_for_kyber768_secret_key);

  OPENSSL_memcpy(key->priv, in, len);
  key->has_private = 1;

  kyber768_free(pkey);
  pkey->pkey.ptr = key;
  return 1;
}

static int kyber768_set_pub_raw(EVP_PKEY *pkey, const uint8_t *in, size_t len) {
  if (len != KYBER768_PUBLIC_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_KEYBITS);
    return 0;
  }

  KYBER768_KEY *key = OPENSSL_malloc(sizeof(KYBER768_KEY));
  if (key == NULL) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  OPENSSL_STATIC_ASSERT(sizeof(key->pub) >= KYBER768_PUBLIC_KEY_BYTES,
                        not_enough_space_for_kyber768_public_key);

  OPENSSL_memcpy(key->pub, in, len);
  key->has_private = 0;

  kyber768_free(pkey);
  pkey->pkey.ptr = key;
  return 1;
}

static int kyber768_get_priv_raw(const EVP_PKEY *pkey, uint8_t *out,
                                size_t *out_len) {
  const KYBER768_KEY *key = pkey->pkey.ptr;
  if (!key->has_private) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NOT_A_PRIVATE_KEY);
    return 0;
  }

  if (out == NULL) {
    *out_len = KYBER768_SECRET_KEY_BYTES;
    return 1;
  }

  if (*out_len < KYBER768_SECRET_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
    return 0;
  }

  OPENSSL_memcpy(out, key->priv, KYBER768_SECRET_KEY_BYTES);
  *out_len = KYBER768_SECRET_KEY_BYTES;
  return 1;
}

static int kyber768_get_pub_raw(const EVP_PKEY *pkey, uint8_t *out,
                               size_t *out_len) {
  const KYBER768_KEY *key = pkey->pkey.ptr;
  if (out == NULL) {
    *out_len = KYBER768_PUBLIC_KEY_BYTES;
    return 1;
  }

  if (*out_len < KYBER768_PUBLIC_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
    return 0;
  }

  OPENSSL_memcpy(out, key->pub, KYBER768_PUBLIC_KEY_BYTES);
  *out_len = KYBER768_PUBLIC_KEY_BYTES;
  return 1;
}

static int kyber768_pub_cmp(const EVP_PKEY *a, const EVP_PKEY *b) {
  const KYBER768_KEY *a_key = a->pkey.ptr;
  const KYBER768_KEY *b_key = b->pkey.ptr;
  return OPENSSL_memcmp(a_key->pub, b_key->pub, KYBER768_PUBLIC_KEY_BYTES) == 0;
}

static int kyber768_size(const EVP_PKEY *pkey) {
  return KYBER768_PUBLIC_KEY_BYTES + KYBER768_SECRET_KEY_BYTES;
}

static int kyber768_bits(const EVP_PKEY *pkey) {
  return 8 * kyber768_size(pkey);
}

const EVP_PKEY_ASN1_METHOD kyber768_asn1_meth = {
    EVP_PKEY_KYBER768,
    // 1.3.6.1.4.1.2.267.8 = Kyber KEM Round-3
    // TODO(awslc): this is a placeholder OID until we get the official one.
    {0x06, 0x09, 0x2B, 0x06, 0x01, 0x04, 0x01, 0x02, 0x82, 0x0B, 0x08},
    11,
    NULL,
    NULL,
    kyber768_pub_cmp,
    NULL,
    NULL,
    kyber768_set_priv_raw,
    kyber768_set_pub_raw,
    kyber768_get_priv_raw,
    kyber768_get_pub_raw,
    NULL /* pkey_opaque */,
    kyber768_size,
    kyber768_bits,
    NULL /* param_missing */,
    NULL /* param_copy */,
    NULL /* param_cmp */,
    kyber768_free,
};
