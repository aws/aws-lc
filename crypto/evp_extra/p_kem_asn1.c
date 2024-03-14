// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/mem.h>

#include "../fipsmodule/evp/internal.h"
#include "../kem/internal.h"
#include "../internal.h"
#include "internal.h"

static void kem_free(EVP_PKEY *pkey) {
  KEM_KEY_free(pkey->pkey.kem_key);
  pkey->pkey.kem_key = NULL;
}

static int kem_get_priv_raw(const EVP_PKEY *pkey, uint8_t *out,
                            size_t *out_len) {
  if (pkey->pkey.kem_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
    return 0;
  }

  KEM_KEY *key = pkey->pkey.kem_key;
  const KEM *kem = key->kem;
  if (kem == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
    return 0;
  }

  if (out == NULL) {
    *out_len = kem->secret_key_len;
    return 1;
  }

  if (*out_len < kem->secret_key_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
    return 0;
  }

  if (key->secret_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NO_KEY_SET);
    return 0;
  }

  OPENSSL_memcpy(out, key->secret_key, kem->secret_key_len);
  *out_len = kem->secret_key_len;

  return 1;
}

static int kem_get_pub_raw(const EVP_PKEY *pkey, uint8_t *out,
                           size_t *out_len) {
  if (pkey->pkey.kem_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
    return 0;
  }

  KEM_KEY *key = pkey->pkey.kem_key;
  const KEM *kem = key->kem;
  if (kem == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
    return 0;
  }

  if (out == NULL) {
    *out_len = kem->public_key_len;
    return 1;
  }

  if (*out_len < kem->public_key_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
    return 0;
  }

  if (key->public_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NO_KEY_SET);
    return 0;
  }

  OPENSSL_memcpy(out, key->public_key, kem->public_key_len);
  *out_len = kem->public_key_len;

  return 1;
}

static int kem_cmp_parameters(const EVP_PKEY *a, const EVP_PKEY *b) {
  const KEM_KEY *a_key = a->pkey.kem_key;
  const KEM_KEY *b_key = b->pkey.kem_key;
  if (a_key == NULL || b_key == NULL) {
    return -2;
  }

  const KEM *a_kem = a_key->kem;
  const KEM *b_kem = b_key->kem;
  if (a_kem == NULL || b_kem == NULL) {
    return -2;
  }

  return a_kem->nid == b_kem->nid;
}

static int kem_pub_cmp(const EVP_PKEY *a, const EVP_PKEY *b) {
  int ret;
  ret = kem_cmp_parameters(a, b);
  if (ret <= 0) {
    return ret;
  }

  const KEM_KEY *a_key = a->pkey.kem_key;
  const KEM_KEY *b_key = b->pkey.kem_key;
  return OPENSSL_memcmp(a_key->public_key, b_key->public_key,
                        a_key->kem->public_key_len) == 0;
}

const EVP_PKEY_ASN1_METHOD kem_asn1_meth = {
  EVP_PKEY_KEM,
  // TODO(awslc): this is a placeholder OID. Do we need OID for KEM at all?
  {0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff},
  11,
  NULL, // pub_decode
  NULL, // pub_encode
  kem_pub_cmp,
  NULL, // priv_decode
  NULL, // priv_encode
  NULL, // priv_encode_v2
  NULL, // set_priv_raw
  NULL, // set_pub_raw,
  kem_get_priv_raw,
  kem_get_pub_raw,
  NULL, // pkey_opaque
  NULL, // kem_size
  NULL, // kem_bits
  NULL, // missing_parameters
  NULL, // param_copy
  kem_cmp_parameters,
  kem_free,
};
