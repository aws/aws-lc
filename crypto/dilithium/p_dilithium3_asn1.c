// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/evp.h>

#include <openssl/bytestring.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include "../evp_extra/internal.h"
#include "../fipsmodule/evp/internal.h"
#include "../internal.h"
#include "sig_dilithium.h"


static void dilithium3_free(EVP_PKEY *pkey) {
  DILITHIUM3_KEY *key = pkey->pkey.ptr;
  if (key == NULL) {
    return;
  }
  OPENSSL_free(key->pub);
  key->pub = NULL;
  OPENSSL_free(key->priv);
  key->priv = NULL;
  OPENSSL_free(pkey->pkey.ptr);
  pkey->pkey.ptr = NULL;
}

static int dilithium3_set_priv_raw(EVP_PKEY *pkey, const uint8_t *privkey,
        size_t privkey_len, const uint8_t *pubkey, size_t pubkey_len) {
  if (privkey_len != DILITHIUM3_PRIVATE_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  // At time of writing, all |set_priv_raw| and |dilithium3_set_priv_raw|
  // invocations specify NULL public key. If that changes, we should modify
  // the conditional below to set the public key on |key|.
  if (pubkey != NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATION_NOT_SUPPORTED_FOR_THIS_KEYTYPE);
    return 0;
  }

  DILITHIUM3_KEY *key = OPENSSL_malloc(sizeof(DILITHIUM3_KEY));
  if (key == NULL) {
      return 0;
  }
  key->priv = OPENSSL_malloc(DILITHIUM3_PRIVATE_KEY_BYTES);
  if (key->priv == NULL) {
    OPENSSL_free(key);
    return 0;
  }

  key->pub = NULL;
  OPENSSL_memcpy(key->priv, privkey, privkey_len);

  dilithium3_free(pkey);
  pkey->pkey.ptr = key;
  return 1;
}

static int dilithium3_set_pub_raw(EVP_PKEY *pkey, const uint8_t *in, size_t len) {
  if (len != DILITHIUM3_PUBLIC_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_KEYBITS);
    return 0;
  }

  DILITHIUM3_KEY *key = OPENSSL_malloc(sizeof(DILITHIUM3_KEY));
  if (key == NULL) {
    return 0;
  }
  key->pub = OPENSSL_malloc(DILITHIUM3_PUBLIC_KEY_BYTES);
  if (key->pub == NULL) {
    OPENSSL_free(key);
    return 0;
  }

  OPENSSL_memcpy(key->pub, in, len);
  key->priv = NULL;

  dilithium3_free(pkey);
  pkey->pkey.ptr = key;
  return 1;
}

static int dilithium3_get_priv_raw(const EVP_PKEY *pkey, uint8_t *out,
                                   size_t *out_len) {
  const DILITHIUM3_KEY *key = pkey->pkey.ptr;
  if (key->priv == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NOT_A_PRIVATE_KEY);
    return 0;
  }

  if (out == NULL) {
    *out_len = DILITHIUM3_PRIVATE_KEY_BYTES;
    return 1;
  }

  if (*out_len < DILITHIUM3_PRIVATE_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
    return 0;
  }

  OPENSSL_memcpy(out, key->priv, DILITHIUM3_PRIVATE_KEY_BYTES);
  *out_len = DILITHIUM3_PRIVATE_KEY_BYTES;
  return 1;
}

static int dilithium3_get_pub_raw(const EVP_PKEY *pkey, uint8_t *out,
                                  size_t *out_len) {
  const DILITHIUM3_KEY *key = pkey->pkey.ptr;
  if (key->pub == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATION_NOT_SUPPORTED_FOR_THIS_KEYTYPE);
    return 0;
  }

  if (out == NULL) {
    *out_len = DILITHIUM3_PUBLIC_KEY_BYTES;
    return 1;
  }

  if (*out_len < DILITHIUM3_PUBLIC_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
    return 0;
  }

  OPENSSL_memcpy(out, key->pub, DILITHIUM3_PUBLIC_KEY_BYTES);
  *out_len = DILITHIUM3_PUBLIC_KEY_BYTES;
  return 1;
}

static int dilithium3_pub_decode(EVP_PKEY *out, CBS *params, CBS *key) {
  // See https://datatracker.ietf.org/doc/draft-ietf-lamps-dilithium-certificates/ section 4.
  // The parameters must be omitted.
  if (CBS_len(params) != 0) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  return dilithium3_set_pub_raw(out, CBS_data(key), CBS_len(key));
}

static int dilithium3_pub_encode(CBB *out, const EVP_PKEY *pkey) {
  const DILITHIUM3_KEY *key = pkey->pkey.ptr;
  if (key->pub == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATION_NOT_SUPPORTED_FOR_THIS_KEYTYPE);
    return 0;
  }

  // See https://datatracker.ietf.org/doc/draft-ietf-lamps-dilithium-certificates/ section 4.
  // TODO: finalize this definition - OCTETSTRING to BITSTRING conversion.
  CBB spki, algorithm, oid, key_bitstring;
  if (!CBB_add_asn1(out, &spki, CBS_ASN1_SEQUENCE) ||
      !CBB_add_asn1(&spki, &algorithm, CBS_ASN1_SEQUENCE) ||
      !CBB_add_asn1(&algorithm, &oid, CBS_ASN1_OBJECT) ||
      !CBB_add_bytes(&oid, dilithium3_asn1_meth.oid, dilithium3_asn1_meth.oid_len) ||
      !CBB_add_asn1(&spki, &key_bitstring, CBS_ASN1_BITSTRING) ||
      !CBB_add_u8(&key_bitstring, 0 /* padding */) ||
      !CBB_add_bytes(&key_bitstring, key->pub, DILITHIUM3_PUBLIC_KEY_BYTES) ||
      !CBB_flush(out)) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_ENCODE_ERROR);
    return 0;
  }

  return 1;
}

static int dilithium3_pub_cmp(const EVP_PKEY *a, const EVP_PKEY *b) {
  const DILITHIUM3_KEY *a_key = a->pkey.ptr;
  const DILITHIUM3_KEY *b_key = b->pkey.ptr;
  return OPENSSL_memcmp(a_key->pub, b_key->pub, DILITHIUM3_PUBLIC_KEY_BYTES) == 0;
}

static int dilithium3_priv_decode(EVP_PKEY *out, CBS *params, CBS *key, CBS *pubkey) {
  // See https://datatracker.ietf.org/doc/draft-ietf-lamps-dilithium-certificates/ section 6.

  // The parameters must be omitted.
  if (CBS_len(params) != 0 ) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  return dilithium3_set_priv_raw(out, CBS_data(key), CBS_len(key), NULL, 0);
}

static int dilithium3_priv_encode(CBB *out, const EVP_PKEY *pkey) {
  DILITHIUM3_KEY *key = pkey->pkey.ptr;
  if (key->priv == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NOT_A_PRIVATE_KEY);
    return 0;
  }
  // See https://datatracker.ietf.org/doc/draft-ietf-lamps-dilithium-certificates/ section 6.
  CBB pkcs8, algorithm, oid, private_key;
  if (!CBB_add_asn1(out, &pkcs8, CBS_ASN1_SEQUENCE) ||
      !CBB_add_asn1_uint64(&pkcs8, 0 /* version */) ||
      !CBB_add_asn1(&pkcs8, &algorithm, CBS_ASN1_SEQUENCE) ||
      !CBB_add_asn1(&algorithm, &oid, CBS_ASN1_OBJECT) ||
      !CBB_add_bytes(&oid, dilithium3_asn1_meth.oid, dilithium3_asn1_meth.oid_len) ||
      !CBB_add_asn1(&pkcs8, &private_key, CBS_ASN1_OCTETSTRING) ||
      !CBB_add_bytes(&private_key, key->priv, DILITHIUM3_PRIVATE_KEY_BYTES) ||
      !CBB_flush(out)) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_ENCODE_ERROR);
    return 0;
  }

  return 1;
}

static int dilithium3_size(const EVP_PKEY *pkey) {
  return DILITHIUM3_SIGNATURE_BYTES;
}

static int dilithium3_bits(const EVP_PKEY *pkey) {
  return 8 * (DILITHIUM3_PUBLIC_KEY_BYTES);
}

const EVP_PKEY_ASN1_METHOD dilithium3_asn1_meth = {
    EVP_PKEY_DILITHIUM3,
    // 1.3.6.1.4.1.2.267.7.6.5 = Dilithium SIG Round-3. These are temp values from
    // https://github.com/IETF-Hackathon/pqc-certificates/blob/master/docs/oid_mapping.md
    // as we await NIST to release OIDs.
    {0x2B, 0x06, 0x01, 0x04, 0x01, 0x02, 0x82, 0x0B, 0x07, 0x06, 0x05},
    11,
    dilithium3_pub_decode,
    dilithium3_pub_encode,
    dilithium3_pub_cmp,
    dilithium3_priv_decode,
    dilithium3_priv_encode,
    NULL /*priv_encode_v2*/,
    dilithium3_set_priv_raw,
    dilithium3_set_pub_raw,
    dilithium3_get_priv_raw,
    dilithium3_get_pub_raw,
    NULL /* pkey_opaque */,
    dilithium3_size,
    dilithium3_bits,
    NULL /* param_missing */,
    NULL /* param_copy */,
    NULL /* param_cmp */,
    dilithium3_free,
};



