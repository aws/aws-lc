// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/mem.h>

#include <openssl/bytestring.h>
#include "../fipsmodule/evp/internal.h"
#include "../fipsmodule/kem/internal.h"
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


static int kem_pub_decode(EVP_PKEY *out, CBS *oid, CBS *params, CBS *key) {
  // See https://datatracker.ietf.org/doc/draft-ietf-lamps-kyber-certificates/
  // section 4. There should be no parameters
  if (CBS_len(params) > 0) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }
  // Set the kem params on |out|.
  if (!EVP_PKEY_kem_set_params(out, OBJ_cbs2nid(oid))) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }
  
  if (CBS_len(key) != out->pkey.kem_key->kem->public_key_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }
  
  return KEM_KEY_set_raw_public_key(out->pkey.kem_key, CBS_data(key));
}

static int kem_pub_encode(CBB *out, const EVP_PKEY *pkey) {
  KEM_KEY *key = pkey->pkey.kem_key;
  const KEM *kem = key->kem;
  if (key->public_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATION_NOT_SUPPORTED_FOR_THIS_KEYTYPE);
    return 0;
  }

  // See https://datatracker.ietf.org/doc/draft-ietf-lamps-kyber-certificates/
  // section 4.
  CBB spki, algorithm, oid, key_bitstring;
  if (!CBB_add_asn1(out, &spki, CBS_ASN1_SEQUENCE) || // SubjectPublicKeyInfo SEQUENCE
      !CBB_add_asn1(&spki, &algorithm, CBS_ASN1_SEQUENCE) || // algorithm: AlgorithmIdentifier SEQUENCE
      !CBB_add_asn1(&algorithm, &oid, CBS_ASN1_OBJECT) || // OBJECT IDENTIFIER
      !CBB_add_bytes(&oid, kem->oid, kem->oid_len) || // OID bytes for id-alg-ml-kem-512/768/1024, params must be absent per standard
      !CBB_add_asn1(&spki, &key_bitstring, CBS_ASN1_BITSTRING) || // subjectPublicKey: BIT STRING
      !CBB_add_u8(&key_bitstring, 0 /* padding */) || // 0 unused bits (ML-KEM public keys are complete octets) 
      !CBB_add_bytes(&key_bitstring, key->public_key, kem->public_key_len) || // Raw ML-KEM public key
      !CBB_flush(out)) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_ENCODE_ERROR);
    return 0;
  }

  return 1;
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

static int kem_priv_decode(EVP_PKEY *out, CBS *oid, CBS *params, CBS *key,
                           CBS *pubkey) {
  // See https://datatracker.ietf.org/doc/draft-ietf-lamps-kyber-certificates/
  // section 6. There should be no parameters.
  if (CBS_len(params) > 0) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  // Set the kem params on |out|.
  if (!EVP_PKEY_kem_set_params(out, OBJ_cbs2nid(oid))) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  // At the moment, we only support expandedKey format from
  // https://datatracker.ietf.org/doc/draft-ietf-lamps-kyber-certificates.
  // TODO(awslc): add support for "seed" and "both" formats.
  if (!CBS_peek_asn1_tag(key, CBS_ASN1_OCTETSTRING)) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  CBS expanded_key;
  if (!CBS_get_asn1(key, &expanded_key, CBS_ASN1_OCTETSTRING)) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  if (CBS_len(&expanded_key) != out->pkey.kem_key->kem->secret_key_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }

  return KEM_KEY_set_raw_secret_key(out->pkey.kem_key, CBS_data(&expanded_key));
}

static int kem_priv_encode(CBB *out, const EVP_PKEY *pkey) {
  KEM_KEY *key = pkey->pkey.kem_key;
  const KEM *kem = key->kem;
  if (key->secret_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NOT_A_PRIVATE_KEY);
    return 0;
  }
  // See https://datatracker.ietf.org/doc/draft-ietf-lamps-kyber-certificates/
  // section 6.
  CBB pkcs8, algorithm, oid, private_key, expanded_key;
  if (!CBB_add_asn1(out, &pkcs8, CBS_ASN1_SEQUENCE) || // OneAsymmetricKey SEQUENCE
      !CBB_add_asn1_uint64(&pkcs8, PKCS8_VERSION_ONE /* version */) ||
      !CBB_add_asn1(&pkcs8, &algorithm, CBS_ASN1_SEQUENCE) || // privateKeyAlgorithm: SEQUENCE
      !CBB_add_asn1(&algorithm, &oid, CBS_ASN1_OBJECT) || // algorithm: OBJECT IDENTIFIER
      !CBB_add_bytes(&oid, kem->oid, kem->oid_len) || // OID bytes for id-alg-ml-kem-512/768/1024
      !CBB_add_asn1(&pkcs8, &private_key, CBS_ASN1_OCTETSTRING) || // // privateKey: OCTET STRING (outer container)
      !CBB_add_asn1(&private_key, &expanded_key, CBS_ASN1_OCTETSTRING) || // expandedKey CHOICE variant, AWS-LC uses expandedKey for the moment
      !CBB_add_bytes(&expanded_key, key->secret_key, kem->secret_key_len) || // raw private key 
      !CBB_flush(out)) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_ENCODE_ERROR);
    return 0;
  }

  return 1;
}

const EVP_PKEY_ASN1_METHOD kem_asn1_meth = {
    // 2.16.840.1.101.3.4.4
    EVP_PKEY_KEM,

    {0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04},
    8,

    "KEM",
    "AWS-LC KEM method",

    kem_pub_decode,
    kem_pub_encode,
    kem_pub_cmp,
    kem_priv_decode,
    kem_priv_encode,
    NULL, // priv_encode_v2 
    NULL, // kem_set_priv_raw
    NULL, // kem_set_pub_raw
    kem_get_priv_raw,
    kem_get_pub_raw,
    NULL, // pkey_opaque
    NULL, // kem_size
    NULL, // kem_bits 
    NULL, // param_missing 
    NULL, // param_copy 
    kem_cmp_parameters,
    kem_free,
};
