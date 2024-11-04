// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/evp.h>

#include <openssl/bytestring.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include "../evp_extra/internal.h"
#include "../fipsmodule/evp/internal.h"
#include "../internal.h"
#include "sig_dilithium.h"
#include "internal.h"


static void nistdsa_free(EVP_PKEY *pkey) {
  NISTDSA_KEY_free(pkey->pkey.nistdsa_key);
  pkey->pkey.nistdsa_key = NULL;
}


static int nistdsa_set_priv_raw(EVP_PKEY *pkey, const uint8_t *privkey,
        size_t privkey_len, const uint8_t *pubkey, size_t pubkey_len) {

  NISTDSA_KEY *key = OPENSSL_malloc(sizeof(NISTDSA_KEY));
  if (key == NULL) {
    return 0;
  }

  // At time of writing, all |set_priv_raw| and |nistdsa_set_priv_raw|
  // invocations specify NULL public key. If that changes, we should modify
  // the conditional below to set the public key on |key|.
  if (pubkey != NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATION_NOT_SUPPORTED_FOR_THIS_KEYTYPE);
    return 0;
  }

  // NOTE: No checks are done in this function, the caller has to ensure
  //       that the pointers are valid and |in| has the correct size.
  key->public_key = NULL;
  key->secret_key = OPENSSL_memdup(privkey, privkey_len);
  nistdsa_free(pkey);
  pkey->pkey.nistdsa_key = key;
  return 1;
}

static int nistdsa_set_pub_raw(EVP_PKEY *pkey, const uint8_t *in, size_t len) {
  //generate a fresh nistdsa_key
  NISTDSA_KEY *key = OPENSSL_malloc(sizeof(NISTDSA_KEY));

  if (key == NULL) {
    return 0;
  }

  // NOTE: No checks are done in this function, the caller has to ensure
  //       that the pointers are valid and |in| has the correct size.
  key->public_key = OPENSSL_memdup(in, len);
  key->secret_key = NULL;

  nistdsa_free(pkey);
  pkey->pkey.nistdsa_key = key;
  return 1;
}

static int nistdsa_get_priv_raw(const EVP_PKEY *pkey, uint8_t *out,
                                   size_t *out_len) {
  if (pkey->pkey.nistdsa_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
    return 0;
  }

  NISTDSA_KEY *key = pkey->pkey.nistdsa_key;
  const NISTDSA *nistdsa = key->nistdsa;

  if (key->secret_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NOT_A_PRIVATE_KEY);
    return 0;
  }

  if (nistdsa == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
    return 0;
  }

  if (out == NULL) {
    *out_len = key->nistdsa->secret_key_len;
    return 1;
  }

  if (*out_len < key->nistdsa->secret_key_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
    return 0;
  }

  OPENSSL_memcpy(out, key->secret_key, nistdsa->secret_key_len);
  *out_len = nistdsa->secret_key_len;
  return 1;
}

static int nistdsa_get_pub_raw(const EVP_PKEY *pkey, uint8_t *out,
                                  size_t *out_len) {
  if (pkey->pkey.nistdsa_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
    return 0;
  }

  NISTDSA_KEY *key = pkey->pkey.nistdsa_key;
  const NISTDSA *nistdsa = key->nistdsa;

  if (nistdsa == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
    return 0;
  }

  if (key->public_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATION_NOT_SUPPORTED_FOR_THIS_KEYTYPE);
    return 0;
  }

  if (out == NULL) {
    *out_len = nistdsa->public_key_len;
    return 1;
  }

  if (*out_len < key->nistdsa->public_key_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_BUFFER_TOO_SMALL);
    return 0;
  }

  OPENSSL_memcpy(out, key->public_key, nistdsa->public_key_len);
  *out_len = nistdsa->public_key_len;
  return 1;
}

static int nistdsa_pub_decode(EVP_PKEY *out, CBS *params, CBS *key) {
  // See https://datatracker.ietf.org/doc/draft-ietf-lamps-dilithium-certificates/ section 4.
  // The parameters must be omitted.
  if (CBS_len(params) != 0) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }
  return nistdsa_set_pub_raw(out, CBS_data(key), CBS_len(key));
}

static int nistdsa_pub_encode(CBB *out, const EVP_PKEY *pkey) {
  NISTDSA_KEY *key = pkey->pkey.nistdsa_key;
  const NISTDSA *nistdsa = key->nistdsa;
  if (key->public_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_OPERATION_NOT_SUPPORTED_FOR_THIS_KEYTYPE);
    return 0;
  }

  // See https://datatracker.ietf.org/doc/draft-ietf-lamps-dilithium-certificates/ section 4.
  // TODO: finalize this definition - OCTETSTRING to BITSTRING conversion.
  CBB spki, algorithm, oid, key_bitstring;
  if (!CBB_add_asn1(out, &spki, CBS_ASN1_SEQUENCE) ||
      !CBB_add_asn1(&spki, &algorithm, CBS_ASN1_SEQUENCE) ||
      !CBB_add_asn1(&algorithm, &oid, CBS_ASN1_OBJECT) ||
      !CBB_add_bytes(&oid, pkey->ameth->oid, pkey->ameth->oid_len) ||
      !CBB_add_asn1(&spki, &key_bitstring, CBS_ASN1_BITSTRING) ||
      !CBB_add_u8(&key_bitstring, 0 /* padding */) ||
      !CBB_add_bytes(&key_bitstring, key->public_key, nistdsa->public_key_len) ||
      !CBB_flush(out)) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_ENCODE_ERROR);
    return 0;
      }

  return 1;
}

static int nistdsa_pub_cmp(const EVP_PKEY *a, const EVP_PKEY *b) {
  NISTDSA_KEY *a_key = a->pkey.nistdsa_key;
  NISTDSA_KEY *b_key = b->pkey.nistdsa_key;

  return OPENSSL_memcmp(a_key->public_key,
                        b_key->public_key,
                        a->pkey.nistdsa_key->nistdsa->public_key_len) == 0;
}

static int nistdsa_priv_decode(EVP_PKEY *out, CBS *params, CBS *key, CBS *pubkey) {
  // See https://datatracker.ietf.org/doc/draft-ietf-lamps-dilithium-certificates/ section 6.
  // The parameters must be omitted.
  if (CBS_len(params) != 0 ) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  return nistdsa_set_priv_raw(out, CBS_data(key), CBS_len(key), NULL, 0);
}

static int nistdsa_priv_encode(CBB *out, const EVP_PKEY *pkey) {
  NISTDSA_KEY *key = pkey->pkey.nistdsa_key;
  const NISTDSA *nistdsa = key->nistdsa;
  if (key->secret_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NOT_A_PRIVATE_KEY);
    return 0;
  }
  // See https://datatracker.ietf.org/doc/draft-ietf-lamps-dilithium-certificates/ section 6.
  CBB pkcs8, algorithm, oid, private_key;
  if (!CBB_add_asn1(out, &pkcs8, CBS_ASN1_SEQUENCE) ||
      !CBB_add_asn1_uint64(&pkcs8, 0 /* version */) ||
      !CBB_add_asn1(&pkcs8, &algorithm, CBS_ASN1_SEQUENCE) ||
      !CBB_add_asn1(&algorithm, &oid, CBS_ASN1_OBJECT) ||
      !CBB_add_bytes(&oid, pkey->ameth->oid, pkey->ameth->oid_len) ||
      !CBB_add_asn1(&pkcs8, &private_key, CBS_ASN1_OCTETSTRING) ||
      !CBB_add_bytes(&private_key, key->secret_key, nistdsa->secret_key_len) ||
      !CBB_flush(out)) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_ENCODE_ERROR);
    return 0;
      }

  return 1;
}

static int nistdsa_size(const EVP_PKEY *pkey) {
  if (pkey->pkey.nistdsa_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
    return 0;
  }
  return pkey->pkey.nistdsa_key->nistdsa->signature_len;
}

static int nistdsa_bits(const EVP_PKEY *pkey) {
  if (pkey->pkey.nistdsa_key == NULL) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_NO_PARAMETERS_SET);
    return 0;
  }
  return 8 * (pkey->pkey.nistdsa_key->nistdsa->public_key_len);
}

const EVP_PKEY_ASN1_METHOD nistdsa_asn1_meth = {
  //2.16.840.1.101.3.4.3
  EVP_PKEY_NISTDSA,

  {0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03},
  8,

  "NIST DSA",
  "AWS-LC NIST DSA method",

  nistdsa_pub_decode,
  nistdsa_pub_encode,
  nistdsa_pub_cmp,
  nistdsa_priv_decode,
  nistdsa_priv_encode,
  NULL /*priv_encode_v2*/,
  nistdsa_set_priv_raw,
  nistdsa_set_pub_raw,
  nistdsa_get_priv_raw,
  nistdsa_get_pub_raw,
  NULL /* pkey_opaque */,
  nistdsa_size,
  nistdsa_bits,
  NULL /* param_missing */,
  NULL /* param_copy */,
  NULL /* param_cmp */,
  nistdsa_free,
};
