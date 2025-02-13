// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC
#include <openssl/evp.h>
#include <openssl/mem.h>
#include <openssl/base.h>

#include "../delocate.h"
#include "../../evp_extra/internal.h"
#include "../ml_dsa/ml_dsa.h"
#include "internal.h"

// ML-DSA OIDs as defined within:
// https://csrc.nist.gov/projects/computer-security-objects-register/algorithm-registration
//2.16.840.1.101.3.4.3.17
static const uint8_t kOIDMLDSA44[]  = {0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x11};
//2.16.840.1.101.3.4.3.18
static const uint8_t kOIDMLDSA65[]  = {0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x12};
//2.16.840.1.101.3.4.3.19
static const uint8_t kOIDMLDSA87[]  = {0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x13};

// PQDSA functions: these are init/new/clear/free/get_sig functions for PQDSA_KEY
// These are analagous to the ec_key functions in crypto/fipsmodule/ec/ec_key.c

PQDSA_KEY *PQDSA_KEY_new(void) {
  PQDSA_KEY *ret = OPENSSL_zalloc(sizeof(PQDSA_KEY));
  if (ret == NULL) {
    return NULL;
  }

  return ret;
}

static void PQDSA_KEY_clear(PQDSA_KEY *key) {
  key->pqdsa = NULL;
  OPENSSL_free(key->public_key);
  OPENSSL_free(key->private_key);
  key->public_key = NULL;
  key->private_key = NULL;
}

int PQDSA_KEY_init(PQDSA_KEY *key, const PQDSA *pqdsa) {
  if (key == NULL || pqdsa == NULL) {
    return 0;
  }
  // If the key is already initialized clear it.
  PQDSA_KEY_clear(key);

  key->pqdsa = pqdsa;
  key->public_key = OPENSSL_malloc(pqdsa->public_key_len);
  key->private_key = OPENSSL_malloc(pqdsa->private_key_len);
  if (key->public_key == NULL || key->private_key == NULL) {
    PQDSA_KEY_clear(key);
    return 0;
  }
  return 1;
}

void PQDSA_KEY_free(PQDSA_KEY *key) {
  if (key == NULL) {
    return;
  }
  PQDSA_KEY_clear(key);
  OPENSSL_free(key);
}

const PQDSA *PQDSA_KEY_get0_dsa(PQDSA_KEY* key) {
  return key->pqdsa;
}

int PQDSA_KEY_set_raw_public_key(PQDSA_KEY *key, CBS *in) {
  // Check if the parsed length corresponds with the expected length.
  if (CBS_len(in) != key->pqdsa->public_key_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }

  key->public_key = OPENSSL_memdup(CBS_data(in), key->pqdsa->public_key_len);
  if (key->public_key == NULL) {
    return 0;
  }

  return 1;
}

int PQDSA_KEY_set_raw_keypair_from_seed(PQDSA_KEY *key, CBS *in) {
  // Check if the parsed length corresponds with the expected length.
  if (CBS_len(in) != key->pqdsa->keygen_seed_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }

  //allocate buffers to store key pair
  uint8_t *public_key = OPENSSL_malloc(key->pqdsa->public_key_len);
  if (public_key == NULL) {
    return 0;
  }

  uint8_t *private_key = OPENSSL_malloc(key->pqdsa->private_key_len);
  if (private_key == NULL) {
    OPENSSL_free(public_key);
    return 0;
  }

  // attempt to generate the key from the provided seed
  if (!key->pqdsa->method->pqdsa_keygen_internal(public_key,
                                                 private_key,
                                                 CBS_data(in))) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  // set the public and private key
  key->public_key = public_key;
  key->private_key = private_key;

  return 1;
}

int PQDSA_KEY_set_raw_private_key(PQDSA_KEY *key, CBS *in) {
  // Check if the parsed length corresponds with the expected length.
  if (CBS_len(in) != key->pqdsa->private_key_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }

  key->private_key = OPENSSL_memdup(CBS_data(in), key->pqdsa->private_key_len);
  if (key->private_key == NULL) {
    return 0;
  }

  // Create buffers to store public key based on size
  size_t pk_len = key->pqdsa->public_key_len;
  uint8_t *public_key = OPENSSL_malloc(pk_len);

  if (public_key == NULL) {
    return 0;
  }

  // Construct the public key from the private key
  if (!key->pqdsa->method->pqdsa_pack_pk_from_sk(public_key, key->private_key)) {
    OPENSSL_free(public_key);
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  key->public_key = public_key;

  return 1;
}

DEFINE_LOCAL_DATA(PQDSA_METHOD, sig_ml_dsa_44_method) {
  out->pqdsa_keygen = ml_dsa_44_keypair;
  out->pqdsa_keygen_internal = ml_dsa_44_keypair_internal;
  out->pqdsa_sign_message = ml_dsa_44_sign;
  out->pqdsa_sign = ml_dsa_extmu_44_sign;
  out->pqdsa_verify_message = ml_dsa_44_verify;
  out->pqdsa_verify = ml_dsa_extmu_44_verify;
  out->pqdsa_pack_pk_from_sk = ml_dsa_44_pack_pk_from_sk;
}

DEFINE_LOCAL_DATA(PQDSA_METHOD, sig_ml_dsa_65_method) {
  out->pqdsa_keygen = ml_dsa_65_keypair;
  out->pqdsa_keygen_internal = ml_dsa_65_keypair_internal;
  out->pqdsa_sign_message = ml_dsa_65_sign;
  out->pqdsa_sign = ml_dsa_extmu_65_sign;
  out->pqdsa_verify_message = ml_dsa_65_verify;
  out->pqdsa_verify = ml_dsa_extmu_65_verify;
  out->pqdsa_pack_pk_from_sk = ml_dsa_65_pack_pk_from_sk;
}

DEFINE_LOCAL_DATA(PQDSA_METHOD, sig_ml_dsa_87_method) {
  out->pqdsa_keygen = ml_dsa_87_keypair;
  out->pqdsa_keygen_internal = ml_dsa_87_keypair_internal;
  out->pqdsa_sign_message = ml_dsa_87_sign;
  out->pqdsa_sign = ml_dsa_extmu_87_sign;
  out->pqdsa_verify_message = ml_dsa_87_verify;
  out->pqdsa_verify = ml_dsa_extmu_87_verify;
  out->pqdsa_pack_pk_from_sk = ml_dsa_87_pack_pk_from_sk;
}

DEFINE_LOCAL_DATA(PQDSA, sig_ml_dsa_44) {
  out->nid = NID_MLDSA44;
  out->oid = kOIDMLDSA44;
  out->oid_len = sizeof(kOIDMLDSA44);
  out->comment = "MLDSA44";
  out->public_key_len = MLDSA44_PUBLIC_KEY_BYTES;
  out->private_key_len = MLDSA44_PRIVATE_KEY_BYTES;
  out->signature_len = MLDSA44_SIGNATURE_BYTES;
  out->keygen_seed_len = MLDSA44_KEYGEN_SEED_BYTES;
  out->sign_seed_len = MLDSA44_SIGNATURE_SEED_BYTES;
  out->method = sig_ml_dsa_44_method();
}

DEFINE_LOCAL_DATA(PQDSA, sig_ml_dsa_65) {
  out->nid = NID_MLDSA65;
  out->oid = kOIDMLDSA65;
  out->oid_len = sizeof(kOIDMLDSA65);
  out->comment = "MLDSA65";
  out->public_key_len = MLDSA65_PUBLIC_KEY_BYTES;
  out->private_key_len = MLDSA65_PRIVATE_KEY_BYTES;
  out->signature_len = MLDSA65_SIGNATURE_BYTES;
  out->keygen_seed_len = MLDSA65_KEYGEN_SEED_BYTES;
  out->sign_seed_len = MLDSA65_SIGNATURE_SEED_BYTES;
  out->method = sig_ml_dsa_65_method();
}

DEFINE_LOCAL_DATA(PQDSA, sig_ml_dsa_87) {
  out->nid = NID_MLDSA87;
  out->oid = kOIDMLDSA87;
  out->oid_len = sizeof(kOIDMLDSA87);
  out->comment = "MLDSA87";
  out->public_key_len = MLDSA87_PUBLIC_KEY_BYTES;
  out->private_key_len = MLDSA87_PRIVATE_KEY_BYTES;
  out->signature_len = MLDSA87_SIGNATURE_BYTES;
  out->keygen_seed_len = MLDSA87_KEYGEN_SEED_BYTES;
  out->sign_seed_len = MLDSA87_SIGNATURE_SEED_BYTES;
  out->method = sig_ml_dsa_87_method();
}

const PQDSA *PQDSA_find_dsa_by_nid(int nid) {
  switch (nid) {
    case NID_MLDSA44:
      return sig_ml_dsa_44();
    case NID_MLDSA65:
      return sig_ml_dsa_65();
    case NID_MLDSA87:
      return sig_ml_dsa_87();
    default:
      return NULL;
  }
}

const EVP_PKEY_ASN1_METHOD *PQDSA_find_asn1_by_nid(int nid) {
  switch (nid) {
    case NID_MLDSA44:
    case NID_MLDSA65:
    case NID_MLDSA87:
      return &pqdsa_asn1_meth;
    default:
      return NULL;
  }
}
