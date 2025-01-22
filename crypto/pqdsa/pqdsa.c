// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC
#include <openssl/evp.h>
#include <openssl/mem.h>

#include <openssl/base.h>
#include "../evp_extra/internal.h"
#include "../crypto/ml_dsa/ml_dsa.h"
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

int PQDSA_KEY_set_raw_public_key(PQDSA_KEY *key, const uint8_t *in) {
  key->public_key = OPENSSL_memdup(in, key->pqdsa->public_key_len);
  if (key->public_key == NULL) {
    return 0;
  }

  return 1;
}

int PQDSA_KEY_set_raw_private_key(PQDSA_KEY *key, const uint8_t *in) {
  key->private_key = OPENSSL_memdup(in, key->pqdsa->private_key_len);
  if (key->private_key == NULL) {
    return 0;
  }

  return 1;
}

static const PQDSA_METHOD sig_ml_dsa_44_method = {
  ml_dsa_44_keypair,
  ml_dsa_44_sign,
  ml_dsa_extmu_44_sign,
  ml_dsa_44_verify,
  ml_dsa_extmu_44_verify
};

static const PQDSA_METHOD sig_ml_dsa_65_method = {
  ml_dsa_65_keypair,
  ml_dsa_65_sign,
  ml_dsa_extmu_65_sign,
  ml_dsa_65_verify,
  ml_dsa_extmu_65_verify
};

static const PQDSA_METHOD sig_ml_dsa_87_method = {
  ml_dsa_87_keypair,
  ml_dsa_87_sign,
  ml_dsa_extmu_87_sign,
  ml_dsa_87_verify,
  ml_dsa_extmu_87_verify
};

static const PQDSA sig_ml_dsa_44 = {
  NID_MLDSA44,
  kOIDMLDSA44,
  sizeof(kOIDMLDSA44),
  "MLDSA44",
  MLDSA44_PUBLIC_KEY_BYTES,
  MLDSA44_PRIVATE_KEY_BYTES,
  MLDSA44_SIGNATURE_BYTES,
  MLDSA44_KEYGEN_SEED_BYTES,
  MLDSA44_SIGNATURE_SEED_BYTES,
  &sig_ml_dsa_44_method,
};

static const PQDSA sig_ml_dsa_65 = {
  NID_MLDSA65,
  kOIDMLDSA65,
  sizeof(kOIDMLDSA65),
  "MLDSA65",
  MLDSA65_PUBLIC_KEY_BYTES,
  MLDSA65_PRIVATE_KEY_BYTES,
  MLDSA65_SIGNATURE_BYTES,
  MLDSA65_KEYGEN_SEED_BYTES,
  MLDSA65_SIGNATURE_SEED_BYTES,
  &sig_ml_dsa_65_method,
};

static const PQDSA sig_ml_dsa_87 = {
  NID_MLDSA87,
  kOIDMLDSA87,
  sizeof(kOIDMLDSA87),
  "MLDSA87",
  MLDSA87_PUBLIC_KEY_BYTES,
  MLDSA87_PRIVATE_KEY_BYTES,
  MLDSA87_SIGNATURE_BYTES,
  MLDSA87_KEYGEN_SEED_BYTES,
  MLDSA87_SIGNATURE_SEED_BYTES,
  &sig_ml_dsa_87_method,
};

const PQDSA *PQDSA_find_dsa_by_nid(int nid) {
  switch (nid) {
    case NID_MLDSA44:
      return &sig_ml_dsa_44;
    case NID_MLDSA65:
      return &sig_ml_dsa_65;
    case NID_MLDSA87:
      return &sig_ml_dsa_87;
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
