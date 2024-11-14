// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC
#include <openssl/evp.h>
#include <openssl/mem.h>

#include <openssl/base.h>
#include "internal.h"
#include "../fipsmodule/delocate.h"
#include "ml_dsa.h"

// ML-DSA OIDs as defined within:
// https://csrc.nist.gov/projects/computer-security-objects-register/algorithm-registration
//2.16.840.1.101.3.4.3.18
static const uint8_t kOIDMLDSA65[]  = {0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x12};

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

DEFINE_LOCAL_DATA(PQDSA_METHOD, sig_ml_dsa_65_method) {
  out->keygen = ml_dsa_65_keypair;
  out->sign = ml_dsa_65_sign;
  out->verify = ml_dsa_65_verify;
}

DEFINE_LOCAL_DATA(PQDSA, sig_ml_dsa_65) {
  out->nid = NID_MLDSA65;
  out->oid = kOIDMLDSA65;
  out->oid_len = sizeof(kOIDMLDSA65);
  out->comment = "MLDSA65 ";
  out->public_key_len = MLDSA65_PUBLIC_KEY_BYTES;
  out->private_key_len = MLDSA65_PRIVATE_KEY_BYTES;
  out->signature_len = MLDSA65_SIGNATURE_BYTES;
  out->keygen_seed_len = MLDSA65_KEYGEN_SEED_BYTES;
  out->sign_seed_len = MLDSA65_SIGNATURE_SEED_BYTES;
  out->method = sig_ml_dsa_65_method();
}

const PQDSA *PQDSA_find_dsa_by_nid(int nid) {
  switch (nid) {
    case NID_MLDSA65:
      return sig_ml_dsa_65();
    default:
      return NULL;
  }
}
