// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/evp.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include "../crypto/internal.h"
#include "../evp_extra/internal.h"
#include "../fipsmodule/delocate.h"
#include "../fipsmodule/evp/internal.h"
#include "../ml_dsa/ml_dsa.h"
#include "internal.h"

//https://csrc.nist.gov/projects/computer-security-objects-register/algorithm-registration
//2.16.840.1.101.3.4.3.17
static const uint8_t kOIDMLDSA44[]  = {0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x11};
//2.16.840.1.101.3.4.3.18
static const uint8_t kOIDMLDSA65[]  = {0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x12};
//2.16.840.1.101.3.4.3.19
static const uint8_t kOIDMLDSA87[]  = {0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x13};

NISTDSA_KEY *NISTDSA_KEY_new(void) {
  NISTDSA_KEY *ret = OPENSSL_zalloc(sizeof(NISTDSA_KEY));
  if (ret == NULL) {
    return NULL;
  }

  return ret;
}

static void NISTDSA_KEY_clear(NISTDSA_KEY *key) {
  key->nistdsa = NULL;
  OPENSSL_free(key->public_key);
  OPENSSL_free(key->secret_key);
  key->public_key = NULL;
  key->secret_key = NULL;
}

int NISTDSA_KEY_init(NISTDSA_KEY *key, const NISTDSA *nistdsa) {
  if (key == NULL || nistdsa == NULL) {
    return 0;
  }
  // If the key is already initialized clear it.
  NISTDSA_KEY_clear(key);

  key->nistdsa = nistdsa;
  key->public_key = OPENSSL_malloc(nistdsa->public_key_len);
  key->secret_key = OPENSSL_malloc(nistdsa->secret_key_len);
  if (key->public_key == NULL || key->secret_key == NULL) {
    NISTDSA_KEY_clear(key);
    return 0;
  }

  return 1;
}

void NISTDSA_KEY_free(NISTDSA_KEY *key) {
  if (key == NULL) {
    return;
  }
  NISTDSA_KEY_clear(key);
  OPENSSL_free(key);
}

const NISTDSA *NISTDSA_KEY_get0_sig(NISTDSA_KEY* key) {
  return key->nistdsa;
}

DEFINE_LOCAL_DATA(NISTDSA_METHOD, nist_ml_dsa_44_method) {
  out->keygen = ml_dsa_44_keypair;
  out->sign = ml_dsa_44_sign;
  out->verify = ml_dsa_44_verify;
}

DEFINE_LOCAL_DATA(NISTDSA, nist_dsa_ml_dsa_44) {
  out->nid = NID_MLDSA44;
  out->oid = kOIDMLDSA44;
  out->oid_len = sizeof(kOIDMLDSA44);
  out->comment = "MLDSA44 ";
  out->public_key_len = MLDSA44_PUBLIC_KEY_BYTES;
  out->secret_key_len = MLDSA44_PRIVATE_KEY_BYTES;
  out->signature_len = MLDSA44_SIGNATURE_BYTES;
  out->keygen_seed_len = MLDSA44_KEYGEN_SEED_BYTES;
  out->sign_seed_len = MLDSA44_SIGNATURE_SEED_BYTES;
  out->method = nist_ml_dsa_44_method();
  out->asn1_method = &nistdsa_asn1_meth;
}

DEFINE_LOCAL_DATA(NISTDSA_METHOD, nist_ml_dsa_65_method) {
  out->keygen = ml_dsa_65_keypair;
  out->sign = ml_dsa_65_sign;
  out->verify = ml_dsa_65_verify;
}

DEFINE_LOCAL_DATA(NISTDSA, nist_dsa_ml_dsa_65) {
  out->nid = NID_MLDSA65;
  out->oid = kOIDMLDSA65;
  out->oid_len = sizeof(kOIDMLDSA65);
  out->comment = "MLDSA65 ";
  out->public_key_len = MLDSA65_PUBLIC_KEY_BYTES;
  out->secret_key_len = MLDSA65_PRIVATE_KEY_BYTES;
  out->signature_len = MLDSA65_SIGNATURE_BYTES;
  out->keygen_seed_len = MLDSA65_KEYGEN_SEED_BYTES;
  out->sign_seed_len = MLDSA65_SIGNATURE_SEED_BYTES;
  out->method = nist_ml_dsa_65_method();
  out->asn1_method = &nistdsa_asn1_meth;
}

DEFINE_LOCAL_DATA(NISTDSA_METHOD, nist_ml_dsa_87_method) {
  out->keygen = ml_dsa_87_keypair;
  out->sign = ml_dsa_87_sign;
  out->verify = ml_dsa_87_verify;
}

DEFINE_LOCAL_DATA(NISTDSA, nist_dsa_ml_dsa_87) {
  out->nid = NID_MLDSA87;
  out->oid = kOIDMLDSA87;
  out->oid_len = sizeof(kOIDMLDSA87);
  out->comment = "MLDSA87 ";
  out->public_key_len = MLDSA87_PUBLIC_KEY_BYTES;
  out->secret_key_len = MLDSA87_PRIVATE_KEY_BYTES;
  out->signature_len = MLDSA87_SIGNATURE_BYTES;
  out->keygen_seed_len = MLDSA87_KEYGEN_SEED_BYTES;
  out->sign_seed_len = MLDSA87_SIGNATURE_SEED_BYTES;
  out->method = nist_ml_dsa_87_method();
  out->asn1_method = &nistdsa_asn1_meth;
}

const NISTDSA *SIG_find_dsa_by_nid(int nid) {
  switch (nid) {
    case NID_MLDSA44:
      return nist_dsa_ml_dsa_44();
    case NID_MLDSA65:
      return nist_dsa_ml_dsa_65();
    case NID_MLDSA87:
      return nist_dsa_ml_dsa_87();
    default:
      return NULL;
  }
}
