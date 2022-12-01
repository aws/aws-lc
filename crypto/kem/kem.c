// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/mem.h>
#include <openssl/nid.h>

#include "../fipsmodule/delocate.h"
#include "../internal.h"
#include "internal.h"

DEFINE_METHOD_FUNCTION(struct built_in_kems, AWSLC_built_in_kems) {
  // TODO(awslc): placeholder OID, replace with the real one when available.
  static const uint8_t kOIDKyber512[] = {0xff, 0xff, 0xff, 0xff};
  out->kems[0].nid = NID_KYBER512;
  out->kems[0].oid = kOIDKyber512;
  out->kems[0].oid_len = sizeof(kOIDKyber512);
  out->kems[0].comment = "Kyber512";
  out->kems[0].public_key_len = 800;
  out->kems[0].secret_key_len = 1632;
  out->kems[0].ciphertext_len = 768;
  out->kems[0].shared_secret_len = 32;
  out->kems[0].method = KEM_kyber512_method();

  // Example how adding new KEM looks like:
  //
  // static const uint8_t kOIDKyber768[] = {0xff, 0xff, 0xff, 0xff};
  // out->kems[1].nid = NID_KYBER768;
  // out->kems[1].oid = kOIDKyber768;
  // out->kems[1].oid_len = sizeof(kOIDKyber768);
  // out->kems[1].comment = "Kyber768";
  // out->kems[1].public_key_len = 1184;
  // out->kems[1].secret_key_len = 2400;
  // out->kems[1].ciphertext_len = 1088;
  // out->kems[1].shared_secret_len = 32;
  // out->kems[1].method = KEM_kyber768_method();
}

const KEM *KEM_find_kem_by_nid(int nid) {
  const struct built_in_kems *kems = AWSLC_built_in_kems();
  const KEM *ret = NULL;
  for (size_t i = 0; i < AWSLC_NUM_BUILT_IN_KEMS; i++) {
    if (kems->kems[i].nid == nid) {
      ret = &kems->kems[i];
      break;
    }
  }
  return ret;
}

KEM_KEY *KEM_KEY_new(void) {
  KEM_KEY *ret = OPENSSL_malloc(sizeof(KEM_KEY));
  if (ret == NULL) {
    return NULL;
  }

  OPENSSL_memset(ret, 0, sizeof(KEM_KEY));
  return ret;
}

int KEM_KEY_init(KEM_KEY *key, const KEM *kem) {
  if (key == NULL || kem == NULL) {
    return 0;
  }

  key->kem = kem;
  key->public_key = OPENSSL_malloc(kem->public_key_len);
  key->secret_key = OPENSSL_malloc(kem->secret_key_len);
  key->has_secret_key = 0;
  if (key->public_key == NULL || key->secret_key == NULL) {
    KEM_KEY_free(key);
    return 0;
  }

  return 1;
}

void KEM_KEY_free(KEM_KEY *key) {
  key->kem = NULL;
  OPENSSL_free(key->public_key);
  OPENSSL_free(key->secret_key);
}

const KEM *KEM_KEY_get0_kem(KEM_KEY* key) {
  return key->kem;
}
