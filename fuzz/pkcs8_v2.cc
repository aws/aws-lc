// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/bytestring.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/mem.h>


extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  CBS cbs;
  CBS_init(&cbs, buf, len);
  EVP_PKEY *pkey = EVP_parse_private_key(&cbs);
  if (pkey == NULL) {
    return 0;
  }

  uint8_t *der;
  size_t der_len;
  CBB cbb;
  if (CBB_init(&cbb, 0) &&
      EVP_marshal_private_key_v2(&cbb, pkey) &&
      CBB_finish(&cbb, &der, &der_len)) {
    OPENSSL_free(der);
  }
  CBB_cleanup(&cbb);
  EVP_PKEY_free(pkey);
  ERR_clear_error();
  return 0;
}
