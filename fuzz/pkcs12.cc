// Copyright (c) 2018, Google Inc.
// SPDX-License-Identifier: ISC

#include <openssl/bytestring.h>
#include <openssl/evp.h>
#include <openssl/pkcs8.h>
#include <openssl/x509.h>


extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  bssl::UniquePtr<STACK_OF(X509)> certs(sk_X509_new_null());
  EVP_PKEY *key = nullptr;
  CBS cbs;
  CBS_init(&cbs, buf, len);
  PKCS12_get_key_and_certs(&key, certs.get(), &cbs, "foo");
  EVP_PKEY_free(key);
  return 0;
}
