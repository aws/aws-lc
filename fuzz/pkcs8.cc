// Copyright (c) 2016, Google Inc.
// SPDX-License-Identifier: ISC

#include <openssl/bytestring.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/mem.h>

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  CBS cbs;
  CBS_init(&cbs, buf, len);
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_parse_private_key(&cbs));
  if (pkey == nullptr) {
    ERR_clear_error();
    return 0;
  }

  if (EVP_PKEY_id(pkey.get()) != EVP_PKEY_RSA_PSS) {
    // Every parsed private key should be serializable.
    bssl::ScopedCBB cbb;
    BSSL_CHECK(CBB_init(cbb.get(), 0));
    BSSL_CHECK(EVP_marshal_public_key(cbb.get(), pkey.get()));
    BSSL_CHECK(EVP_marshal_private_key(cbb.get(), pkey.get()));

    bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_mem()));
    EVP_PKEY_print_params(bio.get(), pkey.get(), 0, nullptr);
    EVP_PKEY_print_public(bio.get(), pkey.get(), 0, nullptr);
    EVP_PKEY_print_private(bio.get(), pkey.get(), 0, nullptr);
  }

  ERR_clear_error();
  return 0;
}
