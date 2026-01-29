/* Copyright (c) 2016, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#include <openssl/bytestring.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/mem.h>

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  CBS cbs;
  CBS_init(&cbs, buf, len);
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_parse_public_key(&cbs));
  if (pkey == nullptr) {
    ERR_clear_error();
    return 0;
  }

  if (EVP_PKEY_id(pkey.get()) != EVP_PKEY_RSA_PSS) {
    // Every parsed public key should be serializable.
    bssl::ScopedCBB cbb;
    BSSL_CHECK(CBB_init(cbb.get(), 0));
    BSSL_CHECK(EVP_marshal_public_key(cbb.get(), pkey.get()));

    bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_mem()));
    EVP_PKEY_print_params(bio.get(), pkey.get(), 0, nullptr);
    EVP_PKEY_print_public(bio.get(), pkey.get(), 0, nullptr);
  }

  ERR_clear_error();
  return 0;
}
