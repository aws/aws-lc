// Copyright (c) 2016, Google Inc.
// SPDX-License-Identifier: ISC

#include <openssl/err.h>
#include <openssl/evp.h>

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  EVP_PKEY_free(d2i_AutoPrivateKey(NULL, &buf, len));
  ERR_clear_error();
  return 0;
}
