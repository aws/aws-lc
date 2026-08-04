// Copyright (c) 2016, Google Inc.
// SPDX-License-Identifier: ISC

#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/mem.h>
#include <openssl/pem.h>


extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  char *name, *header;
  uint8_t *pem_data;
  long pem_len;

  BIO *bio = BIO_new_mem_buf(buf, len);

  if (PEM_read_bio(bio, &name, &header, &pem_data, &pem_len) == 1) {
    OPENSSL_free(name);
    OPENSSL_free(header);
    OPENSSL_free(pem_data);
  }

  BIO_free(bio);

  ERR_clear_error();
  return 0;
}
