// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/asn1.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/mem.h>

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_mem()));
  if(len > LONG_MAX) {
    return 0;
  }
  ASN1_parse(bio.get(), buf, len, 0);
  return 0;
}
