// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_HEADER_CMAC_INTERNAL_H
#define AWSLC_HEADER_CMAC_INTERNAL_H

#include <openssl/base.h>

#if defined(__cplusplus)
extern "C" {
#endif

struct cmac_ctx_st {
  EVP_CIPHER_CTX cipher_ctx;
  // k1 and k2 are the CMAC subkeys. See
  // https://tools.ietf.org/html/rfc4493#section-2.3
  uint8_t k1[AES_BLOCK_SIZE];
  uint8_t k2[AES_BLOCK_SIZE];
  // Last (possibly partial) scratch
  uint8_t block[AES_BLOCK_SIZE];
  // block_used contains the number of valid bytes in |block|.
  unsigned block_used;
};

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_CMAC_INTERNAL_H
