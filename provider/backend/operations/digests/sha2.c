// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// Back side: AWS-LC's SHA-2. This file sees AWS-LC's headers, so it must not
// include any OpenSSL provider header.

#include <openssl/sha.h>

#include "internal/backend/digests.h"

size_t awslc_prov_sha256_ctx_size(void) { return sizeof(SHA256_CTX); }

size_t awslc_prov_sha256_digest_size(void) { return SHA256_DIGEST_LENGTH; }

size_t awslc_prov_sha256_block_size(void) { return SHA256_CBLOCK; }

int awslc_prov_sha256_init(void *ctx) {
  if (ctx == NULL) {
    return 0;
  }
  return SHA256_Init((SHA256_CTX *)ctx);
}

int awslc_prov_sha256_update(void *ctx, const void *data, size_t len) {
  if (ctx == NULL || (data == NULL && len != 0)) {
    return 0;
  }
  return SHA256_Update((SHA256_CTX *)ctx, data, len);
}

int awslc_prov_sha256_final(void *ctx, unsigned char *out, size_t out_size) {
  if (ctx == NULL || out == NULL) {
    return 0;
  }
  // SHA256_Final takes no output size and documents that |out| must have room
  // for SHA256_DIGEST_LENGTH bytes. OpenSSL's digest final slot passes the
  // buffer size and expects a clean failure when it is too small, so a short
  // buffer must not reach SHA256_Final at all.
  if (out_size < SHA256_DIGEST_LENGTH) {
    return 0;
  }
  return SHA256_Final(out, (SHA256_CTX *)ctx);
}

int awslc_prov_sha256_copy(void *dst, const void *src) {
  if (dst == NULL || src == NULL) {
    return 0;
  }
  *(SHA256_CTX *)dst = *(const SHA256_CTX *)src;
  return 1;
}
