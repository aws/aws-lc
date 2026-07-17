// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "internal.h"

#include <assert.h>

#include "../internal.h"

// Keccak-256 (Ethereum-style, original 0x01 padding). NOT FIPS-approved.
//
// This reuses the FIPS module's FIPS 202 buffering primitives and Keccak-f[1600]
// permutation but initialises the context with the original Keccak padding byte
// (|KECCAK256_PAD_CHAR|) instead of a FIPS 202 one. Because the module's
// |FIPS202_Init| deliberately rejects non-FIPS-202 padding, we set up the
// context here rather than calling it.

int Keccak256_Init(KECCAK1600_CTX *ctx) {
  if (ctx == NULL) {
    return 0;
  }

  const size_t block_size = KECCAK256_CBLOCK;
  // Mirror the block-size bound |FIPS202_Init| enforces on the context buffer.
  if (block_size > sizeof(ctx->buf)) {
    return 0;
  }

  FIPS202_Reset(ctx);
  ctx->block_size = block_size;
  ctx->md_size = KECCAK256_DIGEST_LENGTH;
  ctx->pad = KECCAK256_PAD_CHAR;
  return 1;
}

int Keccak256_Update(KECCAK1600_CTX *ctx, const void *data, size_t len) {
  if (ctx == NULL) {
    return 0;
  }
  if (data == NULL && len != 0) {
    return 0;
  }
  if (len == 0) {
    return 1;
  }
  return FIPS202_Update(ctx, data, len);
}

int Keccak256_Final(uint8_t out[KECCAK256_DIGEST_LENGTH], KECCAK1600_CTX *ctx) {
  if (out == NULL || ctx == NULL) {
    return 0;
  }
  // This function must be paired with |Keccak256_Init|, which sets |md_size| to
  // |KECCAK256_DIGEST_LENGTH|. Unlike SHA-3/SHAKE, Keccak-256 is a fixed-length
  // hash, so |md_size| is never legitimately zero here.
  assert(ctx->md_size == KECCAK256_DIGEST_LENGTH);
  if (FIPS202_Finalize(out, ctx) == 0) {
    return 0;
  }
  Keccak1600_Squeeze(ctx->A, out, ctx->md_size, ctx->block_size, ctx->state);
  ctx->state = KECCAK1600_STATE_FINAL;
  // Intentionally no FIPS_service_indicator_update_state(): Keccak-256 with
  // 0x01 padding is not an approved service.
  return 1;
}

uint8_t *Keccak256(const uint8_t *data, size_t len,
                   uint8_t out[KECCAK256_DIGEST_LENGTH]) {
  KECCAK1600_CTX ctx;
  int ok = (Keccak256_Init(&ctx) &&
            Keccak256_Update(&ctx, data, len) &&
            Keccak256_Final(out, &ctx));

  OPENSSL_cleanse(&ctx, sizeof(ctx));
  if (ok == 0) {
    return NULL;
  }
  return out;
}
