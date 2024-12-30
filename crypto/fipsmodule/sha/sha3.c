/*
 * Copyright 2017-2020 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the Apache License 2.0 (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

#include "internal.h"
#include <string.h>

uint8_t *SHA3_224(const uint8_t *data, size_t len,
                  uint8_t out[SHA3_224_DIGEST_LENGTH]) {
  FIPS_service_indicator_lock_state();
  KECCAK1600_CTX ctx;
  int ok = (SHA3_Init(&ctx, SHA3_224_DIGEST_BITLENGTH) &&
            SHA3_Update(&ctx, data, len) &&
            SHA3_Final(out, &ctx));

  OPENSSL_cleanse(&ctx, sizeof(ctx));
  FIPS_service_indicator_unlock_state();
  if (ok == 0) {
    return NULL;
  }
  FIPS_service_indicator_update_state();
  return out;
}

uint8_t *SHA3_256(const uint8_t *data, size_t len,
                  uint8_t out[SHA3_256_DIGEST_LENGTH]) {
  FIPS_service_indicator_lock_state();
  KECCAK1600_CTX ctx;
  int ok = (SHA3_Init(&ctx, SHA3_256_DIGEST_BITLENGTH) &&
            SHA3_Update(&ctx, data, len) &&
            SHA3_Final(out, &ctx));

  OPENSSL_cleanse(&ctx, sizeof(ctx));
  FIPS_service_indicator_unlock_state();
  if (ok == 0) {
    return NULL;
  }
  FIPS_service_indicator_update_state();
  return out;
}

uint8_t *SHA3_384(const uint8_t *data, size_t len,
                  uint8_t out[SHA3_384_DIGEST_LENGTH]) {
  FIPS_service_indicator_lock_state();
  KECCAK1600_CTX ctx;
  int ok = (SHA3_Init(&ctx, SHA3_384_DIGEST_BITLENGTH) &&
            SHA3_Update(&ctx, data, len) &&
            SHA3_Final(out, &ctx));

  OPENSSL_cleanse(&ctx, sizeof(ctx));
  FIPS_service_indicator_unlock_state();
  if (ok == 0) {
    return NULL;
  }
  FIPS_service_indicator_update_state();
  return out;
}

uint8_t *SHA3_512(const uint8_t *data, size_t len,
                  uint8_t out[SHA3_512_DIGEST_LENGTH]) {
  FIPS_service_indicator_lock_state();
  KECCAK1600_CTX ctx;
  int ok = (SHA3_Init(&ctx, SHA3_512_DIGEST_BITLENGTH) &&
            SHA3_Update(&ctx, data, len) &&
            SHA3_Final(out, &ctx));

  OPENSSL_cleanse(&ctx, sizeof(ctx));
  FIPS_service_indicator_unlock_state();
  if (ok == 0) {
    return NULL;
  }
  FIPS_service_indicator_update_state();
  return out;
}

uint8_t *SHAKE128(const uint8_t *data, const size_t in_len, uint8_t *out, size_t out_len) {
  FIPS_service_indicator_lock_state();
  KECCAK1600_CTX ctx;
  int ok = (SHAKE_Init(&ctx, SHAKE128_BLOCKSIZE) &&
            SHAKE_Update(&ctx, data, in_len) &&
            SHAKE_Finalize(out, &ctx, out_len));

  OPENSSL_cleanse(&ctx, sizeof(ctx));
  FIPS_service_indicator_unlock_state();
  if (ok == 0) {
    return NULL;
  }
  FIPS_service_indicator_update_state();
  return out;
}

uint8_t *SHAKE256(const uint8_t *data, const size_t in_len, uint8_t *out, size_t out_len) {
  FIPS_service_indicator_lock_state();
  KECCAK1600_CTX ctx;
  int ok = (SHAKE_Init(&ctx, SHAKE256_BLOCKSIZE) &&
            SHAKE_Update(&ctx, data, in_len) &&
            SHAKE_Finalize(out, &ctx, out_len));
  OPENSSL_cleanse(&ctx, sizeof(ctx));
  FIPS_service_indicator_unlock_state();
  if (ok == 0) {
    return NULL;
  }
  FIPS_service_indicator_update_state();
  return out;
}

// FIPS202 APIs manage internal input/output buffer on top of Keccak1600 API layer
void FIPS202_Reset(KECCAK1600_CTX *ctx) {
  memset(ctx->A, 0, sizeof(ctx->A));
  ctx->buf_load = 0;
  ctx->padded = 0;
}

int FIPS202_Init(KECCAK1600_CTX *ctx, uint8_t pad, size_t block_size, size_t bit_len) {
  if (ctx == NULL) {
    return 0;
  }

  if (pad != SHA3_PAD_CHAR && 
      pad != SHAKE_PAD_CHAR) { 
    return 0;
  }
      
  if (block_size <= sizeof(ctx->buf)) {
      FIPS202_Reset(ctx);
      ctx->block_size = block_size;
      ctx->md_size = bit_len / 8;
      ctx->pad = pad;
      return 1;
    }
    return 0;
}

int FIPS202_Update(KECCAK1600_CTX *ctx, const void *data, size_t len) {
  uint8_t *data_ptr_copy = (uint8_t *) data;
  size_t block_size = ctx->block_size;
  size_t num, rem;

  // Case |len| equals 0 is checked in SHA3/SHAKE higher level APIs
  // Process intermediate buffer.
  num = ctx->buf_load;
  if (num != 0) {
    rem = block_size - num;
    if (len < rem) {
      memcpy(ctx->buf + num, data_ptr_copy, len);
      ctx->buf_load += len;
      return 1;
    }

    // There is enough data to fill or overflow the intermediate
    // buffer. So we append |rem| bytes and process the block,
    // leaving the rest for later processing.
    memcpy(ctx->buf + num, data_ptr_copy, rem);
    data_ptr_copy += rem, len -= rem;
    if (Keccak1600_Absorb(ctx->A, ctx->buf, block_size, block_size) != 0 ) {
      return 0;
    }
    ctx->buf_load = 0;
    // ctx->buf is processed, ctx->buf_load is guaranteed to be zero
  }

  if (len >= block_size) {
    rem = Keccak1600_Absorb(ctx->A, data_ptr_copy, len, block_size);
  }
  else {
    rem = len;
  }

  if (rem != 0) {
    memcpy(ctx->buf, data_ptr_copy + len - rem, rem);
    ctx->buf_load = rem;
  }

  return 1;
}

// FIPS202_Finalize processes padding and absorb of last input block
// This function should be called once to finalize absorb and initiate squeeze phase
int FIPS202_Finalize(uint8_t *md, KECCAK1600_CTX *ctx) {
  size_t block_size = ctx->block_size;
  size_t num = ctx->buf_load;

  if (ctx->padded == 1) {
    return 0;
  }

  // Pad the data with 10*1. Note that |num| can be |block_size - 1|
  // in which case both byte operations below are performed on
  // the same byte.
  memset(ctx->buf + num, 0, block_size - num);
  ctx->buf[num] = ctx->pad;
  ctx->buf[block_size - 1] |= 0x80;

  if (Keccak1600_Absorb(ctx->A, ctx->buf, block_size, block_size) != 0) {
    return 0;
  }

  return 1;
}

int SHA3_Init(KECCAK1600_CTX *ctx, size_t bit_len) {
  if (bit_len == SHA3_224_DIGEST_BITLENGTH || 
      bit_len == SHA3_256_DIGEST_BITLENGTH || 
      bit_len == SHA3_384_DIGEST_BITLENGTH || 
      bit_len == SHA3_512_DIGEST_BITLENGTH) { 
        // |block_size| depends on the SHA3 |bit_len| output (digest) length
        return FIPS202_Init(ctx, SHA3_PAD_CHAR, SHA3_BLOCKSIZE(bit_len), bit_len);
  }
  return 0;
}

int SHA3_Update(KECCAK1600_CTX *ctx, const void *data, size_t len) {
  if (ctx == NULL) {
    return 0;
  }

  if (len == 0) {
    return 1;
  }

  return FIPS202_Update(ctx, data, len);
}

// SHA3_Final should be called once to process final digest value
// |ctx->padded| flag does not need to be updated
int SHA3_Final(uint8_t *md, KECCAK1600_CTX *ctx) {
  if (ctx->md_size == 0) {
    return 1;
  }

  if (FIPS202_Finalize(md, ctx) == 0) {
    return 0;
  }

  Keccak1600_Squeeze(ctx->A, md, ctx->md_size, ctx->block_size, ctx->padded);
  
  FIPS_service_indicator_update_state();
  return 1;
}

int SHAKE_Init(KECCAK1600_CTX *ctx, size_t block_size) {
  if (block_size == SHAKE128_BLOCKSIZE ||
      block_size == SHAKE256_BLOCKSIZE) { 
        // |block_size| depends on the SHAKE security level
        // The output length |bit_len| is initialized to 0
        return FIPS202_Init(ctx, SHAKE_PAD_CHAR, block_size, 0);
  }
  return 0;
}

int SHAKE_Update(KECCAK1600_CTX *ctx, const void *data, size_t len) {
  if (ctx == NULL) {
    return 0;
  }

  if (len == 0) {
    return 1;
  }

  return FIPS202_Update(ctx, data, len);
}

// SHAKE_Finalize should be called once to finalize absorb and initiate squeeze phase
// |ctx->padded| restricts consecutive calls to FIPS202_Finalize
// Function SHAKE_Squeeze should be used for incremental XOF output
int SHAKE_Finalize(uint8_t *md, KECCAK1600_CTX *ctx, size_t len) {
  ctx->md_size = len;
  if (ctx->md_size == 0) {
    return 1;
  }

  if (FIPS202_Finalize(md, ctx) == 0) {
    return 0;
  }

  Keccak1600_Squeeze(ctx->A, md, ctx->md_size, ctx->block_size, ctx->padded);
  ctx->padded = 1;
  return 1;
}

// SHAKE_Squeeze can be called multiple times after SHAKE_Finalize
// SHAKE_Squeeze should be called for incremental XOF output
// |ctx->padded| flag should be set by SHAKE_Finalize function
int SHAKE_Squeeze(uint8_t *md, KECCAK1600_CTX *ctx, size_t len) {
  if (ctx->padded == 0) {
    return 0;
  }

  Keccak1600_Squeeze(ctx->A, md, len, ctx->block_size, ctx->padded);
  return 1;
}
