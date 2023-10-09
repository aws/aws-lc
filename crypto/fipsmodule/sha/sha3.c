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
  int ok = (SHA3_Init(&ctx, SHA3_PAD_CHAR, SHA3_224_DIGEST_BITLENGTH) && 
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
  int ok = (SHA3_Init(&ctx, SHA3_PAD_CHAR, SHA3_256_DIGEST_BITLENGTH) && 
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
  int ok = (SHA3_Init(&ctx, SHA3_PAD_CHAR, SHA3_384_DIGEST_BITLENGTH) && 
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
  int ok = (SHA3_Init(&ctx, SHA3_PAD_CHAR, SHA3_512_DIGEST_BITLENGTH) && 
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
            SHA3_Update(&ctx, data, in_len) &&
            SHAKE_Final(out, &ctx, out_len));

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
            SHA3_Update(&ctx, data, in_len) &&
            SHAKE_Final(out, &ctx, out_len));
  OPENSSL_cleanse(&ctx, sizeof(ctx));
  FIPS_service_indicator_unlock_state();
  if (ok == 0) {
    return NULL;
  }
  FIPS_service_indicator_update_state();
  return out;
}

int SHAKE_Init(KECCAK1600_CTX *ctx, size_t block_size) {
  // The SHAKE block size depends on the security level of the algorithm only
  // It is independent of the output size
  ctx->block_size = block_size;
  return SHA3_Init(ctx, SHAKE_PAD_CHAR, 0);
}


int SHAKE_Final(uint8_t *md, KECCAK1600_CTX *ctx, size_t len) {
  ctx->md_size = len;
  return SHA3_Final(md, ctx);
}

void SHA3_Reset(KECCAK1600_CTX *ctx) {
  memset(ctx->A, 0, sizeof(ctx->A));
  ctx->buf_load = 0;
}

int SHA3_Init(KECCAK1600_CTX *ctx, uint8_t pad, size_t bit_len) {
  size_t block_size;

  // The block size is computed differently depending on which algorithm
  // is calling |SHA3_Init|:
  //   - for SHA3 we compute it by calling SHA3_BLOCKSIZE(bit_len)
  //     because the block size depends on the digest bit-length,
  //   - for SHAKE we take the block size from the context.
  // We use the given padding character to differentiate between SHA3 and SHAKE.
  if (pad == SHA3_PAD_CHAR) {
    block_size = SHA3_BLOCKSIZE(bit_len);
  } else if (pad == SHAKE_PAD_CHAR) {
    block_size = ctx->block_size;
  } else {
    return 0;
  }
  
  if (block_size <= sizeof(ctx->buf)) {
    SHA3_Reset(ctx);
    ctx->block_size = block_size;
    ctx->md_size = bit_len / 8;
    ctx->pad = pad;
    return 1;
  }
  return 0;
}

int SHA3_Update(KECCAK1600_CTX *ctx, const void *data, size_t len) {
  uint8_t *data_ptr_copy = (uint8_t *) data;
  size_t block_size = ctx->block_size;
  size_t num, rem;

  if (len == 0) {
    return 1;
  }

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
    if (SHA3_Absorb(ctx->A, ctx->buf, block_size, block_size) != 0 ) {
      return 0;
    }
    ctx->buf_load = 0;
    // ctx->buf is processed, ctx->buf_load is guaranteed to be zero
  }

  if (len >= block_size) {
    rem = SHA3_Absorb(ctx->A, data_ptr_copy, len, block_size);
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

int SHA3_Final(uint8_t *md, KECCAK1600_CTX *ctx) {
  size_t block_size = ctx->block_size;
  size_t num = ctx->buf_load;

  if (ctx->md_size == 0) {
    return 1;
  }

   // Pad the data with 10*1. Note that |num| can be |block_size - 1|
   // in which case both byte operations below are performed on
   // the same byte.
  memset(ctx->buf + num, 0, block_size - num);
  ctx->buf[num] = ctx->pad;
  ctx->buf[block_size - 1] |= 0x80;

  if (SHA3_Absorb(ctx->A, ctx->buf, block_size, block_size) != 0) {
    return 0;
  }

  SHA3_Squeeze(ctx->A, md, ctx->md_size, block_size);

  FIPS_service_indicator_update_state();

  return 1;
}
