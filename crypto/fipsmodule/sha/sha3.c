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

uint8_t *SHA3_256(const uint8_t *data, size_t len,
                  uint8_t out[SHA3_256_DIGEST_LENGTH]) {
  KECCAK1600_CTX ctx;
  int ok = (SHA3_Init(&ctx, SHA3_PAD_CHAR, SHA3_256_DIGEST_BITLENGTH) && 
            SHA3_Update(&ctx, data, len) &&
            SHA3_Final(out, &ctx));

  OPENSSL_cleanse(&ctx, sizeof(ctx));
  if (ok == 0){
    return NULL;
  }
  return out;
}

void SHA3_Reset(KECCAK1600_CTX *ctx) {
  memset(ctx->A, 0, sizeof(ctx->A));
  ctx->buf_load = 0;
}

int SHA3_Init(KECCAK1600_CTX *ctx, unsigned char pad, size_t bit_len) {
  size_t block_size = SHA3_BLOCKSIZE(bit_len);
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
  unsigned char *data_ptr_copy = (unsigned char *) data;
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
    if (SHA3_Absorb(ctx->A, ctx->buf, block_size, block_size) != 0 ){
      return 0;
    }
    ctx->buf_load = 0;
    // ctx->buf is processed, ctx->buf_load is guaranteed to be zero
  }

  if (len >= block_size) {
    rem = SHA3_Absorb(ctx->A, data_ptr_copy, len, block_size);
  }
  else{
    rem = len;
  }

  if (rem != 0) {
    memcpy(ctx->buf, data_ptr_copy + len - rem, rem);
    ctx->buf_load = rem;
  }

  return 1;
}

int SHA3_Final(unsigned char *md, KECCAK1600_CTX *ctx) {
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

  if (SHA3_Absorb(ctx->A, ctx->buf, block_size, block_size) != 0){
    return 0;
  }

  SHA3_Squeeze(ctx->A, md, ctx->md_size, block_size);

  return 1;
}
