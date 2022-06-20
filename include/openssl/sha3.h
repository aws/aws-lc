/*
 * Copyright 2019-2021 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the Apache License 2.0 (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */


#ifndef OSSL_INTERNAL_SHA3_H
#define OSSL_INTERNAL_SHA3_H

#include <openssl/base.h>
#include <stddef.h>

#if defined(__cplusplus)
extern "C" {
#endif

#define SHA3_256_DIGEST_LENGTH 32
#define SHA3_256_DIGEST_BITLENGTH 256
#define SHA3_256_BLOCK_SIZE 136
#define SHA3_256_CAPACITY_BYTES 64
#define SHA3_ROW_LENGTH 5
#define PAD_CHAR 6

// SHA3_256 writes the digest of |len| bytes from |data| to |out| and returns
// |out|. There must be at least |SHA3_256_DIGEST_LENGTH| bytes of space in
// |out|.
OPENSSL_EXPORT uint8_t *SHA3_256(const uint8_t *data, size_t len,
                                 uint8_t out[SHA3_256_DIGEST_LENGTH]);

#define KECCAK1600_WIDTH 1600
#define SHA3_BLOCKSIZE(bitlen) (KECCAK1600_WIDTH - bitlen * 2) / 8

typedef struct keccak_st KECCAK1600_CTX;

struct keccak_st {
  uint64_t A[SHA3_ROW_LENGTH][SHA3_ROW_LENGTH];
  size_t block_size; /* cached ctx->digest->block_size */
  size_t md_size;    /* output length, variable in XOF */
  size_t buf_load;      /* used bytes in below buffer */
  uint8_t buf[KECCAK1600_WIDTH / 8 - SHA3_256_CAPACITY_BYTES];
  unsigned char pad;
};

// SHA3_Reset resets the bitstate and the buffer load.
OPENSSL_EXPORT void SHA3_Reset(KECCAK1600_CTX *ctx);

// SHA3_Init initialises ctx fields and returns 1 on success.
OPENSSL_EXPORT int SHA3_Init(KECCAK1600_CTX *ctx, unsigned char pad,
                             size_t bitlen);

// SHA3_Update proccesses |len| bytes of _inp through the absorbing function and returns 1.
OPENSSL_EXPORT int SHA3_Update(KECCAK1600_CTX *ctx, const void *_inp,
                               size_t len);

// SHA3_Final pads the last block of data and proccess through the absorbing function. 
//Processes the data through squeeze function and returns 1.
OPENSSL_EXPORT int SHA3_Final(unsigned char *md, KECCAK1600_CTX *ctx);

// SHA3_Absorb processes the largest multiple of |r| out of |len| bytes and 
// returns the remaining amount of bytes. 
OPENSSL_EXPORT size_t SHA3_Absorb(uint64_t A[SHA3_ROW_LENGTH][SHA3_ROW_LENGTH], const unsigned char *inp,
                                  size_t len, size_t r);

// SHA3_Squeeze generate |out| hash value of |len| bytes.
OPENSSL_EXPORT void SHA3_Squeeze(uint64_t A[SHA3_ROW_LENGTH][SHA3_ROW_LENGTH], unsigned char *out,
                                 size_t len, size_t r);
#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_SHA3_H
