/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef MLK_AWSLC_FIPS202_GLUE_H
#define MLK_AWSLC_FIPS202_GLUE_H
#include <stddef.h>
#include <stdint.h>

#include "../sha/internal.h"

#define SHAKE128_RATE 168
#define SHAKE256_RATE 136
#define SHA3_256_RATE 136
#define SHA3_384_RATE 104
#define SHA3_512_RATE 72

#define shake128ctx KECCAK1600_CTX

static MLK_INLINE void shake128_init(shake128ctx *state)
{
  /* Return code checks can be omitted
   * SHAKE_Init always returns 1 when called with correct block size value */
  (void) SHAKE_Init(state, SHAKE128_BLOCKSIZE);
}

static MLK_INLINE void shake128_release(shake128ctx *state)
{
  (void) state;
}

static MLK_INLINE void shake128_absorb_once(shake128ctx *state,
                                            const uint8_t *input, size_t inlen)
{
  /* TODO: Document why this function does not fail in the context
   *       of the calls made by mlkem-native. */
  (void) SHAKE_Absorb(state, input, inlen);
}

static MLK_INLINE void shake128_squeezeblocks(uint8_t *output, size_t nblocks,
                                              shake128ctx *state)
{
  /* TODO: Document why this function does not fail in the context
   *       of the calls made by mlkem-native. */
  (void) SHAKE_Squeeze(output, state, nblocks * SHAKE128_RATE);
}

static MLK_INLINE void shake256(uint8_t *output, size_t outlen,
                                const uint8_t *input, size_t inlen)
{
  /* TODO: Document why this function does not fail in the context
   *       of the calls made by mlkem-native. */
  (void) SHAKE256(input, inlen, output, outlen);
}

static MLK_INLINE void sha3_256(uint8_t *output, const uint8_t *input,
                                size_t inlen)
{
  /* TODO: Document why this function does not fail in the context
   *       of the calls made by mlkem-native. */
  (void) SHA3_256(input, inlen, output);
}

static MLK_INLINE void sha3_512(uint8_t *output, const uint8_t *input,
                                size_t inlen)
{
  /* TODO: Document why this function does not fail in the context
   *       of the calls made by mlkem-native. */
  (void) SHA3_512(input, inlen, output);
}

#endif /* MLK_AWSLC_FIPS202_GLUE_H */
