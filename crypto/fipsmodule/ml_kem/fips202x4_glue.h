// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

//
// This is a shim establishing the FIPS-202 API required by
// mlkem-native from the API exposed by AWS-LC.
//

#ifndef MLK_AWSLC_FIPS202X4_GLUE_H
#define MLK_AWSLC_FIPS202X4_GLUE_H

#include <stddef.h>
#include <stdint.h>

#include "fips202_glue.h"

typedef mlk_shake128ctx mlk_shake128x4ctx[4];

static MLK_INLINE void mlk_shake128x4_absorb_once(mlk_shake128x4ctx *state,
						  const uint8_t *in0,
						  const uint8_t *in1,
						  const uint8_t *in2,
						  const uint8_t *in3, size_t inlen) {
  mlk_shake128_absorb_once(&(*state)[0], in0, inlen);
  mlk_shake128_absorb_once(&(*state)[1], in1, inlen);
  mlk_shake128_absorb_once(&(*state)[2], in2, inlen);
  mlk_shake128_absorb_once(&(*state)[3], in3, inlen);
}

static MLK_INLINE void mlk_shake128x4_squeezeblocks(uint8_t *out0, uint8_t *out1,
						    uint8_t *out2, uint8_t *out3,
						    size_t nblocks,
						    mlk_shake128x4ctx *state) {
  mlk_shake128_squeezeblocks(out0, nblocks, &(*state)[0]);
  mlk_shake128_squeezeblocks(out1, nblocks, &(*state)[1]);
  mlk_shake128_squeezeblocks(out2, nblocks, &(*state)[2]);
  mlk_shake128_squeezeblocks(out3, nblocks, &(*state)[3]);
}

static MLK_INLINE void mlk_shake128x4_init(mlk_shake128x4ctx *state) {
  mlk_shake128_init(&(*state)[0]);
  mlk_shake128_init(&(*state)[1]);
  mlk_shake128_init(&(*state)[2]);
  mlk_shake128_init(&(*state)[3]);
}

static MLK_INLINE void mlk_shake128x4_release(mlk_shake128x4ctx *state) {
  mlk_shake128_release(&(*state)[0]);
  mlk_shake128_release(&(*state)[1]);
  mlk_shake128_release(&(*state)[2]);
  mlk_shake128_release(&(*state)[3]);
}

static MLK_INLINE void mlk_shake256x4(uint8_t *out0, uint8_t *out1, uint8_t *out2,
				      uint8_t *out3, size_t outlen, uint8_t *in0,
				      uint8_t *in1, uint8_t *in2, uint8_t *in3,
				      size_t inlen) {
  mlk_shake256(out0, outlen, in0, inlen);
  mlk_shake256(out1, outlen, in1, inlen);
  mlk_shake256(out2, outlen, in2, inlen);
  mlk_shake256(out3, outlen, in3, inlen);
}

#endif // MLK_AWSLC_FIPS202X4_GLUE_H
