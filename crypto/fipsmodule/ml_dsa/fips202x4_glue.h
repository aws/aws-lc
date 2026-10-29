// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

//
// This is a shim establishing the FIPS-202 API required by
// mldsa-native from the API exposed by AWS-LC.
//

#ifndef MLD_AWSLC_FIPS202X4_GLUE_H
#define MLD_AWSLC_FIPS202X4_GLUE_H

#include <stddef.h>
#include <stdint.h>

#include "fips202_glue.h"

// Use AWS-LC's existing KECCAK1600_CTX_x4 structure for SHAKE128 and SHAKE256.
#define mld_shake128x4ctx KECCAK1600_CTX_x4
#define mld_shake256x4ctx KECCAK1600_CTX_x4

static MLD_INLINE void mld_shake128x4_absorb_once(mld_shake128x4ctx *state,
						  const uint8_t *in0,
						  const uint8_t *in1,
						  const uint8_t *in2,
						  const uint8_t *in3, size_t inlen) {
  // Return code check can be omitted
  // since mldsa-native adheres to call discipline
  (void) SHAKE128_Absorb_once_x4(state, in0, in1, in2, in3, inlen);
}

static MLD_INLINE void mld_shake128x4_squeezeblocks(uint8_t *out0, uint8_t *out1,
						    uint8_t *out2, uint8_t *out3,
						    size_t nblocks,
						    mld_shake128x4ctx *state) {
  // Return code check can be omitted
  // since mldsa-native adheres to call discipline
  (void) SHAKE128_Squeezeblocks_x4(out0, out1, out2, out3, state, nblocks);
}

static MLD_INLINE void mld_shake128x4_init(mld_shake128x4ctx *state) {
  // Return code check can be omitted
  // since mldsa-native adheres to call discipline
  (void) SHAKE_Init_x4(state);
}

static MLD_INLINE void mld_shake128x4_release(mld_shake128x4ctx *state) {
  (void) state;
}

static MLD_INLINE void mld_shake256x4_absorb_once(mld_shake256x4ctx *state,
						  const uint8_t *in0,
						  const uint8_t *in1,
						  const uint8_t *in2,
						  const uint8_t *in3, size_t inlen) {
  // Return code check can be omitted
  // since mldsa-native adheres to call discipline
  (void) SHAKE256_Absorb_once_x4(state, in0, in1, in2, in3, inlen);
}

static MLD_INLINE void mld_shake256x4_squeezeblocks(uint8_t *out0, uint8_t *out1,
						    uint8_t *out2, uint8_t *out3,
						    size_t nblocks,
						    mld_shake256x4ctx *state) {
  // Return code check can be omitted
  // since mldsa-native adheres to call discipline
  (void) SHAKE256_Squeezeblocks_x4(out0, out1, out2, out3, state, nblocks);
}

static MLD_INLINE void mld_shake256x4_init(mld_shake256x4ctx *state) {
  // Return code check can be omitted
  // since mldsa-native adheres to call discipline
  (void) SHAKE_Init_x4(state);
}

static MLD_INLINE void mld_shake256x4_release(mld_shake256x4ctx *state) {
  (void) state;
}

static MLD_INLINE void mld_shake256x4(uint8_t *out0, uint8_t *out1, uint8_t *out2,
				      uint8_t *out3, size_t outlen, uint8_t *in0,
				      uint8_t *in1, uint8_t *in2, uint8_t *in3,
				      size_t inlen) {
  // Return code check can be omitted
  // since SHAKE256_x4 is documented not to fail for valid inputs.
  (void) SHAKE256_x4(in0, in1, in2, in3, inlen,
		     out0, out1, out2, out3, outlen);
}

#endif // MLD_AWSLC_FIPS202X4_GLUE_H
