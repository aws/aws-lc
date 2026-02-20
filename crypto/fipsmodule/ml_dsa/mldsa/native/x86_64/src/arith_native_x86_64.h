/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLD_ARITH_NATIVE_X86_64_H
#define MLD_ARITH_NATIVE_X86_64_H

#include <stdint.h>
#include "../../../params.h"
#include "consts.h"

/* NTT forward transformation */
#define mld_ntt_avx2 MLD_NAMESPACE(ntt_avx2)
void mld_ntt_avx2(int32_t r[MLDSA_N], const int32_t *qdata);

/* Inverse NTT transformation */
#define mld_invntt_avx2 MLD_NAMESPACE(invntt_avx2)
void mld_invntt_avx2(int32_t r[MLDSA_N], const int32_t *qdata);

/* NTT unpack - permute from bitreversed to custom order */
#define mld_nttunpack_avx2 MLD_NAMESPACE(nttunpack_avx2)
void mld_nttunpack_avx2(int32_t *r);

#endif /* MLD_ARITH_NATIVE_X86_64_H */
