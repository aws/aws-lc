/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLD_NATIVE_X86_64_SRC_ARITH_NATIVE_X86_64_H
#define MLD_NATIVE_X86_64_SRC_ARITH_NATIVE_X86_64_H
#include "../../../common.h"

#include "consts.h"

#define mld_ntt_avx2 MLD_NAMESPACE(ntt_avx2)
void mld_ntt_avx2(int32_t *r, const int32_t *qdata);

#define mld_invntt_avx2 MLD_NAMESPACE(invntt_avx2)
void mld_invntt_avx2(int32_t *r, const int32_t *qdata);

#define mld_nttunpack_avx2 MLD_NAMESPACE(nttunpack_avx2)
void mld_nttunpack_avx2(int32_t *r);

#define mld_pointwise_avx2 MLD_NAMESPACE(pointwise_avx2)
void mld_pointwise_avx2(int32_t *c, const int32_t *a, const int32_t *b,
                        const int32_t *qdata);

#define mld_pointwise_acc_l4_avx2 MLD_NAMESPACE(pointwise_acc_l4_avx2)
void mld_pointwise_acc_l4_avx2(int32_t c[MLDSA_N], const int32_t a[4][MLDSA_N],
                               const int32_t b[4][MLDSA_N],
                               const int32_t *qdata);

#define mld_pointwise_acc_l5_avx2 MLD_NAMESPACE(pointwise_acc_l5_avx2)
void mld_pointwise_acc_l5_avx2(int32_t c[MLDSA_N], const int32_t a[5][MLDSA_N],
                               const int32_t b[5][MLDSA_N],
                               const int32_t *qdata);

#define mld_pointwise_acc_l7_avx2 MLD_NAMESPACE(pointwise_acc_l7_avx2)
void mld_pointwise_acc_l7_avx2(int32_t c[MLDSA_N], const int32_t a[7][MLDSA_N],
                               const int32_t b[7][MLDSA_N],
                               const int32_t *qdata);

#endif /* !MLD_NATIVE_X86_64_SRC_ARITH_NATIVE_X86_64_H */
