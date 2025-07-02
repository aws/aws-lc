// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef ML_KEM_AARCH64_BACKEND_H
#define ML_KEM_AARCH64_BACKEND_H

#include "../mlkem/common.h"

#define MLK_USE_NATIVE_NTT
#define MLK_USE_NATIVE_INTT
#define MLK_USE_NATIVE_POLY_REDUCE
#define MLK_USE_NATIVE_POLY_TOMONT
#define MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE
#define MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
#define MLK_USE_NATIVE_POLY_TOBYTES
#define MLK_USE_NATIVE_REJ_UNIFORM

extern const int16_t mlk_aarch64_ntt_zetas_layer12345[];
extern const int16_t mlk_aarch64_ntt_zetas_layer67[];
extern const int16_t mlk_aarch64_invntt_zetas_layer12345[];
extern const int16_t mlk_aarch64_invntt_zetas_layer67[];
extern const uint8_t mlk_rej_uniform_table[];
extern const int16_t mlk_aarch64_zetas_mulcache_native[];
extern const int16_t mlk_aarch64_zetas_mulcache_twisted_native[];

#include "../../../../third_party/s2n-bignum/s2n-bignum_aws-lc.h"

static MLK_INLINE void mlk_ntt_native(int16_t data[MLKEM_N]) {
    mlkem_ntt(data, mlk_aarch64_ntt_zetas_layer12345, mlk_aarch64_ntt_zetas_layer67);
}

static MLK_INLINE void mlk_intt_native(int16_t data[MLKEM_N]) {
    mlkem_intt(data, mlk_aarch64_invntt_zetas_layer12345, mlk_aarch64_invntt_zetas_layer67);
}

static MLK_INLINE void mlk_poly_reduce_native(int16_t data[MLKEM_N]) {
    mlkem_poly_reduce(data);
}

static MLK_INLINE void mlk_poly_tomont_native(int16_t data[MLKEM_N]) {
    mlkem_poly_tomont(data);
}

static MLK_INLINE void mlk_poly_mulcache_compute_native(int16_t x[MLKEM_N / 2], const int16_t y[MLKEM_N]) {
    mlkem_mulcache_compute(x, y, mlk_aarch64_zetas_mulcache_native,
	mlk_aarch64_zetas_mulcache_twisted_native);
}

static MLK_INLINE void mlk_polyvec_basemul_acc_montgomery_cached_k2_native(
    int16_t r[MLKEM_N], const int16_t a[2 * MLKEM_N],
    const int16_t b[2 * MLKEM_N], const int16_t b_cache[2 * (MLKEM_N / 2)]) {
  mlkem_basemul_k2(r, a, b, b_cache);
}

static MLK_INLINE void mlk_polyvec_basemul_acc_montgomery_cached_k3_native(
    int16_t r[MLKEM_N], const int16_t a[3 * MLKEM_N],
    const int16_t b[3 * MLKEM_N], const int16_t b_cache[3 * (MLKEM_N / 2)]) {
  mlkem_basemul_k3(r, a, b, b_cache);
}

static MLK_INLINE void mlk_polyvec_basemul_acc_montgomery_cached_k4_native(
    int16_t r[MLKEM_N], const int16_t a[4 * MLKEM_N],
    const int16_t b[4 * MLKEM_N], const int16_t b_cache[4 * (MLKEM_N / 2)]) {
  mlkem_basemul_k4(r, a, b, b_cache);
}

static MLK_INLINE void mlk_poly_tobytes_native(uint8_t r[MLKEM_POLYBYTES],
					       const int16_t a[MLKEM_N]) {
  mlkem_poly_tobytes(r, a);
}

static MLK_INLINE int mlk_rej_uniform_native(int16_t *r, unsigned len,
					     const uint8_t *buf,
					     unsigned buflen) {
  if (len != MLKEM_N || buflen % 24 != 0) {
      return -1;
  }
  return (int) mlkem_rej_uniform_VARIABLE_TIME(r, buf, buflen, mlk_rej_uniform_table);
}

#endif /* ML_KEM_AARCH64_BACKEND_H */
