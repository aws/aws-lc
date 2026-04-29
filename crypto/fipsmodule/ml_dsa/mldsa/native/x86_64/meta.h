/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLD_NATIVE_X86_64_META_H
#define MLD_NATIVE_X86_64_META_H

/* Identifier for this backend so that source and assembly files
 * in the build can be appropriately guarded. */
#define MLD_ARITH_BACKEND_X86_64_DEFAULT

#define MLD_USE_NATIVE_NTT_CUSTOM_ORDER
#define MLD_USE_NATIVE_NTT
#define MLD_USE_NATIVE_INTT
#define MLD_USE_NATIVE_POINTWISE_MONTGOMERY
#define MLD_USE_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_L4
#define MLD_USE_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_L5
#define MLD_USE_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_L7

#if !defined(__ASSEMBLER__)
#include "../../common.h"
#include "../api.h"
#include "src/arith_native_x86_64.h"

static MLD_INLINE void mld_poly_permute_bitrev_to_custom(int32_t data[MLDSA_N])
{
  if (mld_sys_check_capability(MLD_SYS_CAP_AVX2))
  {
    mld_nttunpack_avx2(data);
  }
}

static MLD_INLINE int mld_ntt_native(int32_t data[MLDSA_N])
{
  if (!mld_sys_check_capability(MLD_SYS_CAP_AVX2))
  {
    return MLD_NATIVE_FUNC_FALLBACK;
  }

  mld_ntt_avx2(data, mld_qdata);
  return MLD_NATIVE_FUNC_SUCCESS;
}
static MLD_INLINE int mld_intt_native(int32_t data[MLDSA_N])
{
  if (!mld_sys_check_capability(MLD_SYS_CAP_AVX2))
  {
    return MLD_NATIVE_FUNC_FALLBACK;
  }
  mld_invntt_avx2(data, mld_qdata);
  return MLD_NATIVE_FUNC_SUCCESS;
}

static MLD_INLINE int mld_poly_pointwise_montgomery_native(
    int32_t c[MLDSA_N], const int32_t a[MLDSA_N], const int32_t b[MLDSA_N])
{
  if (!mld_sys_check_capability(MLD_SYS_CAP_AVX2))
  {
    return MLD_NATIVE_FUNC_FALLBACK;
  }
  mld_pointwise_avx2(c, a, b, mld_qdata);
  return MLD_NATIVE_FUNC_SUCCESS;
}

static MLD_INLINE int mld_polyvecl_pointwise_acc_montgomery_l4_native(
    int32_t w[MLDSA_N], const int32_t u[4][MLDSA_N],
    const int32_t v[4][MLDSA_N])
{
  if (!mld_sys_check_capability(MLD_SYS_CAP_AVX2))
  {
    return MLD_NATIVE_FUNC_FALLBACK;
  }
  mld_pointwise_acc_l4_avx2(w, u, v, mld_qdata);
  return MLD_NATIVE_FUNC_SUCCESS;
}

static MLD_INLINE int mld_polyvecl_pointwise_acc_montgomery_l5_native(
    int32_t w[MLDSA_N], const int32_t u[5][MLDSA_N],
    const int32_t v[5][MLDSA_N])
{
  if (!mld_sys_check_capability(MLD_SYS_CAP_AVX2))
  {
    return MLD_NATIVE_FUNC_FALLBACK;
  }
  mld_pointwise_acc_l5_avx2(w, u, v, mld_qdata);
  return MLD_NATIVE_FUNC_SUCCESS;
}

static MLD_INLINE int mld_polyvecl_pointwise_acc_montgomery_l7_native(
    int32_t w[MLDSA_N], const int32_t u[7][MLDSA_N],
    const int32_t v[7][MLDSA_N])
{
  if (!mld_sys_check_capability(MLD_SYS_CAP_AVX2))
  {
    return MLD_NATIVE_FUNC_FALLBACK;
  }
  mld_pointwise_acc_l7_avx2(w, u, v, mld_qdata);
  return MLD_NATIVE_FUNC_SUCCESS;
}

#endif /* !__ASSEMBLER__ */

#endif /* !MLD_NATIVE_X86_64_META_H */
