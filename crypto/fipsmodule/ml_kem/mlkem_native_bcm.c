/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          Do not modify it directly.
 */

/*
 * Monolithic compilation unit bundling all compilation units within
 * mlkem-native
 */

/* If parts of the mlkem-native source tree are not used,
 * consider reducing this header via `unifdef`.
 *
 * Example:
 * ```bash
 * unifdef -UMLK_MONOBUILD_WITH_NATIVE_ARITH mlkem_native_monobuild.c
 * ```
 */

#include "mlkem/sys.h"

#include "mlkem/compress.c"
#include "mlkem/debug.c"
#include "mlkem/indcpa.c"
#include "mlkem/kem.c"
#include "mlkem/poly.c"
#include "mlkem/poly_k.c"
#include "mlkem/sampling.c"
#include "mlkem/verify.c"
#include "mlkem/zetas.c"




/*
 * Undefine macros from MLKEM_K-specific files
 */
/* mlkem/common.h */
#undef MLK_ARITH_BACKEND_NAME
#undef MLK_ASM_FN_SYMBOL
#undef MLK_ASM_NAMESPACE
#undef MLK_COMMON_H
#undef MLK_EMPTY_CU
#undef MLK_EXTERNAL_API
#undef MLK_FIPS202X4_HEADER_FILE
#undef MLK_FIPS202_BACKEND_NAME
#undef MLK_FIPS202_HEADER_FILE
#undef MLK_INTERNAL_API
#undef MLK_MAKE_NAMESPACE
#undef MLK_MAKE_NAMESPACE_
#undef MLK_MAKE_NAMESPACE_K
#undef MLK_MAKE_NAMESPACE_K_
#undef MLK_NAMESPACE
#undef MLK_NAMESPACE_K
#undef MLK_PREFIX_UNDERSCORE
#undef MLK_PREFIX_UNDERSCORE_
/* mlkem/config.h */
#undef MLKEM_K
#undef MLK_ARITH_BACKEND_FILE
#undef MLK_CONFIG_H
#undef MLK_DEFAULT_NAMESPACE_PREFIX
#undef MLK_FIPS202_BACKEND_FILE
#undef MLK_NAMESPACE_PREFIX
/* mlkem/indcpa.h */
#undef MLK_INDCPA_H
#undef gen_matrix
#undef indcpa_dec
#undef indcpa_enc
#undef indcpa_keypair_derand
/* mlkem/kem.h */
#undef MLK_KEM_H
#undef crypto_kem_dec
#undef crypto_kem_enc
#undef crypto_kem_enc_derand
#undef crypto_kem_keypair
#undef crypto_kem_keypair_derand
/* mlkem/mlkem_native.h */
#undef CRYPTO_BYTES
#undef CRYPTO_CIPHERTEXTBYTES
#undef CRYPTO_PUBLICKEYBYTES
#undef CRYPTO_SECRETKEYBYTES
#undef CRYPTO_SYMBYTES
#undef MLKEM1024_BYTES
#undef MLKEM1024_CIPHERTEXTBYTES
#undef MLKEM1024_PUBLICKEYBYTES
#undef MLKEM1024_SECRETKEYBYTES
#undef MLKEM1024_SYMBYTES
#undef MLKEM512_BYTES
#undef MLKEM512_CIPHERTEXTBYTES
#undef MLKEM512_PUBLICKEYBYTES
#undef MLKEM512_SECRETKEYBYTES
#undef MLKEM512_SYMBYTES
#undef MLKEM768_BYTES
#undef MLKEM768_CIPHERTEXTBYTES
#undef MLKEM768_PUBLICKEYBYTES
#undef MLKEM768_SECRETKEYBYTES
#undef MLKEM768_SYMBYTES
#undef MLKEM_BYTES
#undef MLKEM_CIPHERTEXTBYTES
#undef MLKEM_CIPHERTEXTBYTES_
#undef MLKEM_PUBLICKEYBYTES
#undef MLKEM_PUBLICKEYBYTES_
#undef MLKEM_SECRETKEYBYTES
#undef MLKEM_SECRETKEYBYTES_
#undef MLKEM_SYMBYTES
#undef MLK_BUILD_INFO_CONCAT2
#undef MLK_BUILD_INFO_CONCAT2_
#undef MLK_BUILD_INFO_CONCAT3
#undef MLK_BUILD_INFO_CONCAT3_
#undef MLK_BUILD_INFO_LVL
#undef MLK_BUILD_INFO_NAMESPACE
#undef MLK_H
#undef MLK_MUST_CHECK_RETURN_VALUE
#undef crypto_kem_dec
#undef crypto_kem_enc
#undef crypto_kem_enc_derand
#undef crypto_kem_keypair
#undef crypto_kem_keypair_derand
/* mlkem/params.h */
#undef MLKEM_DU
#undef MLKEM_DV
#undef MLKEM_ETA1
#undef MLKEM_ETA2
#undef MLKEM_INDCCA_CIPHERTEXTBYTES
#undef MLKEM_INDCCA_PUBLICKEYBYTES
#undef MLKEM_INDCCA_SECRETKEYBYTES
#undef MLKEM_INDCPA_BYTES
#undef MLKEM_INDCPA_MSGBYTES
#undef MLKEM_INDCPA_PUBLICKEYBYTES
#undef MLKEM_INDCPA_SECRETKEYBYTES
#undef MLKEM_LVL
#undef MLKEM_N
#undef MLKEM_POLYBYTES
#undef MLKEM_POLYCOMPRESSEDBYTES_D10
#undef MLKEM_POLYCOMPRESSEDBYTES_D11
#undef MLKEM_POLYCOMPRESSEDBYTES_D4
#undef MLKEM_POLYCOMPRESSEDBYTES_D5
#undef MLKEM_POLYCOMPRESSEDBYTES_DU
#undef MLKEM_POLYCOMPRESSEDBYTES_DV
#undef MLKEM_POLYVECBYTES
#undef MLKEM_POLYVECCOMPRESSEDBYTES_DU
#undef MLKEM_Q
#undef MLKEM_Q_HALF
#undef MLKEM_SSBYTES
#undef MLKEM_SYMBYTES
#undef MLKEM_UINT12_LIMIT
#undef MLK_PARAMS_H
/* mlkem/poly_k.h */
#undef MLK_POLY_K_H
#undef poly_compress_du
#undef poly_compress_dv
#undef poly_decompress_du
#undef poly_decompress_dv
#undef poly_getnoise_eta1122_4x
#undef poly_getnoise_eta1_4x
#undef poly_getnoise_eta2
#undef poly_getnoise_eta2_4x
#undef polyvec
#undef polyvec_add
#undef polyvec_basemul_acc_montgomery_cached
#undef polyvec_compress_du
#undef polyvec_decompress_du
#undef polyvec_frombytes
#undef polyvec_invntt_tomont
#undef polyvec_mulcache
#undef polyvec_mulcache_compute
#undef polyvec_ntt
#undef polyvec_reduce
#undef polyvec_tobytes
#undef polyvec_tomont
/* mlkem/sys.h */
#undef MLK_ALIGN
#undef MLK_ALWAYS_INLINE
#undef MLK_CET_ENDBR
#undef MLK_CT_TESTING_DECLASSIFY
#undef MLK_CT_TESTING_SECRET
#undef MLK_DEFAULT_ALIGN
#undef MLK_HAVE_INLINE_ASM
#undef MLK_INLINE
#undef MLK_MUST_CHECK_RETURN_VALUE
#undef MLK_RESTRICT
#undef MLK_SYS_AARCH64
#undef MLK_SYS_AARCH64_EB
#undef MLK_SYS_BIG_ENDIAN
#undef MLK_SYS_H
#undef MLK_SYS_LITTLE_ENDIAN
#undef MLK_SYS_WINDOWS
#undef MLK_SYS_X86_64
#undef MLK_SYS_X86_64_AVX2

#if !defined(MLK_MONOBUILD_KEEP_SHARED_HEADERS)
/*
 * Undefine macros from MLKEM_K-generic files
 */
/* mlkem/arith_backend.h */
#undef MLK_ARITH_BACKEND_H
/* mlkem/compress.h */
#undef MLK_COMPRESS_H
#undef poly_compress_d10
#undef poly_compress_d11
#undef poly_compress_d4
#undef poly_compress_d5
#undef poly_decompress_d10
#undef poly_decompress_d11
#undef poly_decompress_d4
#undef poly_decompress_d5
#undef poly_frombytes
#undef poly_frommsg
#undef poly_tobytes
#undef poly_tomsg
#undef scalar_compress_d1
#undef scalar_compress_d10
#undef scalar_compress_d11
#undef scalar_compress_d4
#undef scalar_compress_d5
#undef scalar_decompress_d10
#undef scalar_decompress_d11
#undef scalar_decompress_d4
#undef scalar_decompress_d5
/* mlkem/debug.h */
#undef MLK_DEBUG_H
#undef debug_assert
#undef debug_assert_abs_bound
#undef debug_assert_abs_bound_2d
#undef debug_assert_bound
#undef debug_assert_bound_2d
#undef mlkem_debug_assert
#undef mlkem_debug_check_bounds
/* mlkem/poly.h */
#undef MLK_INVNTT_BOUND
#undef MLK_NTT_BOUND
#undef MLK_POLY_H
#undef cast_uint16_to_int16
#undef montgomery_reduce
#undef poly
#undef poly_add
#undef poly_invntt_tomont
#undef poly_mulcache
#undef poly_mulcache_compute
#undef poly_ntt
#undef poly_reduce
#undef poly_sub
#undef poly_tomont
#undef zetas
/* mlkem/randombytes.h */
#undef MLK_RANDOMBYTES_H
/* mlkem/sampling.h */
#undef MLK_SAMPLING_H
#undef poly_cbd2
#undef poly_cbd3
#undef poly_rej_uniform
#undef poly_rej_uniform_x4
/* mlkem/symmetric.h */
#undef MLK_SYMMETRIC_H
#undef XOF_RATE
#undef hash_g
#undef hash_h
#undef hash_j
#undef prf_eta
#undef prf_eta1
#undef prf_eta1_x4
#undef prf_eta2
#undef xof_absorb
#undef xof_ctx
#undef xof_init
#undef xof_release
#undef xof_squeezeblocks
#undef xof_x4_absorb
#undef xof_x4_ctx
#undef xof_x4_init
#undef xof_x4_release
#undef xof_x4_squeezeblocks
/* mlkem/verify.h */
#undef MLK_USE_ASM_VALUE_BARRIER
#undef MLK_VERIFY_H
#undef ct_cmask_neg_i16
#undef ct_cmask_nonzero_u16
#undef ct_cmask_nonzero_u8
#undef ct_cmov_zero
#undef ct_memcmp
#undef ct_opt_blocker_u64
#undef ct_sel_int16
#undef ct_sel_uint8
#undef ct_zeroize
#undef value_barrier_i32
#undef value_barrier_u32
#undef value_barrier_u8
/* mlkem/cbmc.h */
#undef MLK_CBMC_H
#undef __contract__
#undef __loop__


#endif /* MLK_MONOBUILD_KEEP_SHARED_HEADERS */
