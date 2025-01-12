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

/******************************************************************************
 *
 * Single compilation unit (SCU) for fixed-level build of mlkem-native
 *
 * This compilation unit bundles together all source files for a build
 * of mlkem-native for a fixed security level (MLKEM-512/768/1024).
 *
 * # API
 *
 * The API exposed by this file is described in mlkem_native.h.
 *
 * # Multilevel build
 *
 * If you want an SCU build of mlkem-native with support for multiple security
 * levels, you need to include this file multiple times, and set
 * MLK_CONFIG_MULTILEVEL_WITH_SHARED and MLK_CONFIG_MULTILEVEL_NO_SHARED
 * appropriately. This is exemplified in examples/monolithic_build_multilevel.
 *
 * # Configuration
 *
 * - MLK_CONFIG_MONOBUILD_CUSTOM_FIPS202
 *   Set this option if you use a custom FIPS202 implementation.
 *
 * - MLK_CONFIG_MONOBUILD_WITH_NATIVE_ARITH
 *   Set this option if you want to include the native arithmetic backends
 *   in your build.
 *
 * - MLK_CONFIG_MONOBUILD_WITH_NATIVE_FIPS202
 *   Set this option if you want to include the native FIPS202 backends
 *   in your build.
 *
 * - MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS
 *   Set this option if you want to keep the directives defined in
 *   level-independent headers. This is needed for a multilevel build.
 */

/* If parts of the mlkem-native source tree are not used,
 * consider reducing this header via `unifdef`.
 *
 * Example:
 * ```bash
 * unifdef -UMLK_CONFIG_MONOBUILD_WITH_NATIVE_ARITH mlkem_native_monobuild.c
 * ```
 */

#include "sys.h"

#include "compress.c"
#include "debug.c"
#include "indcpa.c"
#include "kem.c"
#include "poly.c"
#include "poly_k.c"
#include "sampling.c"
#include "verify.c"




/*
 * Undefine macros from MLK_CONFIG_PARAMETER_SET-specific files
 */
/* mlkem/common.h */
#undef MLK_ADD_LEVEL
#undef MLK_ASM_FN_SYMBOL
#undef MLK_ASM_NAMESPACE
#undef MLK_COMMON_H
#undef MLK_CONCAT
#undef MLK_CONCAT_
#undef MLK_CONFIG_API_NAMESPACE_PREFIX
#undef MLK_CONFIG_API_PARAMETER_SET
#undef MLK_EMPTY_CU
#undef MLK_EXTERNAL_API
#undef MLK_FIPS202X4_HEADER_FILE
#undef MLK_FIPS202_HEADER_FILE
#undef MLK_INTERNAL_API
#undef MLK_MULTILEVEL_BUILD
#undef MLK_NAMESPACE
#undef MLK_NAMESPACE_K
/* mlkem/indcpa.h */
#undef MLK_INDCPA_H
#undef mlk_gen_matrix
#undef mlk_indcpa_dec
#undef mlk_indcpa_enc
#undef mlk_indcpa_keypair_derand
/* mlkem/kem.h */
#undef MLK_CONFIG_API_NO_SUPERCOP
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
#undef MLK_API_CONCAT
#undef MLK_API_CONCAT_
#undef MLK_API_CONCAT_UNDERSCORE
#undef MLK_API_MUST_CHECK_RETURN_VALUE
#undef MLK_API_NAMESPACE
#undef MLK_H
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
#undef MLKEM_K
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
#undef mlk_poly_compress_du
#undef mlk_poly_compress_dv
#undef mlk_poly_decompress_du
#undef mlk_poly_decompress_dv
#undef mlk_poly_getnoise_eta1122_4x
#undef mlk_poly_getnoise_eta1_4x
#undef mlk_poly_getnoise_eta2
#undef mlk_poly_getnoise_eta2_4x
#undef mlk_polymat
#undef mlk_polyvec
#undef mlk_polyvec_add
#undef mlk_polyvec_basemul_acc_montgomery_cached
#undef mlk_polyvec_compress_du
#undef mlk_polyvec_decompress_du
#undef mlk_polyvec_frombytes
#undef mlk_polyvec_invntt_tomont
#undef mlk_polyvec_mulcache
#undef mlk_polyvec_mulcache_compute
#undef mlk_polyvec_ntt
#undef mlk_polyvec_reduce
#undef mlk_polyvec_tobytes
#undef mlk_polyvec_tomont
/* mlkem/sys.h */
#undef MLK_ALIGN
#undef MLK_ALIGN_UP
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

#if !defined(MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS)
/*
 * Undefine macros from MLK_CONFIG_PARAMETER_SET-generic files
 */
/* mlkem/compress.h */
#undef MLK_COMPRESS_H
#undef mlk_poly_compress_d10
#undef mlk_poly_compress_d11
#undef mlk_poly_compress_d4
#undef mlk_poly_compress_d5
#undef mlk_poly_decompress_d10
#undef mlk_poly_decompress_d11
#undef mlk_poly_decompress_d4
#undef mlk_poly_decompress_d5
#undef mlk_poly_frombytes
#undef mlk_poly_frommsg
#undef mlk_poly_tobytes
#undef mlk_poly_tomsg
/* mlkem/debug.h */
#undef MLK_DEBUG_H
#undef mlk_assert
#undef mlk_assert_abs_bound
#undef mlk_assert_abs_bound_2d
#undef mlk_assert_bound
#undef mlk_assert_bound_2d
#undef mlk_debug_check_assert
#undef mlk_debug_check_bounds
/* mlkem/poly.h */
#undef MLK_INVNTT_BOUND
#undef MLK_NTT_BOUND
#undef MLK_POLY_H
#undef mlk_poly_add
#undef mlk_poly_invntt_tomont
#undef mlk_poly_mulcache_compute
#undef mlk_poly_ntt
#undef mlk_poly_reduce
#undef mlk_poly_sub
#undef mlk_poly_tomont
/* mlkem/randombytes.h */
#undef MLK_RANDOMBYTES_H
/* mlkem/sampling.h */
#undef MLK_SAMPLING_H
#undef mlk_poly_cbd2
#undef mlk_poly_cbd3
#undef mlk_poly_rej_uniform
#undef mlk_poly_rej_uniform_x4
/* mlkem/symmetric.h */
#undef MLK_SYMMETRIC_H
#undef MLK_XOF_RATE
#undef mlk_hash_g
#undef mlk_hash_h
#undef mlk_hash_j
#undef mlk_prf_eta
#undef mlk_prf_eta1
#undef mlk_prf_eta1_x4
#undef mlk_prf_eta2
#undef mlk_xof_absorb
#undef mlk_xof_ctx
#undef mlk_xof_init
#undef mlk_xof_release
#undef mlk_xof_squeezeblocks
#undef mlk_xof_x4_absorb
#undef mlk_xof_x4_ctx
#undef mlk_xof_x4_init
#undef mlk_xof_x4_release
#undef mlk_xof_x4_squeezeblocks
/* mlkem/verify.h */
#undef MLK_USE_ASM_VALUE_BARRIER
#undef MLK_VERIFY_H
#undef mlk_ct_opt_blocker_u64
/* mlkem/cbmc.h */
#undef MLK_CBMC_H
#undef __contract__
#undef __loop__


#endif /* !MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS */
