/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <stdint.h>
#include <string.h>

#include "arith_backend.h"
#include "compress.h"
#include "debug.h"
#include "poly_k.h"
#include "sampling.h"
#include "symmetric.h"

/* Static namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define poly_cbd_eta1 MLK_NAMESPACE_K(poly_cbd_eta1)
#define poly_cbd_eta2 MLK_NAMESPACE_K(poly_cbd_eta2)
/* End of static namespacing */

MLK_INTERNAL_API
void polyvec_compress_du(uint8_t r[MLKEM_POLYVECCOMPRESSEDBYTES_DU],
                         const polyvec *a)
{
  unsigned i;
  debug_assert_bound_2d(a, MLKEM_K, MLKEM_N, 0, MLKEM_Q);

  for (i = 0; i < MLKEM_K; i++)
  {
    poly_compress_du(r + i * MLKEM_POLYCOMPRESSEDBYTES_DU, &a->vec[i]);
  }
}

MLK_INTERNAL_API
void polyvec_decompress_du(polyvec *r,
                           const uint8_t a[MLKEM_POLYVECCOMPRESSEDBYTES_DU])
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_decompress_du(&r->vec[i], a + i * MLKEM_POLYCOMPRESSEDBYTES_DU);
  }

  debug_assert_bound_2d(r, MLKEM_K, MLKEM_N, 0, MLKEM_Q);
}

MLK_INTERNAL_API
void polyvec_tobytes(uint8_t r[MLKEM_POLYVECBYTES], const polyvec *a)
{
  unsigned i;
  debug_assert_bound_2d(a, MLKEM_K, MLKEM_N, 0, MLKEM_Q);

  for (i = 0; i < MLKEM_K; i++)
  {
    poly_tobytes(r + i * MLKEM_POLYBYTES, &a->vec[i]);
  }
}

MLK_INTERNAL_API
void polyvec_frombytes(polyvec *r, const uint8_t a[MLKEM_POLYVECBYTES])
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_frombytes(&r->vec[i], a + i * MLKEM_POLYBYTES);
  }

  debug_assert_bound_2d(r, MLKEM_K, MLKEM_N, 0, MLKEM_UINT12_LIMIT);
}

MLK_INTERNAL_API
void polyvec_ntt(polyvec *r)
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_ntt(&r->vec[i]);
  }

  debug_assert_abs_bound_2d(r, MLKEM_K, MLKEM_N, MLK_NTT_BOUND);
}

MLK_INTERNAL_API
void polyvec_invntt_tomont(polyvec *r)
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_invntt_tomont(&r->vec[i]);
  }

  debug_assert_abs_bound_2d(r, MLKEM_K, MLKEM_N, MLK_INVNTT_BOUND);
}

#if !defined(MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
MLK_INTERNAL_API
void polyvec_basemul_acc_montgomery_cached(poly *r, const polyvec *a,
                                           const polyvec *b,
                                           const polyvec_mulcache *b_cache)
{
  unsigned i;
  debug_assert_bound_2d(a, MLKEM_K, MLKEM_N, 0, MLKEM_UINT12_LIMIT);
  for (i = 0; i < MLKEM_N / 2; i++)
  __loop__(invariant(i <= MLKEM_N / 2))
  {
    unsigned k;
    int32_t t[2] = {0};
    for (k = 0; k < MLKEM_K; k++)
    __loop__(
      invariant(k <= MLKEM_K &&
         t[0] <=    (int32_t) k * 2 * MLKEM_UINT12_LIMIT * 32768  &&
         t[0] >= - ((int32_t) k * 2 * MLKEM_UINT12_LIMIT * 32768) &&
         t[1] <=   ((int32_t) k * 2 * MLKEM_UINT12_LIMIT * 32768) &&
         t[1] >= - ((int32_t) k * 2 * MLKEM_UINT12_LIMIT * 32768)))
    {
      t[0] += (int32_t)a->vec[k].coeffs[2 * i + 1] * b_cache->vec[k].coeffs[i];
      t[0] += (int32_t)a->vec[k].coeffs[2 * i] * b->vec[k].coeffs[2 * i];
      t[1] += (int32_t)a->vec[k].coeffs[2 * i] * b->vec[k].coeffs[2 * i + 1];
      t[1] += (int32_t)a->vec[k].coeffs[2 * i + 1] * b->vec[k].coeffs[2 * i];
    }
    r->coeffs[2 * i + 0] = montgomery_reduce(t[0]);
    r->coeffs[2 * i + 1] = montgomery_reduce(t[1]);
  }
}

#else /* !MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED */
MLK_INTERNAL_API
void polyvec_basemul_acc_montgomery_cached(poly *r, const polyvec *a,
                                           const polyvec *b,
                                           const polyvec_mulcache *b_cache)
{
  debug_assert_bound_2d(a, MLKEM_K, MLKEM_N, 0, MLKEM_UINT12_LIMIT);
  /* Omitting bounds assertion for cache since native implementations may
   * decide not to use a mulcache. Note that the C backend implementation
   * of poly_basemul_montgomery_cached() does still include the check. */
#if MLKEM_K == 2
  polyvec_basemul_acc_montgomery_cached_k2_native(r->coeffs, (const int16_t *)a,
                                                  (const int16_t *)b,
                                                  (const int16_t *)b_cache);
#elif MLKEM_K == 3
  polyvec_basemul_acc_montgomery_cached_k3_native(r->coeffs, (const int16_t *)a,
                                                  (const int16_t *)b,
                                                  (const int16_t *)b_cache);
#elif MLKEM_K == 4
  polyvec_basemul_acc_montgomery_cached_k4_native(r->coeffs, (const int16_t *)a,
                                                  (const int16_t *)b,
                                                  (const int16_t *)b_cache);
#endif
}
#endif /* MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED */

MLK_INTERNAL_API
void polyvec_mulcache_compute(polyvec_mulcache *x, const polyvec *a)
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_mulcache_compute(&x->vec[i], &a->vec[i]);
  }
}

MLK_INTERNAL_API
void polyvec_reduce(polyvec *r)
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_reduce(&r->vec[i]);
  }

  debug_assert_bound_2d(r, MLKEM_K, MLKEM_N, 0, MLKEM_Q);
}

MLK_INTERNAL_API
void polyvec_add(polyvec *r, const polyvec *b)
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_add(&r->vec[i], &b->vec[i]);
  }
}

MLK_INTERNAL_API
void polyvec_tomont(polyvec *r)
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_tomont(&r->vec[i]);
  }

  debug_assert_abs_bound_2d(r, MLKEM_K, MLKEM_N, MLKEM_Q);
}


/*************************************************
 * Name:        poly_cbd_eta1
 *
 * Description: Given an array of uniformly random bytes, compute
 *              polynomial with coefficients distributed according to
 *              a centered binomial distribution with parameter MLKEM_ETA1.
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *buf: pointer to input byte array
 **************************************************/
static MLK_INLINE void poly_cbd_eta1(
    poly *r, const uint8_t buf[MLKEM_ETA1 * MLKEM_N / 4])
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  requires(memory_no_alias(buf, MLKEM_ETA1 * MLKEM_N / 4))
  assigns(memory_slice(r, sizeof(poly)))
  ensures(array_abs_bound(r->coeffs, 0, MLKEM_N, MLKEM_ETA1 + 1))
)
{
#if MLKEM_ETA1 == 2
  poly_cbd2(r, buf);
#elif MLKEM_ETA1 == 3
  poly_cbd3(r, buf);
#else
#error "Invalid value of MLKEM_ETA1"
#endif
}

MLK_INTERNAL_API
void poly_getnoise_eta1_4x(poly *r0, poly *r1, poly *r2, poly *r3,
                           const uint8_t seed[MLKEM_SYMBYTES], uint8_t nonce0,
                           uint8_t nonce1, uint8_t nonce2, uint8_t nonce3)
{
  MLK_ALIGN uint8_t buf0[MLKEM_ETA1 * MLKEM_N / 4];
  MLK_ALIGN uint8_t buf1[MLKEM_ETA1 * MLKEM_N / 4];
  MLK_ALIGN uint8_t buf2[MLKEM_ETA1 * MLKEM_N / 4];
  MLK_ALIGN uint8_t buf3[MLKEM_ETA1 * MLKEM_N / 4];
  MLK_ALIGN uint8_t extkey0[MLKEM_SYMBYTES + 1];
  MLK_ALIGN uint8_t extkey1[MLKEM_SYMBYTES + 1];
  MLK_ALIGN uint8_t extkey2[MLKEM_SYMBYTES + 1];
  MLK_ALIGN uint8_t extkey3[MLKEM_SYMBYTES + 1];
  memcpy(extkey0, seed, MLKEM_SYMBYTES);
  memcpy(extkey1, seed, MLKEM_SYMBYTES);
  memcpy(extkey2, seed, MLKEM_SYMBYTES);
  memcpy(extkey3, seed, MLKEM_SYMBYTES);
  extkey0[MLKEM_SYMBYTES] = nonce0;
  extkey1[MLKEM_SYMBYTES] = nonce1;
  extkey2[MLKEM_SYMBYTES] = nonce2;
  extkey3[MLKEM_SYMBYTES] = nonce3;
  prf_eta1_x4(buf0, buf1, buf2, buf3, extkey0, extkey1, extkey2, extkey3);
  poly_cbd_eta1(r0, buf0);
  poly_cbd_eta1(r1, buf1);
  poly_cbd_eta1(r2, buf2);
  poly_cbd_eta1(r3, buf3);

  debug_assert_abs_bound(r0, MLKEM_N, MLKEM_ETA1 + 1);
  debug_assert_abs_bound(r1, MLKEM_N, MLKEM_ETA1 + 1);
  debug_assert_abs_bound(r2, MLKEM_N, MLKEM_ETA1 + 1);
  debug_assert_abs_bound(r3, MLKEM_N, MLKEM_ETA1 + 1);

  /* FIPS 203. Section 3.3 Destruction of intermediate values. */
  ct_zeroize(buf0, sizeof(buf0));
  ct_zeroize(buf1, sizeof(buf1));
  ct_zeroize(buf2, sizeof(buf2));
  ct_zeroize(buf3, sizeof(buf3));
  ct_zeroize(extkey0, sizeof(extkey0));
  ct_zeroize(extkey1, sizeof(extkey1));
  ct_zeroize(extkey2, sizeof(extkey2));
  ct_zeroize(extkey3, sizeof(extkey3));
}

#if MLKEM_K == 2 || MLKEM_K == 4
/*************************************************
 * Name:        poly_cbd_eta2
 *
 * Description: Given an array of uniformly random bytes, compute
 *              polynomial with coefficients distributed according to
 *              a centered binomial distribution with parameter MLKEM_ETA2.
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *buf: pointer to input byte array
 **************************************************/
static MLK_INLINE void poly_cbd_eta2(
    poly *r, const uint8_t buf[MLKEM_ETA2 * MLKEM_N / 4])
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  requires(memory_no_alias(buf, MLKEM_ETA2 * MLKEM_N / 4))
  assigns(memory_slice(r, sizeof(poly)))
  ensures(array_abs_bound(r->coeffs, 0, MLKEM_N, MLKEM_ETA2 + 1)))
{
#if MLKEM_ETA2 == 2
  poly_cbd2(r, buf);
#else
#error "Invalid value of MLKEM_ETA2"
#endif
}

MLK_INTERNAL_API
void poly_getnoise_eta2(poly *r, const uint8_t seed[MLKEM_SYMBYTES],
                        uint8_t nonce)
{
  MLK_ALIGN uint8_t buf[MLKEM_ETA2 * MLKEM_N / 4];
  MLK_ALIGN uint8_t extkey[MLKEM_SYMBYTES + 1];

  memcpy(extkey, seed, MLKEM_SYMBYTES);
  extkey[MLKEM_SYMBYTES] = nonce;
  prf_eta2(buf, extkey);

  poly_cbd_eta2(r, buf);

  debug_assert_abs_bound(r, MLKEM_N, MLKEM_ETA1 + 1);

  /* FIPS 203. Section 3.3 Destruction of intermediate values. */
  ct_zeroize(buf, sizeof(buf));
  ct_zeroize(extkey, sizeof(extkey));
}
#endif /* MLKEM_K == 2 || MLKEM_K == 4 */


#if MLKEM_K == 2
MLK_INTERNAL_API
void poly_getnoise_eta1122_4x(poly *r0, poly *r1, poly *r2, poly *r3,
                              const uint8_t seed[MLKEM_SYMBYTES],
                              uint8_t nonce0, uint8_t nonce1, uint8_t nonce2,
                              uint8_t nonce3)
{
#if MLKEM_ETA2 >= MLKEM_ETA1
#error poly_getnoise_eta1122_4x assumes MLKEM_ETA1 > MLKEM_ETA2
#endif
  MLK_ALIGN uint8_t buf0[MLKEM_ETA1 * MLKEM_N / 4];
  MLK_ALIGN uint8_t buf1[MLKEM_ETA1 * MLKEM_N / 4];
  /* Pad to larger buffer */
  MLK_ALIGN uint8_t buf2[MLKEM_ETA1 * MLKEM_N / 4];
  MLK_ALIGN uint8_t buf3[MLKEM_ETA1 * MLKEM_N / 4];

  MLK_ALIGN uint8_t extkey0[MLKEM_SYMBYTES + 1];
  MLK_ALIGN uint8_t extkey1[MLKEM_SYMBYTES + 1];
  MLK_ALIGN uint8_t extkey2[MLKEM_SYMBYTES + 1];
  MLK_ALIGN uint8_t extkey3[MLKEM_SYMBYTES + 1];

  memcpy(extkey0, seed, MLKEM_SYMBYTES);
  memcpy(extkey1, seed, MLKEM_SYMBYTES);
  memcpy(extkey2, seed, MLKEM_SYMBYTES);
  memcpy(extkey3, seed, MLKEM_SYMBYTES);
  extkey0[MLKEM_SYMBYTES] = nonce0;
  extkey1[MLKEM_SYMBYTES] = nonce1;
  extkey2[MLKEM_SYMBYTES] = nonce2;
  extkey3[MLKEM_SYMBYTES] = nonce3;

  /* On systems with fast batched Keccak, we use 4-fold batched PRF,
   * even though that means generating more random data in buf2 and buf3
   * than necessary. */
#if !defined(FIPS202_X4_DEFAULT_IMPLEMENTATION)
  prf_eta1_x4(buf0, buf1, buf2, buf3, extkey0, extkey1, extkey2, extkey3);
#else  /* FIPS202_X4_DEFAULT_IMPLEMENTATION */
  prf_eta1(buf0, extkey0);
  prf_eta1(buf1, extkey1);
  prf_eta2(buf2, extkey2);
  prf_eta2(buf3, extkey3);
#endif /* FIPS202_X4_DEFAULT_IMPLEMENTATION */

  poly_cbd_eta1(r0, buf0);
  poly_cbd_eta1(r1, buf1);
  poly_cbd_eta2(r2, buf2);
  poly_cbd_eta2(r3, buf3);

  debug_assert_abs_bound(r0, MLKEM_N, MLKEM_ETA1 + 1);
  debug_assert_abs_bound(r1, MLKEM_N, MLKEM_ETA1 + 1);
  debug_assert_abs_bound(r2, MLKEM_N, MLKEM_ETA2 + 1);
  debug_assert_abs_bound(r3, MLKEM_N, MLKEM_ETA2 + 1);

  /* FIPS 203. Section 3.3 Destruction of intermediate values. */
  ct_zeroize(buf0, sizeof(buf0));
  ct_zeroize(buf1, sizeof(buf1));
  ct_zeroize(buf2, sizeof(buf2));
  ct_zeroize(buf3, sizeof(buf3));
  ct_zeroize(extkey0, sizeof(extkey0));
  ct_zeroize(extkey1, sizeof(extkey1));
  ct_zeroize(extkey2, sizeof(extkey2));
  ct_zeroize(extkey3, sizeof(extkey3));
}
#endif /* MLKEM_K == 2 */

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef poly_cbd_eta1
#undef poly_cbd_eta2
