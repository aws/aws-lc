/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "common.h"
#if !defined(MLK_MULTILEVEL_BUILD_NO_SHARED)

#include <stdint.h>
#include <string.h>
#include "arith_backend.h"
#include "cbmc.h"
#include "debug.h"
#include "poly.h"
#include "sampling.h"
#include "symmetric.h"
#include "verify.h"

/* Static namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define fqmul MLK_NAMESPACE(fqmul)
#define barrett_reduce MLK_NAMESPACE(barrett_reduce)
#define scalar_signed_to_unsigned_q MLK_NAMESPACE(scalar_signed_to_unsigned_q)
#define ntt_butterfly_block MLK_NAMESPACE(ntt_butterfly_block)
#define ntt_layer MLK_NAMESPACE(ntt_layer)
#define invntt_layer MLK_NAMESPACE(invntt_layer)
/* End of static namespacing */

#if !defined(MLK_USE_NATIVE_POLY_TOMONT) ||           \
    !defined(MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE) || \
    !defined(MLK_USE_NATIVE_NTT) || !defined(MLK_USE_NATIVE_INTT)
/*************************************************
 * Name:        fqmul
 *
 * Description: Montgomery multiplication modulo q=3329
 *
 * Arguments:   - int16_t a: first factor
 *                  Can be any int16_t.
 *              - int16_t b: second factor.
 *                  Must be signed canonical (abs value <(q+1)/2)
 *
 * Returns 16-bit integer congruent to a*b*R^{-1} mod q, and
 * smaller than q in absolute value.
 *
 **************************************************/
static MLK_INLINE int16_t fqmul(int16_t a, int16_t b)
__contract__(
  requires(b > -MLKEM_Q_HALF && b < MLKEM_Q_HALF)
  ensures(return_value > -MLKEM_Q && return_value < MLKEM_Q)
)
{
  int16_t res;
  debug_assert_abs_bound(&b, 1, MLKEM_Q_HALF);

  res = montgomery_reduce((int32_t)a * (int32_t)b);
  /* Bounds:
   * |res| <= ceil(|a| * |b| / 2^16) + (MLKEM_Q + 1) / 2
   *       <= ceil(2^15 * ((MLKEM_Q - 1)/2) / 2^16) + (MLKEM_Q + 1) / 2
   *       <= ceil((MLKEM_Q - 1) / 4) + (MLKEM_Q + 1) / 2
   *        < MLKEM_Q
   */

  debug_assert_abs_bound(&res, 1, MLKEM_Q);
  return res;
}
#endif /* !defined(MLK_USE_NATIVE_POLY_TOMONT) ||           \
          !defined(MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE) || \
          !defined(MLK_USE_NATIVE_NTT) ||                   \
          !defined(MLK_USE_NATIVE_INTT) */

#if !defined(MLK_USE_NATIVE_POLY_REDUCE) || !defined(MLK_USE_NATIVE_INTT)
/*************************************************
 * Name:        barrett_reduce
 *
 * Description: Barrett reduction; given a 16-bit integer a, computes
 *              centered representative congruent to a mod q in
 *              {-(q-1)/2,...,(q-1)/2}
 *
 * Arguments:   - int16_t a: input integer to be reduced
 *
 * Returns:     integer in {-(q-1)/2,...,(q-1)/2} congruent to a modulo q.
 **************************************************/
static MLK_INLINE int16_t barrett_reduce(int16_t a)
__contract__(
  ensures(return_value > -MLKEM_Q_HALF && return_value < MLKEM_Q_HALF)
)
{
  /*
   * To divide by MLKEM_Q using Barrett multiplication, the "magic number"
   * multiplier is round_to_nearest(2**26/MLKEM_Q)
   */
  const int BPOWER = 26;
  const int32_t barrett_multiplier = ((1 << BPOWER) + MLKEM_Q / 2) / MLKEM_Q;

  /*
   * Compute round_to_nearest(a/MLKEM_Q) using the multiplier
   * above and shift by BPOWER places.
   * PORTABILITY: Right-shift on a signed integer is, strictly-speaking,
   * implementation-defined for negative left argument. Here,
   * we assume it's sign-preserving "arithmetic" shift right. (C99 6.5.7 (5))
   */
  const int32_t t = (barrett_multiplier * a + (1 << (BPOWER - 1))) >> BPOWER;

  /*
   * t is in -10 .. +10, so we need 32-bit math to
   * evaluate t * MLKEM_Q and the subsequent subtraction
   */
  int16_t res = (int16_t)(a - t * MLKEM_Q);

  debug_assert_abs_bound(&res, 1, MLKEM_Q_HALF);
  return res;
}
#endif /* !defined(MLK_USE_NATIVE_POLY_REDUCE) || \
          !defined(MLK_USE_NATIVE_INTT) */

#if !defined(MLK_USE_NATIVE_POLY_TOMONT)
MLK_INTERNAL_API
void poly_tomont(poly *r)
{
  unsigned i;
  const int16_t f = (1ULL << 32) % MLKEM_Q; /* 1353 */
  for (i = 0; i < MLKEM_N; i++)
  __loop__(
    invariant(i <= MLKEM_N)
    invariant(array_abs_bound(r->coeffs, 0, i, MLKEM_Q)))
  {
    r->coeffs[i] = fqmul(r->coeffs[i], f);
  }

  debug_assert_abs_bound(r, MLKEM_N, MLKEM_Q);
}
#else  /* MLK_USE_NATIVE_POLY_TOMONT */
MLK_INTERNAL_API
void poly_tomont(poly *r)
{
  poly_tomont_native(r->coeffs);
  debug_assert_abs_bound(r, MLKEM_N, MLKEM_Q);
}
#endif /* MLK_USE_NATIVE_POLY_TOMONT */

#if !defined(MLK_USE_NATIVE_POLY_REDUCE)
/************************************************************
 * Name: scalar_signed_to_unsigned_q
 *
 * Description: converts signed polynomial coefficient
 *              from signed (-3328 .. 3328) form to
 *              unsigned form (0 .. 3328).
 *
 * Note: Cryptographic constant time implementation
 *
 * Examples:       0 -> 0
 *                 1 -> 1
 *              3328 -> 3328
 *                -1 -> 3328
 *                -2 -> 3327
 *             -3328 -> 1
 *
 * Arguments: c: signed coefficient to be converted
 ************************************************************/
static MLK_INLINE uint16_t scalar_signed_to_unsigned_q(int16_t c)
__contract__(
  requires(c > -MLKEM_Q && c < MLKEM_Q)
  ensures(return_value >= 0 && return_value < MLKEM_Q)
  ensures(return_value == (int32_t)c + (((int32_t)c < 0) * MLKEM_Q)))
{
  debug_assert_abs_bound(&c, 1, MLKEM_Q);

  /* Add Q if c is negative, but in constant time */
  c = ct_sel_int16(c + MLKEM_Q, c, ct_cmask_neg_i16(c));

  /* and therefore cast to uint16_t is safe. */
  debug_assert_bound(&c, 1, 0, MLKEM_Q);
  return (uint16_t)c;
}

MLK_INTERNAL_API
void poly_reduce(poly *r)
{
  unsigned i;
  for (i = 0; i < MLKEM_N; i++)
  __loop__(
    invariant(i <= MLKEM_N)
    invariant(array_bound(r->coeffs, 0, i, 0, MLKEM_Q)))
  {
    /* Barrett reduction, giving signed canonical representative */
    int16_t t = barrett_reduce(r->coeffs[i]);
    /* Conditional addition to get unsigned canonical representative */
    r->coeffs[i] = scalar_signed_to_unsigned_q(t);
  }

  debug_assert_bound(r, MLKEM_N, 0, MLKEM_Q);
}
#else  /* MLK_USE_NATIVE_POLY_REDUCE */
MLK_INTERNAL_API
void poly_reduce(poly *r)
{
  poly_reduce_native(r->coeffs);
  debug_assert_bound(r, MLKEM_N, 0, MLKEM_Q);
}
#endif /* MLK_USE_NATIVE_POLY_REDUCE */

MLK_INTERNAL_API
void poly_add(poly *r, const poly *b)
{
  unsigned i;
  for (i = 0; i < MLKEM_N; i++)
  __loop__(
    invariant(i <= MLKEM_N)
    invariant(forall(k0, i, MLKEM_N, r->coeffs[k0] == loop_entry(*r).coeffs[k0]))
    invariant(forall(k1, 0, i, r->coeffs[k1] == loop_entry(*r).coeffs[k1] + b->coeffs[k1])))
  {
    r->coeffs[i] = r->coeffs[i] + b->coeffs[i];
  }
}

MLK_INTERNAL_API
void poly_sub(poly *r, const poly *b)
{
  unsigned i;
  for (i = 0; i < MLKEM_N; i++)
  __loop__(
    invariant(i <= MLKEM_N)
    invariant(forall(k0, i, MLKEM_N, r->coeffs[k0] == loop_entry(*r).coeffs[k0]))
    invariant(forall(k1, 0, i, r->coeffs[k1] == loop_entry(*r).coeffs[k1] - b->coeffs[k1])))
  {
    r->coeffs[i] = r->coeffs[i] - b->coeffs[i];
  }
}

#if !defined(MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE)
MLK_INTERNAL_API
void poly_mulcache_compute(poly_mulcache *x, const poly *a)
{
  unsigned i;
  for (i = 0; i < MLKEM_N / 4; i++)
  __loop__(
    invariant(i <= MLKEM_N / 4)
    invariant(array_abs_bound(x->coeffs, 0, 2 * i, MLKEM_Q)))
  {
    x->coeffs[2 * i + 0] = fqmul(a->coeffs[4 * i + 1], zetas[64 + i]);
    x->coeffs[2 * i + 1] = fqmul(a->coeffs[4 * i + 3], -zetas[64 + i]);
  }

  /*
   * This bound is true for the C implementation, but not needed
   * in the higher level bounds reasoning. It is thus omitted
   * them from the spec to not unnecessarily constrain native
   * implementations, but checked here nonetheless.
   */
  debug_assert_abs_bound(x, MLKEM_N / 2, MLKEM_Q);
}
#else  /* MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE */
MLK_INTERNAL_API
void poly_mulcache_compute(poly_mulcache *x, const poly *a)
{
  poly_mulcache_compute_native(x->coeffs, a->coeffs);
  /* Omitting bounds assertion since native implementations may
   * decide not to use a mulcache. Note that the C backend implementation
   * of poly_basemul_montgomery_cached() does still include the check. */
}
#endif /* MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE */

#if !defined(MLK_USE_NATIVE_NTT)
/*
 * Computes a block CT butterflies with a fixed twiddle factor,
 * using Montgomery multiplication.
 * Parameters:
 * - r: Pointer to base of polynomial (_not_ the base of butterfly block)
 * - root: Twiddle factor to use for the butterfly. This must be in
 *         Montgomery form and signed canonical.
 * - start: Offset to the beginning of the butterfly block
 * - len: Index difference between coefficients subject to a butterfly
 * - bound: Ghost variable describing coefficient bound: Prior to `start`,
 *          coefficients must be bound by `bound + MLKEM_Q`. Post `start`,
 *          they must be bound by `bound`.
 * When this function returns, output coefficients in the index range
 * [start, start+2*len) have bound bumped to `bound + MLKEM_Q`.
 * Example:
 * - start=8, len=4
 *   This would compute the following four butterflies
 *          8     --    12
 *             9    --     13
 *                10   --     14
 *                   11   --     15
 * - start=4, len=2
 *   This would compute the following two butterflies
 *          4 -- 6
 *             5 -- 7
 */
static void ntt_butterfly_block(int16_t r[MLKEM_N], int16_t zeta,
                                unsigned start, unsigned len, int bound)
__contract__(
  requires(start < MLKEM_N)
  requires(1 <= len && len <= MLKEM_N / 2 && start + 2 * len <= MLKEM_N)
  requires(0 <= bound && bound < INT16_MAX - MLKEM_Q)
  requires(-MLKEM_Q_HALF < zeta && zeta < MLKEM_Q_HALF)
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(r, 0, start, bound + MLKEM_Q))
  requires(array_abs_bound(r, start, MLKEM_N, bound))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, start + 2*len, bound + MLKEM_Q))
  ensures(array_abs_bound(r, start + 2 * len, MLKEM_N, bound)))
{
  /* `bound` is a ghost variable only needed in the CBMC specification */
  unsigned j;
  ((void)bound);
  for (j = start; j < start + len; j++)
  __loop__(
    invariant(start <= j && j <= start + len)
    /*
     * Coefficients are updated in strided pairs, so the bounds for the
     * intermediate states alternate twice between the old and new bound
     */
    invariant(array_abs_bound(r, 0,           j,           bound + MLKEM_Q))
    invariant(array_abs_bound(r, j,           start + len, bound))
    invariant(array_abs_bound(r, start + len, j + len,     bound + MLKEM_Q))
    invariant(array_abs_bound(r, j + len,     MLKEM_N,     bound)))
  {
    int16_t t;
    t = fqmul(r[j + len], zeta);
    r[j + len] = r[j] - t;
    r[j] = r[j] + t;
  }
}

/*
 *Compute one layer of forward NTT
 * Parameters:
 * - r: Pointer to base of polynomial
 * - len: Stride of butterflies in this layer.
 * - layer: Ghost variable indicating which layer is being applied.
 *          Must match `len` via `len == MLKEM_N >> layer`.
 * Note: `len` could be dropped and computed in the function, but
 *   we are following the structure of the reference NTT from the
 *   official Kyber implementation here, merely adding `layer` as
 *   a ghost variable for the specifications.
 */
static void ntt_layer(int16_t r[MLKEM_N], unsigned len, unsigned layer)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(1 <= layer && layer <= 7 && len == (MLKEM_N >> layer))
  requires(array_abs_bound(r, 0, MLKEM_N, layer * MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, (layer + 1) * MLKEM_Q)))
{
  unsigned start, k;
  /* `layer` is a ghost variable only needed in the CBMC specification */
  ((void)layer);
  /* Twiddle factors for layer n start at index 2^(layer-1) */
  k = MLKEM_N / (2 * len);
  for (start = 0; start < MLKEM_N; start += 2 * len)
  __loop__(
    invariant(start < MLKEM_N + 2 * len)
    invariant(k <= MLKEM_N / 2 && 2 * len * k == start + MLKEM_N)
    invariant(array_abs_bound(r, 0, start, layer * MLKEM_Q + MLKEM_Q))
    invariant(array_abs_bound(r, start, MLKEM_N, layer * MLKEM_Q)))
  {
    int16_t zeta = zetas[k++];
    ntt_butterfly_block(r, zeta, start, len, layer * MLKEM_Q);
  }
}

/*
 * Compute full forward NTT
 * NOTE: This particular implementation satisfies a much tighter
 * bound on the output coefficients (5*q) than the contractual one (8*q),
 * but this is not needed in the calling code. Should we change the
 * base multiplication strategy to require smaller NTT output bounds,
 * the proof may need strengthening.
 */

MLK_INTERNAL_API
void poly_ntt(poly *p)
{
  unsigned len, layer;
  int16_t *r;
  debug_assert_abs_bound(p, MLKEM_N, MLKEM_Q);
  r = p->coeffs;

  for (len = 128, layer = 1; len >= 2; len >>= 1, layer++)
  __loop__(
    invariant(1 <= layer && layer <= 8 && len == (MLKEM_N >> layer))
    invariant(array_abs_bound(r, 0, MLKEM_N, layer * MLKEM_Q)))
  {
    ntt_layer(r, len, layer);
  }

  /* Check the stronger bound */
  debug_assert_abs_bound(p, MLKEM_N, MLK_NTT_BOUND);
}
#else  /* MLK_USE_NATIVE_NTT */

MLK_INTERNAL_API
void poly_ntt(poly *p)
{
  debug_assert_abs_bound(p, MLKEM_N, MLKEM_Q);
  ntt_native(p->coeffs);
  debug_assert_abs_bound(p, MLKEM_N, MLK_NTT_BOUND);
}
#endif /* MLK_USE_NATIVE_NTT */

#if !defined(MLK_USE_NATIVE_INTT)

/* Compute one layer of inverse NTT */
static void invntt_layer(int16_t *r, unsigned len, unsigned layer)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(2 <= len && len <= 128 && 1 <= layer && layer <= 7)
  requires(len == (1 << (8 - layer)))
  requires(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q)))
{
  unsigned start, k;
  /* `layer` is a ghost variable used only in the specification */
  ((void)layer);
  k = MLKEM_N / len - 1;
  for (start = 0; start < MLKEM_N; start += 2 * len)
  __loop__(
    invariant(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q))
    invariant(start <= MLKEM_N && k <= 127)
    /* Normalised form of k == MLKEM_N / len - 1 - start / (2 * len) */
    invariant(2 * len * k + start == 2 * MLKEM_N - 2 * len))
  {
    unsigned j;
    int16_t zeta = zetas[k--];
    for (j = start; j < start + len; j++)
    __loop__(
      invariant(start <= j && j <= start + len)
      invariant(start <= MLKEM_N && k <= 127)
      invariant(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q)))
    {
      int16_t t = r[j];
      r[j] = barrett_reduce(t + r[j + len]);
      r[j + len] = r[j + len] - t;
      r[j + len] = fqmul(r[j + len], zeta);
    }
  }
}

MLK_INTERNAL_API
void poly_invntt_tomont(poly *p)
{
  /*
   * Scale input polynomial to account for Montgomery factor
   * and NTT twist. This also brings coefficients down to
   * absolute value < MLKEM_Q.
   */
  unsigned j, len, layer;
  const int16_t f = 1441;
  int16_t *r = p->coeffs;

  for (j = 0; j < MLKEM_N; j++)
  __loop__(
    invariant(j <= MLKEM_N)
    invariant(array_abs_bound(r, 0, j, MLKEM_Q)))
  {
    r[j] = fqmul(r[j], f);
  }

  /* Run the invNTT layers */
  for (len = 2, layer = 7; len <= 128; len <<= 1, layer--)
  __loop__(
    invariant(2 <= len && len <= 256 && layer <= 7 && len == (1 << (8 - layer)))
    invariant(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q)))
  {
    invntt_layer(p->coeffs, len, layer);
  }

  debug_assert_abs_bound(p, MLKEM_N, MLK_INVNTT_BOUND);
}
#else  /* MLK_USE_NATIVE_INTT */

MLK_INTERNAL_API
void poly_invntt_tomont(poly *p)
{
  intt_native(p->coeffs);
  debug_assert_abs_bound(p, MLKEM_N, MLK_INVNTT_BOUND);
}
#endif /* MLK_USE_NATIVE_INTT */

#else /* MLK_MULTILEVEL_BUILD_NO_SHARED */

MLK_EMPTY_CU(poly)

#endif /* MLK_MULTILEVEL_BUILD_NO_SHARED */

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef fqmul
#undef barrett_reduce
#undef scalar_signed_to_unsigned_q
#undef ntt_butterfly_block
#undef ntt_layer
#undef invntt_layer
