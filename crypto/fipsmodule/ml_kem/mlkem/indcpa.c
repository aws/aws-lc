/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "arith_backend.h"
#include "cbmc.h"
#include "debug.h"
#include "indcpa.h"
#include "poly.h"
#include "poly_k.h"
#include "randombytes.h"
#include "sampling.h"
#include "symmetric.h"

/* Static namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define pack_pk MLK_NAMESPACE_K(pack_pk)
#define unpack_pk MLK_NAMESPACE_K(unpack_pk)
#define pack_sk MLK_NAMESPACE_K(pack_sk)
#define unpack_sk MLK_NAMESPACE_K(unpack_sk)
#define pack_ciphertext MLK_NAMESPACE_K(pack_ciphertext)
#define unpack_ciphertext MLK_NAMESPACE_K(unpack_ciphertext)
#define matvec_mul MLK_NAMESPACE_K(matvec_mul)
/* End of static namespacing */

/*************************************************
 * Name:        pack_pk
 *
 * Description: Serialize the public key as concatenation of the
 *              serialized vector of polynomials pk
 *              and the public seed used to generate the matrix A.
 *
 * Arguments:   uint8_t *r: pointer to the output serialized public key
 *              polyvec *pk: pointer to the input public-key polyvec.
 *                Must have coefficients within [0,..,q-1].
 *              const uint8_t *seed: pointer to the input public seed
 **************************************************/
static void pack_pk(uint8_t r[MLKEM_INDCPA_PUBLICKEYBYTES], polyvec *pk,
                    const uint8_t seed[MLKEM_SYMBYTES])
{
  debug_assert_bound_2d(pk, MLKEM_K, MLKEM_N, 0, MLKEM_Q);
  polyvec_tobytes(r, pk);
  memcpy(r + MLKEM_POLYVECBYTES, seed, MLKEM_SYMBYTES);
}

/*************************************************
 * Name:        unpack_pk
 *
 * Description: De-serialize public key from a byte array;
 *              approximate inverse of pack_pk
 *
 * Arguments:   - polyvec *pk: pointer to output public-key polynomial vector
 *                  Coefficients will be normalized to [0,..,q-1].
 *              - uint8_t *seed: pointer to output seed to generate matrix A
 *              - const uint8_t *packedpk: pointer to input serialized public
 *                  key.
 **************************************************/
static void unpack_pk(polyvec *pk, uint8_t seed[MLKEM_SYMBYTES],
                      const uint8_t packedpk[MLKEM_INDCPA_PUBLICKEYBYTES])
{
  polyvec_frombytes(pk, packedpk);
  memcpy(seed, packedpk + MLKEM_POLYVECBYTES, MLKEM_SYMBYTES);

  /* NOTE: If a modulus check was conducted on the PK, we know at this
   * point that the coefficients of `pk` are unsigned canonical. The
   * specifications and proofs, however, do _not_ assume this, and instead
   * work with the easily provable bound by MLKEM_UINT12_LIMIT. */
}

/*************************************************
 * Name:        pack_sk
 *
 * Description: Serialize the secret key
 *
 * Arguments:   - uint8_t *r: pointer to output serialized secret key
 *              - polyvec *sk: pointer to input vector of polynomials (secret
 *key)
 **************************************************/
static void pack_sk(uint8_t r[MLKEM_INDCPA_SECRETKEYBYTES], polyvec *sk)
{
  debug_assert_bound_2d(sk, MLKEM_K, MLKEM_N, 0, MLKEM_Q);
  polyvec_tobytes(r, sk);
}

/*************************************************
 * Name:        unpack_sk
 *
 * Description: De-serialize the secret key; inverse of pack_sk
 *
 * Arguments:   - polyvec *sk: pointer to output vector of polynomials (secret
 *                key)
 *              - const uint8_t *packedsk: pointer to input serialized secret
 *                key
 **************************************************/
static void unpack_sk(polyvec *sk,
                      const uint8_t packedsk[MLKEM_INDCPA_SECRETKEYBYTES])
{
  polyvec_frombytes(sk, packedsk);
}

/*************************************************
 * Name:        pack_ciphertext
 *
 * Description: Serialize the ciphertext as concatenation of the
 *              compressed and serialized vector of polynomials b
 *              and the compressed and serialized polynomial v
 *
 * Arguments:   uint8_t *r: pointer to the output serialized ciphertext
 *              poly *pk: pointer to the input vector of polynomials b
 *              poly *v: pointer to the input polynomial v
 **************************************************/
static void pack_ciphertext(uint8_t r[MLKEM_INDCPA_BYTES], polyvec *b, poly *v)
{
  polyvec_compress_du(r, b);
  poly_compress_dv(r + MLKEM_POLYVECCOMPRESSEDBYTES_DU, v);
}

/*************************************************
 * Name:        unpack_ciphertext
 *
 * Description: De-serialize and decompress ciphertext from a byte array;
 *              approximate inverse of pack_ciphertext
 *
 * Arguments:   - polyvec *b: pointer to the output vector of polynomials b
 *              - poly *v: pointer to the output polynomial v
 *              - const uint8_t *c: pointer to the input serialized ciphertext
 **************************************************/
static void unpack_ciphertext(polyvec *b, poly *v,
                              const uint8_t c[MLKEM_INDCPA_BYTES])
{
  polyvec_decompress_du(b, c);
  poly_decompress_dv(v, c + MLKEM_POLYVECCOMPRESSEDBYTES_DU);
}

#if !defined(MLK_USE_NATIVE_NTT_CUSTOM_ORDER)
/* This namespacing is not done at the top to avoid a naming conflict
 * with native backends, which are currently not yet namespaced. */
#define poly_permute_bitrev_to_custom \
  MLK_NAMESPACE_K(poly_permute_bitrev_to_custom)

static MLK_INLINE void poly_permute_bitrev_to_custom(int16_t data[MLKEM_N])
__contract__(
  /* We don't specify that this should be a permutation, but only
   * that it does not change the bound established at the end of gen_matrix. */
  requires(memory_no_alias(data, sizeof(int16_t) * MLKEM_N))
  requires(array_bound(data, 0, MLKEM_N, 0, MLKEM_Q))
  assigns(memory_slice(data, sizeof(poly)))
  ensures(array_bound(data, 0, MLKEM_N, 0, MLKEM_Q))) { ((void)data); }
#endif /* MLK_USE_NATIVE_NTT_CUSTOM_ORDER */

/* Not static for benchmarking */
MLK_INTERNAL_API
void gen_matrix(polyvec *a, const uint8_t seed[MLKEM_SYMBYTES], int transposed)
{
  unsigned i, j;
  /*
   * We generate four separate seed arrays rather than a single one to work
   * around limitations in CBMC function contracts dealing with disjoint slices
   * of the same parent object.
   */

  MLK_ALIGN uint8_t seed0[MLKEM_SYMBYTES + 2];
  MLK_ALIGN uint8_t seed1[MLKEM_SYMBYTES + 2];
  MLK_ALIGN uint8_t seed2[MLKEM_SYMBYTES + 2];
  MLK_ALIGN uint8_t seed3[MLKEM_SYMBYTES + 2];
  uint8_t *seedxy[4];
  seedxy[0] = seed0;
  seedxy[1] = seed1;
  seedxy[2] = seed2;
  seedxy[3] = seed3;

  for (j = 0; j < 4; j++)
  {
    memcpy(seedxy[j], seed, MLKEM_SYMBYTES);
  }

  /* Sample 4 matrix entries a time. */
  for (i = 0; i < (MLKEM_K * MLKEM_K / 4) * 4; i += 4)
  {
    uint8_t x, y;

    for (j = 0; j < 4; j++)
    {
      x = (i + j) / MLKEM_K;
      y = (i + j) % MLKEM_K;
      if (transposed)
      {
        seedxy[j][MLKEM_SYMBYTES + 0] = x;
        seedxy[j][MLKEM_SYMBYTES + 1] = y;
      }
      else
      {
        seedxy[j][MLKEM_SYMBYTES + 0] = y;
        seedxy[j][MLKEM_SYMBYTES + 1] = x;
      }
    }

    /*
     * This call writes across polyvec boundaries for K=2 and K=3.
     * This is intentional and safe.
     */
    poly_rej_uniform_x4(&a[0].vec[0] + i, seedxy);
  }

  /* For MLKEM_K == 3, sample the last entry individually. */
  if (i < MLKEM_K * MLKEM_K)
  {
    uint8_t x, y;
    x = i / MLKEM_K;
    y = i % MLKEM_K;

    if (transposed)
    {
      seed0[MLKEM_SYMBYTES + 0] = x;
      seed0[MLKEM_SYMBYTES + 1] = y;
    }
    else
    {
      seed0[MLKEM_SYMBYTES + 0] = y;
      seed0[MLKEM_SYMBYTES + 1] = x;
    }

    poly_rej_uniform(&a[0].vec[0] + i, seed0);
    i++;
  }

  debug_assert(i == MLKEM_K * MLKEM_K);

  /*
   * The public matrix is generated in NTT domain. If the native backend
   * uses a custom order in NTT domain, permute A accordingly.
   */
  for (i = 0; i < MLKEM_K; i++)
  {
    for (j = 0; j < MLKEM_K; j++)
    {
      poly_permute_bitrev_to_custom(a[i].vec[j].coeffs);
    }
  }

  /* FIPS 203. Section 3.3 Destruction of intermediate values. */
  ct_zeroize(seed0, sizeof(seed0));
  ct_zeroize(seed1, sizeof(seed1));
  ct_zeroize(seed2, sizeof(seed2));
  ct_zeroize(seed3, sizeof(seed3));
}

/*************************************************
 * Name:        matvec_mul
 *
 * Description: Computes matrix-vector product in NTT domain,
 *              via Montgomery multiplication.
 *
 * Arguments:   - polyvec *out: Pointer to output polynomial vector
 *              - polyvec a[MLKEM_K]: Input matrix. Must be in NTT domain
 *                  and have coefficients of absolute value < 4096.
 *              - polyvec *v: Input polynomial vector. Must be in NTT domain.
 *              - polyvec *vc: Mulcache for v, computed via
 *                  polyvec_mulcache_compute().
 **************************************************/
static void matvec_mul(polyvec *out, const polyvec a[MLKEM_K], const polyvec *v,
                       const polyvec_mulcache *vc)
__contract__(
  requires(memory_no_alias(out, sizeof(polyvec)))
  requires(memory_no_alias(a, sizeof(polyvec) * MLKEM_K))
  requires(memory_no_alias(v, sizeof(polyvec)))
  requires(memory_no_alias(vc, sizeof(polyvec_mulcache)))
  requires(forall(k0, 0, MLKEM_K,
    forall(k1, 0, MLKEM_K,
      array_bound(a[k0].vec[k1].coeffs, 0, MLKEM_N, 0, MLKEM_UINT12_LIMIT))))
  assigns(object_whole(out)))
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  __loop__(
    assigns(i, object_whole(out))
    invariant(i <= MLKEM_K))
  {
    polyvec_basemul_acc_montgomery_cached(&out->vec[i], &a[i], v, vc);
  }
}

MLK_INTERNAL_API
void indcpa_keypair_derand(uint8_t pk[MLKEM_INDCPA_PUBLICKEYBYTES],
                           uint8_t sk[MLKEM_INDCPA_SECRETKEYBYTES],
                           const uint8_t coins[MLKEM_SYMBYTES])
{
  MLK_ALIGN uint8_t buf[2 * MLKEM_SYMBYTES];
  const uint8_t *publicseed = buf;
  const uint8_t *noiseseed = buf + MLKEM_SYMBYTES;
  polyvec a[MLKEM_K], e, pkpv, skpv;
  polyvec_mulcache skpv_cache;

  MLK_ALIGN uint8_t coins_with_domain_separator[MLKEM_SYMBYTES + 1];
  /* Concatenate coins with MLKEM_K for domain separation of security levels */
  memcpy(coins_with_domain_separator, coins, MLKEM_SYMBYTES);
  coins_with_domain_separator[MLKEM_SYMBYTES] = MLKEM_K;

  hash_g(buf, coins_with_domain_separator, MLKEM_SYMBYTES + 1);

  /*
   * Declassify the public seed.
   * Required to use it in conditional-branches in rejection sampling.
   * This is needed because all output of randombytes is marked as secret
   * (=undefined)
   */
  MLK_CT_TESTING_DECLASSIFY(publicseed, MLKEM_SYMBYTES);

  gen_matrix(a, publicseed, 0 /* no transpose */);

#if MLKEM_K == 2
  poly_getnoise_eta1_4x(skpv.vec + 0, skpv.vec + 1, e.vec + 0, e.vec + 1,
                        noiseseed, 0, 1, 2, 3);
#elif MLKEM_K == 3
  /*
   * Only the first three output buffers are needed.
   * The laster parameter is a dummy that's overwritten later.
   */
  poly_getnoise_eta1_4x(skpv.vec + 0, skpv.vec + 1, skpv.vec + 2,
                        pkpv.vec + 0 /* irrelevant */, noiseseed, 0, 1, 2,
                        0xFF /* irrelevant */);
  /* Same here */
  poly_getnoise_eta1_4x(e.vec + 0, e.vec + 1, e.vec + 2,
                        pkpv.vec + 0 /* irrelevant */, noiseseed, 3, 4, 5,
                        0xFF /* irrelevant */);
#elif MLKEM_K == 4
  poly_getnoise_eta1_4x(skpv.vec + 0, skpv.vec + 1, skpv.vec + 2, skpv.vec + 3,
                        noiseseed, 0, 1, 2, 3);
  poly_getnoise_eta1_4x(e.vec + 0, e.vec + 1, e.vec + 2, e.vec + 3, noiseseed,
                        4, 5, 6, 7);
#endif

  polyvec_ntt(&skpv);
  polyvec_ntt(&e);

  polyvec_mulcache_compute(&skpv_cache, &skpv);
  matvec_mul(&pkpv, a, &skpv, &skpv_cache);
  polyvec_tomont(&pkpv);

  polyvec_add(&pkpv, &e);
  polyvec_reduce(&pkpv);
  polyvec_reduce(&skpv);

  pack_sk(sk, &skpv);
  pack_pk(pk, &pkpv, publicseed);

  /* FIPS 203. Section 3.3 Destruction of intermediate values. */
  ct_zeroize(buf, sizeof(buf));
  ct_zeroize(coins_with_domain_separator, sizeof(coins_with_domain_separator));
  ct_zeroize(a, sizeof(a));
  ct_zeroize(&e, sizeof(e));
  ct_zeroize(&skpv, sizeof(skpv));
  ct_zeroize(&skpv_cache, sizeof(skpv_cache));
}


MLK_INTERNAL_API
void indcpa_enc(uint8_t c[MLKEM_INDCPA_BYTES],
                const uint8_t m[MLKEM_INDCPA_MSGBYTES],
                const uint8_t pk[MLKEM_INDCPA_PUBLICKEYBYTES],
                const uint8_t coins[MLKEM_SYMBYTES])
{
  MLK_ALIGN uint8_t seed[MLKEM_SYMBYTES];
  polyvec sp, pkpv, ep, at[MLKEM_K], b;
  poly v, k, epp;
  polyvec_mulcache sp_cache;

  unpack_pk(&pkpv, seed, pk);
  poly_frommsg(&k, m);

  /*
   * Declassify the public seed.
   * Required to use it in conditional-branches in rejection sampling.
   * This is needed because in re-encryption the publicseed originated from sk
   * which is marked undefined.
   */
  MLK_CT_TESTING_DECLASSIFY(seed, MLKEM_SYMBYTES);

  gen_matrix(at, seed, 1 /* transpose */);

#if MLKEM_K == 2
  poly_getnoise_eta1122_4x(sp.vec + 0, sp.vec + 1, ep.vec + 0, ep.vec + 1,
                           coins, 0, 1, 2, 3);
  poly_getnoise_eta2(&epp, coins, 4);
#elif MLKEM_K == 3
  /*
   * In this call, only the first three output buffers are needed.
   * The last parameter is a dummy that's overwritten later.
   */
  poly_getnoise_eta1_4x(sp.vec + 0, sp.vec + 1, sp.vec + 2, &b.vec[0], coins, 0,
                        1, 2, 0xFF);
  /* The fourth output buffer in this call _is_ used. */
  poly_getnoise_eta2_4x(ep.vec + 0, ep.vec + 1, ep.vec + 2, &epp, coins, 3, 4,
                        5, 6);
#elif MLKEM_K == 4
  poly_getnoise_eta1_4x(sp.vec + 0, sp.vec + 1, sp.vec + 2, sp.vec + 3, coins,
                        0, 1, 2, 3);
  poly_getnoise_eta2_4x(ep.vec + 0, ep.vec + 1, ep.vec + 2, ep.vec + 3, coins,
                        4, 5, 6, 7);
  poly_getnoise_eta2(&epp, coins, 8);
#endif

  polyvec_ntt(&sp);

  polyvec_mulcache_compute(&sp_cache, &sp);
  matvec_mul(&b, at, &sp, &sp_cache);
  polyvec_basemul_acc_montgomery_cached(&v, &pkpv, &sp, &sp_cache);

  polyvec_invntt_tomont(&b);
  poly_invntt_tomont(&v);

  polyvec_add(&b, &ep);
  poly_add(&v, &epp);
  poly_add(&v, &k);

  polyvec_reduce(&b);
  poly_reduce(&v);

  pack_ciphertext(c, &b, &v);

  /* FIPS 203. Section 3.3 Destruction of intermediate values. */
  ct_zeroize(seed, sizeof(seed));
  ct_zeroize(&sp, sizeof(sp));
  ct_zeroize(&sp_cache, sizeof(sp_cache));
  ct_zeroize(&b, sizeof(b));
  ct_zeroize(&v, sizeof(v));
  ct_zeroize(at, sizeof(at));
  ct_zeroize(&k, sizeof(k));
  ct_zeroize(&ep, sizeof(ep));
  ct_zeroize(&epp, sizeof(epp));
}

MLK_INTERNAL_API
void indcpa_dec(uint8_t m[MLKEM_INDCPA_MSGBYTES],
                const uint8_t c[MLKEM_INDCPA_BYTES],
                const uint8_t sk[MLKEM_INDCPA_SECRETKEYBYTES])
{
  polyvec b, skpv;
  poly v, sb;
  polyvec_mulcache b_cache;

  unpack_ciphertext(&b, &v, c);
  unpack_sk(&skpv, sk);

  polyvec_ntt(&b);
  polyvec_mulcache_compute(&b_cache, &b);
  polyvec_basemul_acc_montgomery_cached(&sb, &skpv, &b, &b_cache);
  poly_invntt_tomont(&sb);

  poly_sub(&v, &sb);
  poly_reduce(&v);

  poly_tomsg(m, &v);

  /* FIPS 203. Section 3.3 Destruction of intermediate values. */
  ct_zeroize(&skpv, sizeof(skpv));
  ct_zeroize(&b, sizeof(b));
  ct_zeroize(&b_cache, sizeof(b_cache));
  ct_zeroize(&v, sizeof(v));
  ct_zeroize(&sb, sizeof(sb));
}

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef pack_pk
#undef unpack_pk
#undef pack_sk
#undef unpack_sk
#undef pack_ciphertext
#undef unpack_ciphertext
#undef matvec_mul
#undef poly_permute_bitrev_to_custom
