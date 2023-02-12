/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0 OR ISC
------------------------------------------------------------------------------------
*/

#include <openssl/bn.h>
#include <openssl/ec.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include "../bn/internal.h"
#include "../cpucap/internal.h"
#include "../delocate.h"
#include "internal.h"

#if !defined(OPENSSL_SMALL)

// We have two implementations of the field arithmetic for P-384 curve:
//   - Fiat-crypto
//   - s2n-bignum
// Both Fiat-crypto and s2n-bignum implementations are formally verified.
// Fiat-crypto implementation is fully portable C code, while s2n-bignum
// implements the operations in assembly for x86_64 and aarch64 platforms.
// All the P-384 field operations supported by Fiat-crypto are supported
// by s2n-bignum as well, so s2n-bignum can be used as a drop-in replacement
// when appropriate. To do that we define macros for the functions.
// For example, field addition macro is either defined as
//   #define p384_felem_add(out, in0, in1) fiat_p384_add(out, in0, in1)
// when Fiat-crypto is used, or as:
//   #define p384_felem_add(out, in0, in1) bignum_add_p384(out, in0, in1)
// when s2n-bignum is used.
//
// If (1) x86_64 or aarch64, (2) linux or apple, and (3) OPENSSL_NO_ASM is not
// set, s2n-bignum path is capable.
#if !defined(OPENSSL_NO_ASM) &&                                                \
    (defined(OPENSSL_LINUX) || defined(OPENSSL_APPLE)) &&                      \
    ((defined(OPENSSL_X86_64) && !defined(MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX)) || \
     defined(OPENSSL_AARCH64))

#  include "../../../third_party/s2n-bignum/include/s2n-bignum_aws-lc.h"

#  define P384_USE_S2N_BIGNUM_FIELD_ARITH 1
#  define P384_USE_64BIT_LIMBS_FELEM 1

#else

#  if defined(BORINGSSL_HAS_UINT128)
#    include "../../../third_party/fiat/p384_64.h"
#    define P384_USE_64BIT_LIMBS_FELEM 1
#  else
#    include "../../../third_party/fiat/p384_32.h"
#  endif

#endif

#if defined(P384_USE_64BIT_LIMBS_FELEM)

#define P384_NLIMBS (6)
typedef uint64_t p384_limb_t;
typedef uint64_t p384_felem[P384_NLIMBS];
static const p384_felem p384_felem_one = {
    0xffffffff00000001, 0xffffffff, 0x1, 0x0, 0x0, 0x0};

#else  // 64BIT; else 32BIT

#define P384_NLIMBS (12)
typedef uint32_t p384_limb_t;
typedef uint32_t p384_felem[P384_NLIMBS];
static const p384_felem p384_felem_one = {
    0x1, 0xffffffff, 0xffffffff, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0};

#endif  // 64BIT


#if defined(P384_USE_S2N_BIGNUM_FIELD_ARITH)

#if defined(OPENSSL_X86_64)
// On x86_64 platforms s2n-bignum uses bmi2 and adx instruction sets
// for some of the functions. These instructions are not supported by
// every x86 CPU so we have to check if they are available and in case
// they are not we fallback to slightly slower but generic implementation.
static inline uint8_t p384_use_s2n_bignum_alt(void) {
  return (!CRYPTO_is_BMI2_capable() || !CRYPTO_is_ADX_capable());
}
#else
// On aarch64 platforms s2n-bignum has two implementations of certain
// functions -- the default one and the alternative (suffixed _alt).
// Depending on the architecture one version is faster than the other.
// Generally, the "_alt" functions are faster on architectures with higher
// multiplier throughput, for example, Graviton 3, Apple's M1 and iPhone chips.
static inline uint8_t p384_use_s2n_bignum_alt(void) {
  return CRYPTO_is_ARMv8_wide_multiplier_capable();
}
#endif

#define p384_felem_add(out, in0, in1)   bignum_add_p384(out, in0, in1)
#define p384_felem_sub(out, in0, in1)   bignum_sub_p384(out, in0, in1)
#define p384_felem_opp(out, in0)        bignum_neg_p384(out, in0)
#define p384_felem_to_bytes(out, in0)   bignum_tolebytes_6(out, in0)
#define p384_felem_from_bytes(out, in0) bignum_fromlebytes_6(out, in0)

// The following four functions need bmi2 and adx support.
#define p384_felem_mul(out, in0, in1) \
  if (p384_use_s2n_bignum_alt()) bignum_montmul_p384_alt(out, in0, in1); \
  else bignum_montmul_p384(out, in0, in1);

#define p384_felem_sqr(out, in0) \
  if (p384_use_s2n_bignum_alt()) bignum_montsqr_p384_alt(out, in0); \
  else bignum_montsqr_p384(out, in0);

#define p384_felem_to_mont(out, in0) \
  if (p384_use_s2n_bignum_alt()) bignum_tomont_p384_alt(out, in0); \
  else bignum_tomont_p384(out, in0);

#define p384_felem_from_mont(out, in0) \
  if (p384_use_s2n_bignum_alt()) bignum_deamont_p384_alt(out, in0); \
  else bignum_deamont_p384(out, in0);

static p384_limb_t p384_felem_nz(const p384_limb_t in1[P384_NLIMBS]) {
  return bignum_nonzero_6(in1);
}

#else // P384_USE_S2N_BIGNUM_FIELD_ARITH

// Fiat-crypto implementation of field arithmetic
#define p384_felem_add(out, in0, in1)   fiat_p384_add(out, in0, in1)
#define p384_felem_sub(out, in0, in1)   fiat_p384_sub(out, in0, in1)
#define p384_felem_opp(out, in0)        fiat_p384_opp(out, in0)
#define p384_felem_mul(out, in0, in1)   fiat_p384_mul(out, in0, in1)
#define p384_felem_sqr(out, in0)        fiat_p384_square(out, in0)
#define p384_felem_to_mont(out, in0)    fiat_p384_to_montgomery(out, in0)
#define p384_felem_from_mont(out, in0)  fiat_p384_from_montgomery(out, in0)
#define p384_felem_to_bytes(out, in0)   fiat_p384_to_bytes(out, in0)
#define p384_felem_from_bytes(out, in0) fiat_p384_from_bytes(out, in0)

static p384_limb_t p384_felem_nz(const p384_limb_t in1[P384_NLIMBS]) {
  p384_limb_t ret;
  fiat_p384_nonzero(&ret, in1);
  return ret;
}

#endif // P384_USE_S2N_BIGNUM_FIELD_ARITH


static void p384_felem_copy(p384_limb_t out[P384_NLIMBS],
                           const p384_limb_t in1[P384_NLIMBS]) {
  for (size_t i = 0; i < P384_NLIMBS; i++) {
    out[i] = in1[i];
  }
}

static void p384_felem_cmovznz(p384_limb_t out[P384_NLIMBS],
                               p384_limb_t t,
                               const p384_limb_t z[P384_NLIMBS],
                               const p384_limb_t nz[P384_NLIMBS]) {
  p384_limb_t mask = constant_time_is_zero_w(t);
  for (size_t i = 0; i < P384_NLIMBS; i++) {
    out[i] = constant_time_select_w(mask, z[i], nz[i]);
  }
}

static void p384_from_generic(p384_felem out, const EC_FELEM *in) {
#ifdef OPENSSL_BIG_ENDIAN
  uint8_t tmp[P384_EC_FELEM_BYTES];
  bn_words_to_little_endian(tmp, P384_EC_FELEM_BYTES, in->words, P384_EC_FELEM_WORDS);
  p384_felem_from_bytes(out, tmp);
#else
  p384_felem_from_bytes(out, (const uint8_t *)in->words);
#endif
}

static void p384_to_generic(EC_FELEM *out, const p384_felem in) {
  // This works because 384 is a multiple of 64, so there are no excess bytes to
  // zero when rounding up to |BN_ULONG|s.
  OPENSSL_STATIC_ASSERT(
      384 / 8 == sizeof(BN_ULONG) * ((384 + BN_BITS2 - 1) / BN_BITS2),
      p384_felem_to_bytes_leaves_bytes_uninitialized);
#ifdef OPENSSL_BIG_ENDIAN
  uint8_t tmp[P384_EC_FELEM_BYTES];
  p384_felem_to_bytes(tmp, in);
  bn_little_endian_to_words(out->words, P384_EC_FELEM_WORDS, tmp, P384_EC_FELEM_BYTES);
#else
  p384_felem_to_bytes((uint8_t *)out->words, in);
#endif
}

static void p384_from_scalar(p384_felem out, const EC_SCALAR *in) {
#ifdef OPENSSL_BIG_ENDIAN
  uint8_t tmp[P384_EC_FELEM_BYTES];
  bn_words_to_little_endian(tmp, P384_EC_FELEM_BYTES, in->words, P384_EC_FELEM_WORDS);
  p384_felem_from_bytes(out, tmp);
#else
  p384_felem_from_bytes(out, (const uint8_t *)in->words);
#endif
}

// p384_inv_square calculates |out| = |in|^{-2}
//
// Based on Fermat's Little Theorem:
//   a^p = a (mod p)
//   a^{p-1} = 1 (mod p)
//   a^{p-3} = a^{-2} (mod p)
// p = 2^384 - 2^128 - 2^96 + 2^32 - 1
// Hexadecimal representation of p − 3:
// p-3 = ffffffff ffffffff ffffffff ffffffff ffffffff ffffffff ffffffff fffffffe
//       ffffffff 00000000 00000000 fffffffc
static void p384_inv_square(p384_felem out,
                            const p384_felem in) {
  // This implements the addition chain described in
  // https://briansmith.org/ecc-inversion-addition-chains-01#p384_field_inversion
  // The side comments show the value of the exponent:
  // squaring the element => doubling the exponent
  // multiplying by an element => adding to the exponent the power of that element
  p384_felem x2, x3, x6, x12, x15, x30, x60, x120;
  p384_felem_sqr(x2, in);   // 2^2 - 2^1
  p384_felem_mul(x2, x2, in);  // 2^2 - 2^0

  p384_felem_sqr(x3, x2);   // 2^3 - 2^1
  p384_felem_mul(x3, x3, in);  // 2^3 - 2^0

  p384_felem_sqr(x6, x3);
  for (int i = 1; i < 3; i++) {
    p384_felem_sqr(x6, x6);
  }                           // 2^6 - 2^3
  p384_felem_mul(x6, x6, x3);  // 2^6 - 2^0

  p384_felem_sqr(x12, x6);
  for (int i = 1; i < 6; i++) {
    p384_felem_sqr(x12, x12);
  }                             // 2^12 - 2^6
  p384_felem_mul(x12, x12, x6);  // 2^12 - 2^0

  p384_felem_sqr(x15, x12);
  for (int i = 1; i < 3; i++) {
    p384_felem_sqr(x15, x15);
  }                             // 2^15 - 2^3
  p384_felem_mul(x15, x15, x3);  // 2^15 - 2^0

  p384_felem_sqr(x30, x15);
  for (int i = 1; i < 15; i++) {
    p384_felem_sqr(x30, x30);
  }                              // 2^30 - 2^15
  p384_felem_mul(x30, x30, x15);  // 2^30 - 2^0

  p384_felem_sqr(x60, x30);
  for (int i = 1; i < 30; i++) {
    p384_felem_sqr(x60, x60);
  }                              // 2^60 - 2^30
  p384_felem_mul(x60, x60, x30);  // 2^60 - 2^0

  p384_felem_sqr(x120, x60);
  for (int i = 1; i < 60; i++) {
    p384_felem_sqr(x120, x120);
  }                                // 2^120 - 2^60
  p384_felem_mul(x120, x120, x60);  // 2^120 - 2^0

  p384_felem ret;
  p384_felem_sqr(ret, x120);
  for (int i = 1; i < 120; i++) {
    p384_felem_sqr(ret, ret);
  }                                // 2^240 - 2^120
  p384_felem_mul(ret, ret, x120);   // 2^240 - 2^0

  for (int i = 0; i < 15; i++) {
    p384_felem_sqr(ret, ret);
  }                                // 2^255 - 2^15
  p384_felem_mul(ret, ret, x15);    // 2^255 - 2^0

  // Why (1 + 30) in the loop?
  // This is as expressed in:
  //   https://briansmith.org/ecc-inversion-addition-chains-01#p384_field_inversion
  // My guess is to say that we're going to shift 31 bits, but this time we
  // won't add x31 to make all the new bits 1s, as was done in previous steps,
  // but we're going to add x30 so there will be 255 1s, then a 0, then 30 1s
  // to form this pattern:
  //   ffffffff ffffffff ffffffff ffffffff ffffffff ffffffff ffffffff fffffffe ffffffff
  // (the last 2 1s are appended in the following step).
  for (int i = 0; i < (1 + 30); i++) {
    p384_felem_sqr(ret, ret);
  }                                // 2^286 - 2^31
  p384_felem_mul(ret, ret, x30);    // 2^286 - 2^30 - 2^0

  p384_felem_sqr(ret, ret);
  p384_felem_sqr(ret, ret);      // 2^288 - 2^32 - 2^2
  p384_felem_mul(ret, ret, x2);     // 2^288 - 2^32 - 2^0

  // Why not 94 instead of (64 + 30) in the loop?
  // Similarly to the comment above, there is a shift of 94 bits
  // but what will be added is x30, which will cause 64 of those bits
  // to be 64 0s and 30 1s to complete the pattern above with:
  //   00000000 00000000 fffffffc
  // (the last 2 0s are appended by the last 2 shifts).
  for (int i = 0; i < (64 + 30); i++) {
    p384_felem_sqr(ret, ret);
  }                                // 2^382 - 2^126 - 2^94
  p384_felem_mul(ret, ret, x30);    // 2^382 - 2^126 - 2^94 + 2^30 - 2^0

  p384_felem_sqr(ret, ret);
  p384_felem_sqr(out, ret);      // 2^384 - 2^128 - 2^96 + 2^32 - 2^2 = p - 3
}

// Group operations
// ----------------
//
// Building on top of the field operations we have the operations on the
// elliptic curve group itself. Points on the curve are represented in Jacobian
// coordinates.
//
// p384_point_double calculates 2*(x_in, y_in, z_in)
//
// The method is taken from:
//   http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html#doubling-dbl-2001-b
//
// Coq transcription and correctness proof:
// <https://github.com/mit-plv/fiat-crypto/blob/79f8b5f39ed609339f0233098dee1a3c4e6b3080/src/Curves/Weierstrass/Jacobian.v#L93>
// <https://github.com/mit-plv/fiat-crypto/blob/79f8b5f39ed609339f0233098dee1a3c4e6b3080/src/Curves/Weierstrass/Jacobian.v#L201>
// Outputs can equal corresponding inputs, i.e., x_out == x_in is allowed;
// while x_out == y_in is not (maybe this works, but it's not tested).
static void p384_point_double(p384_felem x_out,
                              p384_felem y_out,
                              p384_felem z_out,
                              const p384_felem x_in,
                              const p384_felem y_in,
                              const p384_felem z_in) {
  p384_felem delta, gamma, beta, ftmp, ftmp2, tmptmp, alpha, fourbeta;
  // delta = z^2
  p384_felem_sqr(delta, z_in);
  // gamma = y^2
  p384_felem_sqr(gamma, y_in);
  // beta = x*gamma
  p384_felem_mul(beta, x_in, gamma);

  // alpha = 3*(x-delta)*(x+delta)
  p384_felem_sub(ftmp, x_in, delta);
  p384_felem_add(ftmp2, x_in, delta);

  p384_felem_add(tmptmp, ftmp2, ftmp2);
  p384_felem_add(ftmp2, ftmp2, tmptmp);
  p384_felem_mul(alpha, ftmp, ftmp2);

  // x' = alpha^2 - 8*beta
  p384_felem_sqr(x_out, alpha);
  p384_felem_add(fourbeta, beta, beta);
  p384_felem_add(fourbeta, fourbeta, fourbeta);
  p384_felem_add(tmptmp, fourbeta, fourbeta);
  p384_felem_sub(x_out, x_out, tmptmp);

  // z' = (y + z)^2 - gamma - delta
  // The following calculation differs from that in p256.c:
  // an add is replaced with a sub. This saves us 5 cmovznz operations
  // when Fiat-crypto implementation of felem_add and felem_sub is used,
  // and also a certain number of intructions when s2n-bignum is used.
  p384_felem_add(ftmp, y_in, z_in);
  p384_felem_sqr(z_out, ftmp);
  p384_felem_sub(z_out, z_out, gamma);
  p384_felem_sub(z_out, z_out, delta);

  // y' = alpha*(4*beta - x') - 8*gamma^2
  p384_felem_sub(y_out, fourbeta, x_out);
  p384_felem_add(gamma, gamma, gamma);
  p384_felem_sqr(gamma, gamma);
  p384_felem_mul(y_out, alpha, y_out);
  p384_felem_add(gamma, gamma, gamma);
  p384_felem_sub(y_out, y_out, gamma);
}

// p384_point_add calculates (x1, y1, z1) + (x2, y2, z2)
//
// The method is taken from:
//   http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#addition-add-2007-bl
// adapted for mixed addition (z2 = 1, or z2 = 0 for the point at infinity).
//
// Coq transcription and correctness proof:
// <https://github.com/davidben/fiat-crypto/blob/c7b95f62b2a54b559522573310e9b487327d219a/src/Curves/Weierstrass/Jacobian.v#L467>
// <https://github.com/davidben/fiat-crypto/blob/c7b95f62b2a54b559522573310e9b487327d219a/src/Curves/Weierstrass/Jacobian.v#L544>
static void p384_point_add(p384_felem x3, p384_felem y3, p384_felem z3,
                           const p384_felem x1,
                           const p384_felem y1,
                           const p384_felem z1,
                           const int mixed,
                           const p384_felem x2,
                           const p384_felem y2,
                           const p384_felem z2) {
  p384_felem x_out, y_out, z_out;
  p384_limb_t z1nz = p384_felem_nz(z1);
  p384_limb_t z2nz = p384_felem_nz(z2);

  // z1z1 = z1**2
  p384_felem z1z1;
  p384_felem_sqr(z1z1, z1);

  p384_felem u1, s1, two_z1z2;
  if (!mixed) {
    // z2z2 = z2**2
    p384_felem z2z2;
    p384_felem_sqr(z2z2, z2);

    // u1 = x1*z2z2
    p384_felem_mul(u1, x1, z2z2);

    // two_z1z2 = (z1 + z2)**2 - (z1z1 + z2z2) = 2z1z2
    p384_felem_add(two_z1z2, z1, z2);
    p384_felem_sqr(two_z1z2, two_z1z2);
    p384_felem_sub(two_z1z2, two_z1z2, z1z1);
    p384_felem_sub(two_z1z2, two_z1z2, z2z2);

    // s1 = y1 * z2**3
    p384_felem_mul(s1, z2, z2z2);
    p384_felem_mul(s1, s1, y1);
  } else {
    // We'll assume z2 = 1 (special case z2 = 0 is handled later).

    // u1 = x1*z2z2
    p384_felem_copy(u1, x1);
    // two_z1z2 = 2z1z2
    p384_felem_add(two_z1z2, z1, z1);
    // s1 = y1 * z2**3
    p384_felem_copy(s1, y1);
  }

  // u2 = x2*z1z1
  p384_felem u2;
  p384_felem_mul(u2, x2, z1z1);

  // h = u2 - u1
  p384_felem h;
  p384_felem_sub(h, u2, u1);

  p384_limb_t xneq = p384_felem_nz(h);

  // z_out = two_z1z2 * h
  p384_felem_mul(z_out, h, two_z1z2);

  // z1z1z1 = z1 * z1z1
  p384_felem z1z1z1;
  p384_felem_mul(z1z1z1, z1, z1z1);

  // s2 = y2 * z1**3
  p384_felem s2;
  p384_felem_mul(s2, y2, z1z1z1);

  // r = (s2 - s1)*2
  p384_felem r;
  p384_felem_sub(r, s2, s1);
  p384_felem_add(r, r, r);

  p384_limb_t yneq = p384_felem_nz(r);

  // This case will never occur in the constant-time |ec_GFp_mont_mul|.
  p384_limb_t is_nontrivial_double = constant_time_is_zero_w(xneq | yneq) &
                                    ~constant_time_is_zero_w(z1nz) &
                                    ~constant_time_is_zero_w(z2nz);
  if (constant_time_declassify_w(is_nontrivial_double)) {
    p384_point_double(x3, y3, z3, x1, y1, z1);
    return;
  }

  // I = (2h)**2
  p384_felem i;
  p384_felem_add(i, h, h);
  p384_felem_sqr(i, i);

  // J = h * I
  p384_felem j;
  p384_felem_mul(j, h, i);

  // V = U1 * I
  p384_felem v;
  p384_felem_mul(v, u1, i);

  // x_out = r**2 - J - 2V
  p384_felem_sqr(x_out, r);
  p384_felem_sub(x_out, x_out, j);
  p384_felem_sub(x_out, x_out, v);
  p384_felem_sub(x_out, x_out, v);

  // y_out = r(V-x_out) - 2 * s1 * J
  p384_felem_sub(y_out, v, x_out);
  p384_felem_mul(y_out, y_out, r);
  p384_felem s1j;
  p384_felem_mul(s1j, s1, j);
  p384_felem_sub(y_out, y_out, s1j);
  p384_felem_sub(y_out, y_out, s1j);

  p384_felem_cmovznz(x_out, z1nz, x2, x_out);
  p384_felem_cmovznz(x3, z2nz, x1, x_out);
  p384_felem_cmovznz(y_out, z1nz, y2, y_out);
  p384_felem_cmovznz(y3, z2nz, y1, y_out);
  p384_felem_cmovznz(z_out, z1nz, z2, z_out);
  p384_felem_cmovznz(z3, z2nz, z1, z_out);
}

// OPENSSL EC_METHOD FUNCTIONS

// Takes the Jacobian coordinates (X, Y, Z) of a point and returns:
//   (X', Y') = (X/Z^2, Y/Z^3).
static int ec_GFp_nistp384_point_get_affine_coordinates(
    const EC_GROUP *group, const EC_JACOBIAN *point,
    EC_FELEM *x_out, EC_FELEM *y_out) {

  if (constant_time_declassify_w(ec_GFp_simple_is_at_infinity(group, point))) {
    OPENSSL_PUT_ERROR(EC, EC_R_POINT_AT_INFINITY);
    return 0;
  }

  p384_felem z1, z2;
  p384_from_generic(z1, &point->Z);
  p384_inv_square(z2, z1);

  if (x_out != NULL) {
    p384_felem x;
    p384_from_generic(x, &point->X);
    p384_felem_mul(x, x, z2);
    p384_to_generic(x_out, x);
  }

  if (y_out != NULL) {
    p384_felem y;
    p384_from_generic(y, &point->Y);
    p384_felem_sqr(z2, z2);  // z^-4
    p384_felem_mul(y, y, z1);   // y * z
    p384_felem_mul(y, y, z2);   // y * z^-3
    p384_to_generic(y_out, y);
  }

  return 1;
}

static void ec_GFp_nistp384_add(const EC_GROUP *group, EC_JACOBIAN *r,
                                const EC_JACOBIAN *a, const EC_JACOBIAN *b) {
  p384_felem x1, y1, z1, x2, y2, z2;
  p384_from_generic(x1, &a->X);
  p384_from_generic(y1, &a->Y);
  p384_from_generic(z1, &a->Z);
  p384_from_generic(x2, &b->X);
  p384_from_generic(y2, &b->Y);
  p384_from_generic(z2, &b->Z);
  p384_point_add(x1, y1, z1, x1, y1, z1, 0 /* both Jacobian */, x2, y2, z2);
  p384_to_generic(&r->X, x1);
  p384_to_generic(&r->Y, y1);
  p384_to_generic(&r->Z, z1);
}

static void ec_GFp_nistp384_dbl(const EC_GROUP *group, EC_JACOBIAN *r,
                                const EC_JACOBIAN *a) {
  p384_felem x, y, z;
  p384_from_generic(x, &a->X);
  p384_from_generic(y, &a->Y);
  p384_from_generic(z, &a->Z);
  p384_point_double(x, y, z, x, y, z);
  p384_to_generic(&r->X, x);
  p384_to_generic(&r->Y, y);
  p384_to_generic(&r->Z, z);
}

// The calls to from/to_generic are needed for the case
// when BORINGSSL_HAS_UINT128 is undefined, i.e. p384_32.h fiat code is used;
// while OPENSSL_64_BIT is defined, i.e. BN_ULONG is uint64_t
static void ec_GFp_nistp384_mont_felem_to_bytes(
  const EC_GROUP *group, uint8_t *out, size_t *out_len, const EC_FELEM *in) {

  size_t len = BN_num_bytes(&group->field);
  EC_FELEM felem_tmp;
  p384_felem tmp;
  p384_from_generic(tmp, in);
  p384_felem_from_mont(tmp, tmp);
  p384_to_generic(&felem_tmp, tmp);

  bn_words_to_big_endian(out, len, felem_tmp.words, group->order->N.width);

  *out_len = len;
}

static int ec_GFp_nistp384_mont_felem_from_bytes(
  const EC_GROUP *group, EC_FELEM *out, const uint8_t *in, size_t len) {

  EC_FELEM felem_tmp;
  p384_felem tmp;
  // This function calls bn_cmp_words_consttime
  if (!ec_GFp_simple_felem_from_bytes(group, &felem_tmp, in, len)) {
    return 0;
  }
  p384_from_generic(tmp, &felem_tmp);
  p384_felem_to_mont(tmp, tmp);
  p384_to_generic(out, tmp);
  return 1;
}

static int ec_GFp_nistp384_cmp_x_coordinate(const EC_GROUP *group,
                                            const EC_JACOBIAN *p,
                                            const EC_SCALAR *r) {
  if (ec_GFp_simple_is_at_infinity(group, p)) {
    return 0;
  }

  // We wish to compare X/Z^2 with r. This is equivalent to comparing X with
  // r*Z^2. Note that X and Z are represented in Montgomery form, while r is
  // not.
  p384_felem Z2_mont;
  p384_from_generic(Z2_mont, &p->Z);
  p384_felem_mul(Z2_mont, Z2_mont, Z2_mont);

  p384_felem r_Z2;
  p384_from_scalar(r_Z2, r);  // r < order < p, so this is valid.
  p384_felem_mul(r_Z2, r_Z2, Z2_mont);

  p384_felem X;
  p384_from_generic(X, &p->X);
  p384_felem_from_mont(X, X);

  if (OPENSSL_memcmp(&r_Z2, &X, sizeof(r_Z2)) == 0) {
    return 1;
  }

  // During signing the x coefficient is reduced modulo the group order.
  // Therefore there is a small possibility, less than 2^189/2^384 = 1/2^195,
  // that group_order < p.x < p.
  // In that case, we need not only to compare against |r| but also to
  // compare against r+group_order.
  assert(group->field.width == group->order->N.width);
  EC_FELEM tmp;
  BN_ULONG carry =
      bn_add_words(tmp.words, r->words, group->order->N.d, group->field.width);
  if (carry == 0 &&
      bn_less_than_words(tmp.words, group->field.d, group->field.width)) {
    p384_from_generic(r_Z2, &tmp);
    p384_felem_mul(r_Z2, r_Z2, Z2_mont);
    if (OPENSSL_memcmp(&r_Z2, &X, sizeof(r_Z2)) == 0) {
      return 1;
    }
  }

  return 0;
}

// ----------------------------------------------------------------------------
//                    SCALAR MULTIPLICATION OPERATIONS
// ----------------------------------------------------------------------------
//
// The method for computing scalar products in functions:
//   - |ec_GFp_nistp384_point_mul|,
//   - |ec_GFp_nistp384_point_mul_base|,
//   - |ec_GFp_nistp384_point_mul_public|,
// is adapted from ECCKiila project (https://arxiv.org/abs/2007.11481).
//
// One difference from the processing in the ECCKiila project is the order of
// the digit processing in |ec_GFp_nistp384_point_mul_base|, where we end the
// processing with the least significant digit to be able to apply the
// analysis results detailed at the bottom of this file. In
// |ec_GFp_nistp384_point_mul_base| and |ec_GFp_nistp384_point_mul|, we
// considered using window size 7 based on that same analysis. However, the
// table size and performance measurements were more preferable for window
// size 5. The potential issue with different window sizes is that for some
// sizes, a scalar can be found such that a case of point doubling instead of
// point addition happens in the scalar multiplication. This would make
// the multiplication non constant-time. To the best of our knowledge this
// timing leak is not an exploitable issue because the only scalar for which
// the leak can happen is already known by the attacker. This is also provided
// that this recoding and window size are only used with ECDH and ECDSA
// protocols. Any other use would need to be analyzed to determine whether it is
// secure and the user should be aware of this side channel of a particular
// scalar value.
//
// OpenSSL has a similar analysis for P-521 implementation:
// https://github.com/openssl/openssl/blob/e9492d1cecf459261f1f5ac0eb03e9c631600537/crypto/ec/ecp_nistp521.c#L1318
//
// For detailed analysis of different window sizes see the bottom of this file.


// p384_get_bit returns the |i|-th bit in |in|
static crypto_word_t p384_get_bit(const EC_SCALAR *in, int i) {
  if (i < 0 || i >= 384) {
    return 0;
  }
#if defined(OPENSSL_64_BIT)
  assert(sizeof(BN_ULONG) == 8);
  return (in->words[i >> 6] >> (i & 63)) & 1;
#else
  assert(sizeof(BN_ULONG) == 4);
  return (in->words[i >> 5] >> (i & 31)) & 1;
#endif
}

// Constants for scalar encoding in the scalar multiplication functions.
#define P384_MUL_WSIZE        (5) // window size w
// Assert the window size is 5 because the pre-computed table in |p384_table.h|
// is generated for window size 5.
OPENSSL_STATIC_ASSERT(P384_MUL_WSIZE == 5,
    p384_scalar_mul_window_size_is_not_equal_to_five)

#define P384_MUL_TWO_TO_WSIZE (1 << P384_MUL_WSIZE)
#define P384_MUL_WSIZE_MASK   ((P384_MUL_TWO_TO_WSIZE << 1) - 1)

// Number of |P384_MUL_WSIZE|-bit windows in a 384-bit value
#define P384_MUL_NWINDOWS     ((384 + P384_MUL_WSIZE - 1)/P384_MUL_WSIZE)

// For the public point in |ec_GFp_nistp384_point_mul_public| function
// we use window size w = 5.
#define P384_MUL_PUB_WSIZE    (5)

// We keep only odd multiples in tables, hence the table size is (2^w)/2
#define P384_MUL_TABLE_SIZE     (P384_MUL_TWO_TO_WSIZE >> 1)
#define P384_MUL_PUB_TABLE_SIZE (1 << (P384_MUL_PUB_WSIZE - 1))

// Compute "regular" wNAF representation of a scalar, see
// Joye, Tunstall, "Exponent Recoding and Regular Exponentiation Algorithms",
// AfricaCrypt 2009, Alg 6.
// It forces an odd scalar and outputs digits in
// {\pm 1, \pm 3, \pm 5, \pm 7, \pm 9, ...}
// i.e. signed odd digits with _no zeroes_ -- that makes it "regular".
static void p384_felem_mul_scalar_rwnaf(int16_t *out, const EC_SCALAR *in) {
  int16_t window, d;

  window = (in->words[0] & P384_MUL_WSIZE_MASK) | 1;
  for (size_t i = 0; i < P384_MUL_NWINDOWS - 1; i++) {
    d = (window & P384_MUL_WSIZE_MASK) - P384_MUL_TWO_TO_WSIZE;
    out[i] = d;
    window = (window - d) >> P384_MUL_WSIZE;
    for (size_t j = 1; j <= P384_MUL_WSIZE; j++) {
      window += p384_get_bit(in, (i + 1) * P384_MUL_WSIZE + j) << j;
    }
  }
  out[P384_MUL_NWINDOWS - 1] = window;
}

// p384_select_point selects the |idx|-th projective point from the given
// precomputed table and copies it to |out| in constant time.
static void p384_select_point(p384_felem out[3],
                              size_t idx,
                              p384_felem table[][3],
                              size_t table_size) {
  OPENSSL_memset(out, 0, sizeof(p384_felem) * 3);
  for (size_t i = 0; i < table_size; i++) {
    p384_limb_t mismatch = i ^ idx;
    p384_felem_cmovznz(out[0], mismatch, table[i][0], out[0]);
    p384_felem_cmovznz(out[1], mismatch, table[i][1], out[1]);
    p384_felem_cmovznz(out[2], mismatch, table[i][2], out[2]);
  }
}

// p384_select_point_affine selects the |idx|-th affine point from
// the given precomputed table and copies it to |out| in constant-time.
static void p384_select_point_affine(p384_felem out[2],
                                     size_t idx,
                                     const p384_felem table[][2],
                                     size_t table_size) {
  OPENSSL_memset(out, 0, sizeof(p384_felem) * 2);
  for (size_t i = 0; i < table_size; i++) {
    p384_limb_t mismatch = i ^ idx;
    p384_felem_cmovznz(out[0], mismatch, table[i][0], out[0]);
    p384_felem_cmovznz(out[1], mismatch, table[i][1], out[1]);
  }
}

// Multiplication of a point by a scalar, r = [scalar]P.
// The product is computed with the use of a small table generated on-the-fly
// and the scalar recoded in the regular-wNAF representation.
//
// The precomputed (on-the-fly) table |p_pre_comp| holds 16 odd multiples of P:
//     [2i + 1]P for i in [0, 15].
// Computing the negation of a point P = (x, y) is relatively easy:
//     -P = (x, -y).
// So we may assume that instead of the above-mentioned 64, we have 128 points:
//     [\pm 1]P, [\pm 3]P, [\pm 5]P, ..., [\pm 31]P.
//
// The 384-bit scalar is recoded (regular-wNAF encoding) into 77 signed digits
// each of length 5 bits, as explained in the |p384_felem_mul_scalar_rwnaf|
// function. Namely,
//     scalar' = s_0 + s_1*2^5 + s_2*2^10 + ... + s_76*2^380,
// where digits s_i are in [\pm 1, \pm 3, ..., \pm 31]. Note that for an odd
// scalar we have that scalar = scalar', while in the case of an even
// scalar we have that scalar = scalar' - 1.
//
// The required product, [scalar]P, is computed by the following algorithm.
//     1. Initialize the accumulator with the point from |p_pre_comp|
//        corresponding to the most significant digit s_76 of the scalar.
//     2. For digits s_i starting from s_75 down to s_0:
//     3.   Double the accumulator 5 times. (note that doubling a point [a]P
//          seven times results in [2^5*a]P).
//     4.   Read from |p_pre_comp| the point corresponding to abs(s_i),
//          negate it if s_i is negative, and add it to the accumulator.
//
// Note: this function is constant-time.
static void ec_GFp_nistp384_point_mul(const EC_GROUP *group, EC_JACOBIAN *r,
                                      const EC_JACOBIAN *p,
                                      const EC_SCALAR *scalar) {

  p384_felem res[3] = {{0}, {0}, {0}}, tmp[3] = {{0}, {0}, {0}}, ftmp;

  // Table of multiples of P:  [2i + 1]P for i in [0, 15].
  p384_felem p_pre_comp[P384_MUL_TABLE_SIZE][3];

  // Set the first point in the table to P.
  p384_from_generic(p_pre_comp[0][0], &p->X);
  p384_from_generic(p_pre_comp[0][1], &p->Y);
  p384_from_generic(p_pre_comp[0][2], &p->Z);

  // Compute tmp = [2]P.
  p384_point_double(tmp[0], tmp[1], tmp[2],
                    p_pre_comp[0][0], p_pre_comp[0][1], p_pre_comp[0][2]);

  // Generate the remaining 15 multiples of P.
  for (size_t i = 1; i < P384_MUL_TABLE_SIZE; i++) {
    p384_point_add(p_pre_comp[i][0], p_pre_comp[i][1], p_pre_comp[i][2],
                   tmp[0], tmp[1], tmp[2], 0 /* both Jacobian */,
                   p_pre_comp[i - 1][0],
                   p_pre_comp[i - 1][1],
                   p_pre_comp[i - 1][2]);
  }

  // Recode the scalar.
  int16_t rnaf[P384_MUL_NWINDOWS] = {0};
  p384_felem_mul_scalar_rwnaf(rnaf, scalar);

  // Initialize the accumulator |res| with the table entry corresponding to
  // the most significant digit of the recoded scalar (note that this digit
  // can't be negative).
  int16_t idx = rnaf[P384_MUL_NWINDOWS - 1] >> 1;
  p384_select_point(res, idx, p_pre_comp, P384_MUL_TABLE_SIZE);

  // Process the remaining digits of the scalar.
  for (int i = P384_MUL_NWINDOWS - 2; i >= 0; i--) {
    // Double |res| 5 times in each iteration.
    for (size_t j = 0; j < P384_MUL_WSIZE; j++) {
      p384_point_double(res[0], res[1], res[2], res[0], res[1], res[2]);
    }

    int16_t d = rnaf[i];
    // is_neg = (d < 0) ? 1 : 0
    int16_t is_neg = (d >> 15) & 1;
    // d = abs(d)
    d = (d ^ -is_neg) + is_neg;

    idx = d >> 1;

    // Select the point to add, in constant time.
    p384_select_point(tmp, idx, p_pre_comp, P384_MUL_TABLE_SIZE);

    // Negate y coordinate of the point tmp = (x, y); ftmp = -y.
    p384_felem_opp(ftmp, tmp[1]);
    // Conditionally select y or -y depending on the sign of the digit |d|.
    p384_felem_cmovznz(tmp[1], is_neg, tmp[1], ftmp);

    // Add the point to the accumulator |res|.
    p384_point_add(res[0], res[1], res[2], res[0], res[1], res[2],
                   0 /* both Jacobian */, tmp[0], tmp[1], tmp[2]);

  }

  // Conditionally subtract P if the scalar is even, in constant-time.
  // First, compute |tmp| = |res| + (-P).
  p384_felem_copy(tmp[0], p_pre_comp[0][0]);
  p384_felem_opp(tmp[1], p_pre_comp[0][1]);
  p384_felem_copy(tmp[2], p_pre_comp[0][2]);
  p384_point_add(tmp[0], tmp[1], tmp[2], res[0], res[1], res[2],
                 0 /* both Jacobian */, tmp[0], tmp[1], tmp[2]);

  // Select |res| or |tmp| based on the |scalar| parity, in constant-time.
  p384_felem_cmovznz(res[0], scalar->words[0] & 1, tmp[0], res[0]);
  p384_felem_cmovznz(res[1], scalar->words[0] & 1, tmp[1], res[1]);
  p384_felem_cmovznz(res[2], scalar->words[0] & 1, tmp[2], res[2]);

  // Copy the result to the output.
  p384_to_generic(&r->X, res[0]);
  p384_to_generic(&r->Y, res[1]);
  p384_to_generic(&r->Z, res[2]);
}

// Include the precomputed table for the based point scalar multiplication.
#include "p384_table.h"

// Multiplication of the base point G of P-384 curve with the given scalar.
// The product is computed with the Comb method using the precomputed table
// |p384_g_pre_comp| from |p384_table.h| file and the regular-wNAF scalar
// encoding.
//
// The |p384_g_pre_comp| table has 20 sub-tables each holding 16 points:
//      0 :       [1]G,       [3]G,  ...,       [31]G
//      1 :  [1*2^20]G,  [3*2^20]G,  ...,  [31*2^20]G
//                         ...
//      i : [1*2^20i]G, [3*2^20i]G,  ..., [31*2^20i]G
//                         ...
//     19 :   [2^380]G, [3*2^380]G,  ..., [31*2^380]G.
// Computing the negation of a point P = (x, y) is relatively easy:
//     -P = (x, -y).
// So we may assume that for each sub-table we have 32 points instead of 16:
//     [\pm 1*2^20i]G, [\pm 3*2^20i]G, ..., [\pm 31*2^20i]G.
//
// The 384-bit |scalar| is recoded (regular-wNAF encoding) into 77 signed
// digits, each of length 5 bits, as explained in the
// |p384_felem_mul_scalar_rwnaf| function. Namely,
//     scalar' = s_0 + s_1*2^5 + s_2*2^10 + ... + s_76*2^380,
// where digits s_i are in [\pm 1, \pm 3, ..., \pm 31]. Note that for an odd
// scalar we have that scalar = scalar', while in the case of an even
// scalar we have that scalar = scalar' - 1.
//
// To compute the required product, [scalar]G, we may do the following.
// Group the recoded digits of the scalar in 4 groups:
//                                           |   corresponding multiples in
//                   digits                  |   the recoded representation
//    -------------------------------------------------------------------------
//    (0): {s_0, s_4,  s_8, ..., s_72, s_76} |  { 2^0, 2^20, ..., 2^360, 2^380}
//    (1): {s_1, s_5,  s_9, ..., s_73}       |  { 2^5, 2^25, ..., 2^365}
//    (2): {s_2, s_6, s_10, ..., s_74}       |  {2^10, 2^30, ..., 2^370}
//    (3): {s_3, s_7, s_11, ..., s_75}       |  {2^15, 2^35, ..., 2^375}
//         corresponding sub-table lookup    |  {  T0,   T1, ...,   T18,   T19}
//
// The group (0) digits correspond precisely to the multiples of G that are
// held in the 20 precomputed sub-tables, so we may simply read the appropriate
// points from the sub-tables and sum them all up (negating if needed, i.e., if
// a digit s_i is negative, we read the point corresponding to the abs(s_i) and
// negate it before adding it to the sum).
// The remaining three groups (1), (2), and (3), correspond to the multiples
// of G from the sub-tables multiplied additionally by 2^5, 2^10, and 2^15,
// respectively. Therefore, for these groups we may read the appropriate points
// from the table, double them 5, 10, or 15 times, respectively, and add them
// to the final result.
//
// To minimize the number of required doubling operations we process the digits
// of the scalar from left to right. In other words, the algorithm is:
//   1. Read the points corresponding to the group (3) digits from the table
//      and add them to an accumulator.
//   2. Double the accumulator 5 times.
//   3. Repeat steps 1. and 2. for groups (2) and (1),
//      and perform step 1. for group (0).
//   4. If the scalar is even subtract G from the accumulator.
//
// Note: this function is constant-time.
static void ec_GFp_nistp384_point_mul_base(const EC_GROUP *group,
                                           EC_JACOBIAN *r,
                                           const EC_SCALAR *scalar) {

  p384_felem res[3] = {{0}, {0}, {0}}, tmp[3] = {{0}, {0}, {0}}, ftmp;
  int16_t rnaf[P384_MUL_NWINDOWS] = {0};

  // Recode the scalar.
  p384_felem_mul_scalar_rwnaf(rnaf, scalar);

  // Process the 4 groups of digits starting from group (3) down to group (0).
  for (int i = 3; i >= 0; i--) {
    // Double |res| 5 times in each iteration, except in the first one.
    for (int j = 0; i != 3 && j < P384_MUL_WSIZE; j++) {
      p384_point_double(res[0], res[1], res[2], res[0], res[1], res[2]);
    }

    // Process the digits in the current group from the most to the least
    // significant one (this is a requirement to ensure that the case of point
    // doubling can't happen).
    // For group (3) we process digits s_75 to s_3, for group (2) s_74 to s_2,
    // group (1) s_73 to s_1, and for group (0) s_76 to s_0.
    const size_t start_idx = ((P384_MUL_NWINDOWS - i - 1)/4)*4 + i;

    for (int j = start_idx; j >= 0; j -= 4) {
      // For each digit |d| in the current group read the corresponding point
      // from the table and add it to |res|. If |d| is negative, negate
      // the point before adding it to |res|.
      int16_t d = rnaf[j];
      // is_neg = (d < 0) ? 1 : 0
      int16_t is_neg = (d >> 15) & 1;
      // d = abs(d)
      d = (d ^ -is_neg) + is_neg;

      int16_t idx = d >> 1;

      // Select the point to add, in constant time.
      p384_select_point_affine(tmp, idx, p384_g_pre_comp[j / 4],
                               P384_MUL_TABLE_SIZE);

      // Negate y coordinate of the point tmp = (x, y); ftmp = -y.
      p384_felem_opp(ftmp, tmp[1]);
      // Conditionally select y or -y depending on the sign of the digit |d|.
      p384_felem_cmovznz(tmp[1], is_neg, tmp[1], ftmp);

      // Add the point to the accumulator |res|.
      // Note that the points in the pre-computed table are given with affine
      // coordinates. The point addition function computes a sum of two points,
      // either both given in projective, or one in projective and the other one
      // in affine coordinates. The |mixed| flag indicates the latter option,
      // in which case we set the third coordinate of the second point to one.
      p384_point_add(res[0], res[1], res[2], res[0], res[1], res[2],
                     1 /* mixed */, tmp[0], tmp[1], p384_felem_one);
    }
  }

  // Conditionally subtract G if the scalar is even, in constant-time.
  // First, compute |tmp| = |res| + (-G).
  p384_felem_copy(tmp[0], p384_g_pre_comp[0][0][0]);
  p384_felem_opp(tmp[1], p384_g_pre_comp[0][0][1]);
  p384_point_add(tmp[0], tmp[1], tmp[2], res[0], res[1], res[2],
                 1 /* mixed */, tmp[0], tmp[1], p384_felem_one);

  // Select |res| or |tmp| based on the |scalar| parity.
  p384_felem_cmovznz(res[0], scalar->words[0] & 1, tmp[0], res[0]);
  p384_felem_cmovznz(res[1], scalar->words[0] & 1, tmp[1], res[1]);
  p384_felem_cmovznz(res[2], scalar->words[0] & 1, tmp[2], res[2]);

  // Copy the result to the output.
  p384_to_generic(&r->X, res[0]);
  p384_to_generic(&r->Y, res[1]);
  p384_to_generic(&r->Z, res[2]);
}

// Computes [g_scalar]G + [p_scalar]P, where G is the base point of the P-384
// curve, and P is the given point |p|.
//
// Both scalar products are computed by the same "textbook" wNAF method,
// with w = 5 for g_scalar and w = 5 for p_scalar.
// For the base point G product we use the first sub-table of the precomputed
// table |p384_g_pre_comp| from |p384_table.h| file, while for P we generate
// |p_pre_comp| table on-the-fly. The tables hold the first 16 odd multiples
// of G or P:
//     g_pre_comp = {[1]G, [3]G, ..., [31]G},
//     p_pre_comp = {[1]P, [3]P, ..., [31]P}.
// Computing the negation of a point P = (x, y) is relatively easy:
//     -P = (x, -y).
// So we may assume that we also have the negatives of the points in the tables.
//
// The 384-bit scalars are recoded by the textbook wNAF method to 385 digits,
// where a digit is either a zero or an odd integer in [-31, 31]. The method
// guarantees that each non-zero digit is followed by at least four
// zeroes.
//
// The result [g_scalar]G + [p_scalar]P is computed by the following algorithm:
//     1. Initialize the accumulator with the point-at-infinity.
//     2. For i starting from 384 down to 0:
//     3.   Double the accumulator (doubling can be skipped while the
//          accumulator is equal to the point-at-infinity).
//     4.   Read from |p_pre_comp| the point corresponding to the i-th digit of
//          p_scalar, negate it if the digit is negative, and add it to the
//          accumulator.
//     5.   Read from |g_pre_comp| the point corresponding to the i-th digit of
//          g_scalar, negate it if the digit is negative, and add it to the
//          accumulator.
//
// Note: this function is NOT constant-time.
static void ec_GFp_nistp384_point_mul_public(const EC_GROUP *group,
                                             EC_JACOBIAN *r,
                                             const EC_SCALAR *g_scalar,
                                             const EC_JACOBIAN *p,
                                             const EC_SCALAR *p_scalar) {

  p384_felem res[3] = {{0}, {0}, {0}}, two_p[3] = {{0}, {0}, {0}}, ftmp;

  // Table of multiples of P:  [2i + 1]P for i in [0, 15].
  p384_felem p_pre_comp[P384_MUL_PUB_TABLE_SIZE][3];

  // Set the first point in the table to P.
  p384_from_generic(p_pre_comp[0][0], &p->X);
  p384_from_generic(p_pre_comp[0][1], &p->Y);
  p384_from_generic(p_pre_comp[0][2], &p->Z);

  // Compute two_p = [2]P.
  p384_point_double(two_p[0], two_p[1], two_p[2],
                    p_pre_comp[0][0], p_pre_comp[0][1], p_pre_comp[0][2]);

  // Generate the remaining 15 multiples of P.
  for (size_t i = 1; i < P384_MUL_PUB_TABLE_SIZE; i++) {
    p384_point_add(p_pre_comp[i][0], p_pre_comp[i][1], p_pre_comp[i][2],
                   two_p[0], two_p[1], two_p[2], 0 /* both Jacobian */,
                   p_pre_comp[i - 1][0],
                   p_pre_comp[i - 1][1],
                   p_pre_comp[i - 1][2]);
  }

  // Recode the scalars.
  int8_t p_wnaf[385] = {0}, g_wnaf[385] = {0};
  ec_compute_wNAF(group, p_wnaf, p_scalar, 384, P384_MUL_PUB_WSIZE);
  ec_compute_wNAF(group, g_wnaf, g_scalar, 384, P384_MUL_WSIZE);

  // In the beginning res is set to point-at-infinity, so we set the flag.
  int16_t res_is_inf = 1;
  int16_t d, is_neg, idx;

  for (int i = 384; i >= 0; i--) {

    // If |res| is point-at-infinity there is no point in doubling so skip it.
    if (!res_is_inf) {
      p384_point_double(res[0], res[1], res[2], res[0], res[1], res[2]);
    }

    // Process the p_scalar digit.
    d = p_wnaf[i];
    if (d != 0) {
      is_neg = d < 0 ? 1 : 0;
      idx = (is_neg) ? (-d - 1) >> 1 : (d - 1) >> 1;

      if (res_is_inf) {
        // If |res| is point-at-infinity there is no need to add the new point,
        // we can simply copy it.
        p384_felem_copy(res[0], p_pre_comp[idx][0]);
        p384_felem_copy(res[1], p_pre_comp[idx][1]);
        p384_felem_copy(res[2], p_pre_comp[idx][2]);
        res_is_inf = 0;
      } else {
        // Otherwise, add to the accumulator either the point at position idx
        // in the table or its negation.
        if (is_neg) {
          p384_felem_opp(ftmp, p_pre_comp[idx][1]);
        } else {
          p384_felem_copy(ftmp, p_pre_comp[idx][1]);
        }
        p384_point_add(res[0], res[1], res[2],
                       res[0], res[1], res[2],
                       0 /* both Jacobian */,
                       p_pre_comp[idx][0], ftmp, p_pre_comp[idx][2]);
      }
    }

    // Process the g_scalar digit.
    d = g_wnaf[i];
    if (d != 0) {
      is_neg = d < 0 ? 1 : 0;
      idx = (is_neg) ? (-d - 1) >> 1 : (d - 1) >> 1;

      if (res_is_inf) {
        // If |res| is point-at-infinity there is no need to add the new point,
        // we can simply copy it.
        p384_felem_copy(res[0], p384_g_pre_comp[0][idx][0]);
        p384_felem_copy(res[1], p384_g_pre_comp[0][idx][1]);
        p384_felem_copy(res[2], p384_felem_one);
        res_is_inf = 0;
      } else {
        // Otherwise, add to the accumulator either the point at position idx
        // in the table or its negation.
        if (is_neg) {
          p384_felem_opp(ftmp, p384_g_pre_comp[0][idx][1]);
        } else {
          p384_felem_copy(ftmp, p384_g_pre_comp[0][idx][1]);
        }
        // Add the point to the accumulator |res|.
        // Note that the points in the pre-computed table are given with affine
        // coordinates. The point addition function computes a sum of two points,
        // either both given in projective, or one in projective and one in
        // affine coordinates. The |mixed| flag indicates the latter option,
        // in which case we set the third coordinate of the second point to one.
        p384_point_add(res[0], res[1], res[2],
                       res[0], res[1], res[2],
                       1 /* mixed */,
                       p384_g_pre_comp[0][idx][0], ftmp, p384_felem_one);
      }
    }
  }

  // Copy the result to the output.
  p384_to_generic(&r->X, res[0]);
  p384_to_generic(&r->Y, res[1]);
  p384_to_generic(&r->Z, res[2]);
}

DEFINE_METHOD_FUNCTION(EC_METHOD, EC_GFp_nistp384_method) {
  out->group_init = ec_GFp_mont_group_init;
  out->group_finish = ec_GFp_mont_group_finish;
  out->group_set_curve = ec_GFp_mont_group_set_curve;
  out->point_get_affine_coordinates =
      ec_GFp_nistp384_point_get_affine_coordinates;
  out->jacobian_to_affine_batch =
      ec_GFp_mont_jacobian_to_affine_batch;     // needed for TrustToken tests
  out->add = ec_GFp_nistp384_add;
  out->dbl = ec_GFp_nistp384_dbl;
  out->mul = ec_GFp_nistp384_point_mul;
  out->mul_base = ec_GFp_nistp384_point_mul_base;
  out->mul_public = ec_GFp_nistp384_point_mul_public;
  out->mul_batch = ec_GFp_mont_mul_batch;       // needed for TrustToken tests
  out->mul_public_batch = ec_GFp_mont_mul_public_batch;
  out->init_precomp = ec_GFp_mont_init_precomp; // needed for TrustToken tests
  out->mul_precomp = ec_GFp_mont_mul_precomp;   // needed for TrustToken tests
  out->felem_mul = ec_GFp_mont_felem_mul;
  out->felem_sqr = ec_GFp_mont_felem_sqr;
  out->felem_to_bytes = ec_GFp_nistp384_mont_felem_to_bytes;
  out->felem_from_bytes = ec_GFp_nistp384_mont_felem_from_bytes;
  out->felem_reduce = ec_GFp_mont_felem_reduce; // needed for ECTest.HashToCurve
  out->felem_exp = ec_GFp_mont_felem_exp;       // needed for ECTest.HashToCurve
  out->scalar_inv0_montgomery = ec_simple_scalar_inv0_montgomery;
  out->scalar_to_montgomery_inv_vartime =
      ec_simple_scalar_to_montgomery_inv_vartime;
  out->cmp_x_coordinate = ec_GFp_nistp384_cmp_x_coordinate;
}

// ----------------------------------------------------------------------------
//  Analysis of the doubling case occurrence in the Joye-Tunstall recoding:
//  p384_felem_mul_scalar_rwnaf()
// ----------------------------------------------------------------------------
//
// The JT scalar recoding is Algorithm 6: (Odd) Signed-Digit Recoding Algorithm in
// Joye, Tunstall, "Exponent Recoding and Regular Exponentiation Algorithms",
// AfricaCrypt 2009, available from
// https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.477.1245&rep=rep1&type=pdf
//
// We write the algorithm using variables similar to those used in the code and
// in the proof detailed in util.c (t_i in the algorithm below is d in
// p384_felem_mul_scalar_rwnaf()):
//
// Input: k: odd scalar, where k = (b_{l-1}, ..., b_1, b_0) in binary form,
//        w: window width
// Output: k = (t_{h-1}, ..., t_1, t_0)
//         with t_i \in {\pm 1, \pm 3, ..., \pm (2^{w} - 1)},
//         h = ceil(t/w), i.e. t_i are positive and negative odd digits
//         which absolute value is less than (2^{w} - 1).
// i := 0
// j := 0
// while (k > 2^w):
//   window := (b_{j+w}, ..., b_j)   # (w+1)-bit window in k where
//                                   # the least significant bit is b_j
//   t_i := window - 2^w
//   k := k - t_i
//   k := k / 2^w          # k >> w
//   i += 1
//   j += w
// t_{h-1} := k
//
// Note that if b_{j+w} = 0, t_i will be negative;
// otherwise, if b_{j+w} = 1, t_i will be positive.
//
// The algorithm recodes the least (w+1) bits into a (odd) digit in the range
// [-(2^{w}-1), (2^{w}-1)] by subtracting 2^w from that digit and adding it back
// to the remaining bits of the scalar. This ensures that, after the w-bit right
// shift, the next least significant bit is 1, i.e. next digit is odd.
//
// In the following we will show that the non-trivial doubling case in
// single-point left-to-right windowed (or m-ary, m = 2^w) scalar multiplication
// may occur if and only if the (2^w)th bit of the group order is 1.  This only
// holds if the scalar is fully reduced and the group order is a prime that is
// much larger than 2^{w+1}.
//
// PROOF:
//
// Let n be the group order. Let l be the number of bits needed to represent n.
// Assume there exists some 0 <= k < n such that signed w-bit windowed
// multiplication hits the doubling case.
//
// Windowed multiplication consists of iterating over the digits t_i defined
// above by the algorithm from most to least significant. At iteration i
// (for i = ..., 3w, 2w, w, 0, starting from the most significant window), we:
//
//  1. Double the accumulator A, w times. Let A_i be the value of A at this
//     point, and it corresponds to a value [a_i]P.
//
//  2. Set A to T_i + A_i, where T_i is a precomputed multiple of P, [t_i]P

// From the algorithm steps we can see that the current digit
// t_i = (b_{w+i} ... b_i) - 2^w, b_i = 1     => -2^w < t_i < 2^w, t_i: odd
// which can also be written using C notation as
// t_i = [(k >> i) & ((1<<(w+1)) - 1)] - (1 << w)     -- (1)
//
// and the accumulator value
// a_i = b_{l-1} ... b_{i+w+1} 1
// when written as C notation
// a_i = (k >> (i+w+1)) << (w+1)) + (1 << w)          -- (2)
//
// Similarly to the recoding in util.c, a_i is bounded by
// 0 <= a_i < n + 2^w. Additionally, a_i can only be zero if b_(i+w-1) and up
// are all zero. (Note this implies a non-trivial P + (-P) is unreachable for
// all groups. That would imply the subsequent a_i is zero, which means all
// terms thus far were zero.)
//
// Let j be the index such that A_j = T_j ≠ ∞. We have a_j = t_j (mod n). We now
// determine the value of a_j - t_j, which must be divisible by n.
// Our bounds on a_j and t_j imply a_j - t_j is 0 or n.
// If it is 0, a_j = t_j. However, 2^w divides a_j and -2^w < t_i < 2^w, so this
// can only happen if a_j = t_j = 0, which is a trivial doubling.
// Therefore, a_j - t_j = n.
//
// Now we determine j. Suppose j > 0. w divides j, so j >= w. Then,
//
//   n = a_j - t_j = (k >> (j+w+1)) << (w+1)) + (1 << w) - t_j
//                 = k/2^j + 2^w - t_j
//                 < n/2^w + 2^w + 2^w-1
//
// n is much larger than 2^{w+1}, so this is impossible. Thus, j = 0: only the
// final addition may hit the doubling case.
//
// Finally, we consider bit patterns for n and k. Divide k into k_H + k_M + k_L
// such that k_H is the contribution from b_(l-1) .. b_{w+1},
// k_M is the contribution from b_w,
// and k_L is the contribution from b_(w-1) ... b_0.
// That is:
//
// - 2^{w+1} divides k_H
// - k_M is 0 or 2^w
// - 0 <= k_L < 2^w
//
// Divide n into n_H + n_M + n_L similarly.
// From (1) and (2), we have
//
// t_0 = (k_M + k_L) - 2^w
// a_0 = k_H + 2^w
//
// We try to find t_0 and a_0 such that
//
//               n = a_0 - t_0
// n_H + n_M + n_L = k_H + 2^w - (k_M + k_L - 2^w)
//                 = k_H + 2^{w+1} - (k_M + k_L)
//
// We know that k_H <= n_H.
//
// If k_H < n_H, then k_H <= n_H - 2^{w+1} (Note that 2^{w+1} divides both k_H
// and n_H). Then we would have
//
// n_H + n_M + n_L <= n_H - 2^{w+1} + 2^{w+1} - (k_M + k_L)
//       n_M + n_L <= - (k_M + k_L)
//
// Contradiction. Thus,
//
//          k_H = n_H                    -- (3)
// => n_M + n_L = 2^{w+1} - (k_M + k_L)  -- (4)
//
// We also have n > k; hence,
// n_M + n_L > k_M + k_L                 -- (5)
//
// For (3), (4) and (5) to hold,
// n_M = 2^w, k_M = 0.
//
// Otherwise, if n_M = 0 and k_M = 0
// n_L = 2^{w+1} - k_L
// n_L >= 2^{w+1} - (2^w - 1)
// n_L >= 2^w + 1
// Contradiction since n_L < 2^w.
//
// And if n_M = 0 and k_M = 2^w, (5) would not hold.
//
// Since n_M = 2^w, n_L >= 1, k_L >= 1, from (4) we have
//  k_M + k_L = 2^{w+1} - (n_M + n_L)
//           <= 2^{w+1} - 2^w - 1
//           <= 2^{w} - 1
// => k_M = 0
//
// Putting this together, from the group order of the curve, n, we can construct
// the scalar, k, that would incur a doubling in the last iteration as:
//
// if n_M = 2^w,
// k_H = n_H and
// k_M + k_L = 2^{w+1} - (n_M + n_L)
//
// COMMON CURVES:
//
// The group orders for common curves end in the following bit patterns:
//
//   P-521: ...00001001; w = 4, 5, 6, 7 are okay
//   P-384: ...01110011; w = 2, 3, 7    are okay
//   P-256: ...01010001; w = 2, 3, 5, 7 are okay
//
//
// CAN DOUBLING OCCUR IN RIGHT-TO-LEFT ALGORITHMS OR COMB ALGORITHMS?
//
// This question was answered empirically for P-384 group order n, w = 5,
// by asking:
// Is there a value d_76, such that
// - d_{76} * 2^{380} - a_{76} = n and
// - d_{76} * 2^{380} + a_{76} = k < n ?
//
// Setting
// d_76 = 0xf
// a_76 = (d_76 << 380) - n =
// -0xfffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
// k = a_76 + (d_76 << 380) =
// 0xe00000000000000000000000000000000000000000000000389cb27e0bc8d220a7e5f24db74f58851313e695333ad68d
//
// n-k =
// 0x1fffffffffffffffffffffffffffffffffffffffffffffff8ec69b03e86e5bbeb0341b6491614ef5d9d832d5998a52e6
// => 0 < k < n
//
// -(1<<380)-a_76 = -0x389cb27e0bc8d220a7e5f24db74f58851313e695333ad68d
// => -2^380 < a_76 < 2^380
//
// This shows that such a k value exists.
//
// This resulted in modifying the comb algorithm used in
// ec_GFp_nistp384_point_mul_base() to proceed in a left-to-right fashion in
// order to add the least significant digit in the last iteration.
//
// We can probably construct values of k that would incur doubling for whenever
// any of the higher digits, t_{j-1}, (down to the middle digit, roughly) is
// added last. This is because the upper half of the group order of P-384 is all
// 1s, therefore we can find a value k < n, having a 0 at the (j*w)th bit which
// would become 1 in the recoding of t_j (being the least significant bit in
// t_j) and making t_{j-1} a negative digit. Hence, the difference between the
// accumulator value containing all digits and t_{j-1} * 2^{(j-1)*w} can be n.
//
// This was tested as follows in Python for j = 75, i.e. the second last digit:
// let that digit's value be the smallest possible value for w = 5, i.e. -31
//  d_75 = -31
// # assuming the accumulator contains the most significant digit d_76
//  a = n + (d_75 << 375); hex(a)
// '0xf07fffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973L'
//  hex(n)
// '0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973L'
//  k = a + (d_75 << 375); hex(k)
// '0xe0ffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973L'
//
// # Checks
//  hex(n-k)
// '0x1f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000L'
//  hex(n - (a - (d_75 << 375)))
// '0x0L'
// => n > k
//    and a value k was found such that when adding d_75 last, the difference
//    between the accumulator a and (d_75 << 375) is n
//
//
// ----------------------------------------------------------------------------
//  Python code showing the doubling case occurrence in the Joye-Tunstall
//  recoding:
// ----------------------------------------------------------------------------
//
// from array import *
//
// # P-384 group order
// n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC7634D81F4372DDF581A0DB248B0A77AECEC196ACCC52973
//
// # k value that causes a doubling case in left-to-right reconstruction
// k = 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc5294d
// # k value that causes a doubling case in right-to-left reconstruction
// k_r2l = 0xe00000000000000000000000000000000000000000000000389cb27e0bc8d220a7e5f24db74f58851313e695333ad68d
//
//
// def recode(k, w):
//     rec = array('i', [])
//     while k > (2 ** w):
//         window = k & ((2 ** (w + 1)) - 1)
//         d = window - (2 ** w)
//         k = k - d
//         k = (k >> w)
//         rec.append(d)
//     rec.append(k)
//     return rec
//
// # Rebuild k from the recoded scalar proceeding from left to right
// def rebuild_l2r(rec, w):
//     l = rec.buffer_info()[1]  # length of the recoded scalar array
//     # initialise accumulator
//     a = rec[l-1]
//     # for i from l-2 downto 0
//     for i in range(l-2,-1,-1):
//         a = (a << w)
//         if (a - rec[i]) == n:
//             print("L2R Doubling case: ")
//             print("    i =", i, " digit =", hex(rec[i]))
//             print("    a =", hex(a))
//         a += rec[i]
//     return a
//
// # Rebuild k from the recoded scalar proceeding from right to left
// def rebuild_r2l(rec, w):
//     l = rec.buffer_info()[1]  # length of the recoded scalar array
//     # initialise accumulator
//     a = rec[0]
//     # for i from 1 to l-1
//     for i in range(1,l):
//         shifted_d = rec[i] << (w*i)
//         if (shifted_d - a) == n:
//             print("R2L Doubling case: ")
//             print("    i =", i, " digit =", hex(rec[i]))
//             print("    a =", hex(a))
//         a += shifted_d
//     return a
//
// def test_recode():
//     w = 5
//
//     # Left-to-right recoding of k which causes a doubling case
//     assert k < n
//     print("k = ", hex(k))
//     # recode k
//     rec_k = recode(k,w)
//     # print(rec_k)
//     print("Digits of the recoded scalar:")
//     for a in rec_k:
//         print(hex(a), end=', ')
//     print()
//     # rebuild k
//     out_k = rebuild_l2r(rec_k, w)
//     if out_k != k:
//         print("ERROR: rebuilt value is different from recoded value")
//     print()
//
//     # Right-to-left recoding of k_r2l which causes a doubling case
//     assert k_r2l < n
//     print("k = ", hex(k_r2l))
//     # recode k_r2l
//     rec_k_r2l = recode(k_r2l,w)
//     # print(rec_k_r2l)
//     print("Digits of the recoded scalar:")
//     for a in rec_k_r2l:
//         print(hex(a), end=', ')
//     print()
//     # rebuild k_r2l
//     out_k_r2l = rebuild_r2l(rec_k_r2l, w)
//     if out_k_r2l != k_r2l:
//         print("ERROR: rebuilt R2L value is different from recoded value")
//     print()
//
// test_recode()
// '''
// Output:
// -------
// k =  0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc5294d
// Digits of the recoded scalar:
// -0x13, -0x15, -0x15, -0x15, -0x13, 0x7, 0xb, 0xd, -0x7, 0x1, 0x1b, -0x7, 0xf, 0x1d, -0x3, -0xb, 0x11, -0x1b, -0xd, 0x5, -0x5, -0x19, 0x9, -0x1d, -0x7, 0x1b, 0x17, -0x5, 0x13, -0x5, -0xf, 0x1f, -0x1f, 0xd, -0xd, -0x19, 0x17, 0x3, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0xf,
// L2R Doubling case:
//     i = 0  digit = -0x13
//     a = 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52960
//
// k =  0xe00000000000000000000000000000000000000000000000389cb27e0bc8d220a7e5f24db74f58851313e695333ad68d
// Digits of the recoded scalar:
// -0x13, 0x15, 0x15, 0x15, 0x13, -0x7, -0xb, -0xd, 0x7, -0x1, -0x1b, 0x7, -0xf, -0x1d, 0x3, 0xb, -0x11, 0x1b, 0xd, -0x5, 0x5, 0x19, -0x9, 0x1d, 0x7, -0x1b, -0x17, 0x5, -0x13, 0x5, 0xf, -0x1f, 0x1f, -0xd, 0xd, 0x19, -0x17, -0x3, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, -0x1f, 0xf,
// R2L Doubling case:
//     i = 76  digit = 0xf
//     a = -0xfffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
// '''
//
#endif // !defined(OPENSSL_SMALL)
