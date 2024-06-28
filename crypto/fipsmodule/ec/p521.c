/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0 OR ISC
------------------------------------------------------------------------------------
*/

// Implementation of P-521 that uses Fiat-crypto for the field arithmetic
// found in third_party/fiat, similarly to p256.c and p384.c

#include <openssl/bn.h>
#include <openssl/ec.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include "../bn/internal.h"
#include "../cpucap/internal.h"
#include "../delocate.h"
#include "internal.h"
#include "ec_nistp.h"

#if !defined(OPENSSL_SMALL)

#if defined(EC_NISTP_USE_S2N_BIGNUM)
#  include "../../../third_party/s2n-bignum/include/s2n-bignum_aws-lc.h"
#else
#  if defined(EC_NISTP_USE_64BIT_LIMB)
#    include "../../../third_party/fiat/p521_64.h"
#  else
#    include "../../../third_party/fiat/p521_32.h"
#  endif
#endif

#if defined(EC_NISTP_USE_S2N_BIGNUM)

#define P521_NLIMBS (9)

typedef uint64_t p521_limb_t;
typedef uint64_t p521_felem[P521_NLIMBS]; // field element

static const p521_limb_t p521_felem_one[P521_NLIMBS] = {
    0x0000000000000001, 0x0000000000000000,
    0x0000000000000000, 0x0000000000000000,
    0x0000000000000000, 0x0000000000000000,
    0x0000000000000000, 0x0000000000000000,
    0x0000000000000000};

// The field characteristic p.
static const p521_limb_t p521_felem_p[P521_NLIMBS] = {
    0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff,
    0x1ff};

// s2n-bignum implementation of field arithmetic
#define p521_felem_add(out, in0, in1)   bignum_add_p521(out, in0, in1)
#define p521_felem_sub(out, in0, in1)   bignum_sub_p521(out, in0, in1)
#define p521_felem_opp(out, in0)        bignum_neg_p521(out, in0)
#define p521_felem_to_bytes(out, in0)   bignum_tolebytes_p521(out, in0)
#define p521_felem_from_bytes(out, in0) bignum_fromlebytes_p521(out, in0)
#define p521_felem_mul(out, in0, in1)   bignum_mul_p521_selector(out, in0, in1)
#define p521_felem_sqr(out, in0)        bignum_sqr_p521_selector(out, in0)

#else // EC_NISTP_USE_S2N_BIGNUM

#if defined(EC_NISTP_USE_64BIT_LIMB)

// In the 64-bit case Fiat-crypto represents a field element by 9 58-bit digits.
#define P521_NLIMBS (9)

typedef uint64_t p521_felem[P521_NLIMBS]; // field element
typedef uint64_t p521_limb_t;

// One in Fiat-crypto's representation (58-bit digits).
static const p521_limb_t p521_felem_one[P521_NLIMBS] = {
    0x0000000000000001, 0x0000000000000000,
    0x0000000000000000, 0x0000000000000000,
    0x0000000000000000, 0x0000000000000000,
    0x0000000000000000, 0x0000000000000000,
    0x0000000000000000};

// The field characteristic p in Fiat-crypto's representation (58-bit digits).
static const p521_limb_t p521_felem_p[P521_NLIMBS] = {
    0x03ffffffffffffff, 0x03ffffffffffffff,
    0x03ffffffffffffff, 0x03ffffffffffffff,
    0x03ffffffffffffff, 0x03ffffffffffffff,
    0x03ffffffffffffff, 0x03ffffffffffffff,
    0x01ffffffffffffff};

#else  // 64BIT; else 32BIT

// In the 32-bit case Fiat-crypto represents a field element by 19 digits
// with the following bit sizes:
// [28, 27, 28, 27, 28, 27, 27, 28, 27, 28, 27, 28, 27, 27, 28, 27, 28, 27, 27].
#define P521_NLIMBS (19)

typedef uint32_t p521_felem[P521_NLIMBS]; // field element
typedef uint32_t p521_limb_t;

// One in Fiat-crypto's representation.
static const p521_limb_t p521_felem_one[P521_NLIMBS] = {
    0x0000001, 0x0000000, 0x0000000, 0x0000000,
    0x0000000, 0x0000000, 0x0000000, 0x0000000,
    0x0000000, 0x0000000, 0x0000000, 0x0000000,
    0x0000000, 0x0000000, 0x0000000, 0x0000000,
    0x0000000, 0x0000000, 0x0000000};

// The field characteristic p in Fiat-crypto's representation.
static const p521_limb_t p521_felem_p[P521_NLIMBS] = {
    0xfffffff, 0x7ffffff, 0xfffffff, 0x7ffffff,
    0xfffffff, 0x7ffffff, 0x7ffffff, 0xfffffff,
    0x7ffffff, 0xfffffff, 0x7ffffff, 0xfffffff,
    0x7ffffff, 0x7ffffff, 0xfffffff, 0x7ffffff,
    0xfffffff, 0x7ffffff, 0x7ffffff};
#endif  // 64BIT

// Fiat-crypto implementation of field arithmetic
#define p521_felem_add(out, in0, in1)   fiat_secp521r1_carry_add(out, in0, in1)
#define p521_felem_sub(out, in0, in1)   fiat_secp521r1_carry_sub(out, in0, in1)
#define p521_felem_opp(out, in0)        fiat_secp521r1_carry_opp(out, in0)
#define p521_felem_mul(out, in0, in1)   fiat_secp521r1_carry_mul(out, in0, in1)
#define p521_felem_sqr(out, in0)        fiat_secp521r1_carry_square(out, in0)
#define p521_felem_to_bytes(out, in0)   fiat_secp521r1_to_bytes(out, in0)
#define p521_felem_from_bytes(out, in0) fiat_secp521r1_from_bytes(out, in0)

#endif // EC_NISTP_USE_S2N_BIGNUM

static p521_limb_t p521_felem_nz(const p521_limb_t in1[P521_NLIMBS]) {
  p521_limb_t is_not_zero = 0;
  for (int i = 0; i < P521_NLIMBS; i++) {
    is_not_zero |= in1[i];
  }

#if defined(EC_NISTP_USE_S2N_BIGNUM)
  return is_not_zero;
#else
  // Fiat-crypto functions may return p (the field characteristic)
  // instead of 0 in some cases, so we also check for that.
  p521_limb_t is_not_p = 0;
  for (int i = 0; i < P521_NLIMBS; i++) {
    is_not_p |= (in1[i] ^ p521_felem_p[i]);
  }

  return ~(constant_time_is_zero_w(is_not_p) |
           constant_time_is_zero_w(is_not_zero));
#endif
}

static void p521_felem_copy(p521_limb_t out[P521_NLIMBS],
                            const p521_limb_t in1[P521_NLIMBS]) {
  for (size_t i = 0; i < P521_NLIMBS; i++) {
    out[i] = in1[i];
  }
}

static void p521_felem_cmovznz(p521_limb_t out[P521_NLIMBS],
                               p521_limb_t t,
                               const p521_limb_t z[P521_NLIMBS],
                               const p521_limb_t nz[P521_NLIMBS]) {
  p521_limb_t mask = constant_time_is_zero_w(t);
  for (size_t i = 0; i < P521_NLIMBS; i++) {
    out[i] = constant_time_select_w(mask, z[i], nz[i]);
  }
}

// NOTE: the input and output are in little-endian representation.
static void p521_from_generic(p521_felem out, const EC_FELEM *in) {
#ifdef OPENSSL_BIG_ENDIAN
  uint8_t tmp[P521_EC_FELEM_BYTES];
  bn_words_to_little_endian(tmp, P521_EC_FELEM_BYTES, in->words, P521_EC_FELEM_WORDS);
  p521_felem_from_bytes(out, tmp);
#else
  p521_felem_from_bytes(out, (const uint8_t *)in->words);
#endif
}

// NOTE: the input and output are in little-endian representation.
static void p521_to_generic(EC_FELEM *out, const p521_felem in) {
  // |p521_felem_to_bytes| function will write the result to the first 66 bytes
  // of |out| which is exactly how many bytes are needed to represent a 521-bit
  // element.
  // The number of BN_ULONGs to represent a 521-bit value is 9 and 17, when
  // BN_ULONG is 64-bit and 32-bit, respectively. Nine 64-bit BN_ULONGs
  // translate to 72 bytes, which means that we have to make sure that the
  // extra 6 bytes are zeroed out. To avoid confusion over 32 vs. 64 bit
  // systems and Fiat's vs. ours representation we zero out the whole element.
#ifdef OPENSSL_BIG_ENDIAN
  uint8_t tmp[P521_EC_FELEM_BYTES];
  p521_felem_to_bytes(tmp, in);
  bn_little_endian_to_words(out->words, P521_EC_FELEM_WORDS, tmp, P521_EC_FELEM_BYTES);
#else
  OPENSSL_memset((uint8_t*)out->words, 0, sizeof(out->words));
  // Convert the element to bytes.
  p521_felem_to_bytes((uint8_t *)out->words, in);
#endif
}

// Finite field inversion using Fermat Little Theorem.
// The code is autogenerated by the ECCKiila project:
//   https://arxiv.org/abs/2007.11481
static void p521_felem_inv(p521_felem output, const p521_felem t1) {
    /* temporary variables */
    p521_felem acc, t2, t4, t8, t16, t32, t64;
    p521_felem t128, t256, t512, t516, t518, t519;

    p521_felem_sqr(acc, t1);
    p521_felem_mul(t2, acc, t1);
    p521_felem_sqr(acc, t2);
    p521_felem_sqr(acc, acc);
    p521_felem_mul(t4, acc, t2);
    p521_felem_sqr(acc, t4);
    for (int i = 0; i < 3; i++) {
      p521_felem_sqr(acc, acc);
    }
    p521_felem_mul(t8, acc, t4);
    p521_felem_sqr(acc, t8);
    for (int i = 0; i < 7; i++) {
      p521_felem_sqr(acc, acc);
    }
    p521_felem_mul(t16, acc, t8);
    p521_felem_sqr(acc, t16);
    for (int i = 0; i < 15; i++) {
      p521_felem_sqr(acc, acc);
    }
    p521_felem_mul(t32, acc, t16);
    p521_felem_sqr(acc, t32);
    for (int i = 0; i < 31; i++) {
      p521_felem_sqr(acc, acc);
    }
    p521_felem_mul(t64, acc, t32);
    p521_felem_sqr(acc, t64);
    for (int i = 0; i < 63; i++) {
      p521_felem_sqr(acc, acc);
    }
    p521_felem_mul(t128, acc, t64);
    p521_felem_sqr(acc, t128);
    for (int i = 0; i < 127; i++) {
      p521_felem_sqr(acc, acc);
    }
    p521_felem_mul(t256, acc, t128);
    p521_felem_sqr(acc, t256);
    for (int i = 0; i < 255; i++) {
      p521_felem_sqr(acc, acc);
    }
    p521_felem_mul(t512, acc, t256);
    p521_felem_sqr(acc, t512);
    for (int i = 0; i < 3; i++) {
      p521_felem_sqr(acc, acc);
    }
    p521_felem_mul(t516, acc, t4);
    p521_felem_sqr(acc, t516);
    p521_felem_sqr(acc, acc);
    p521_felem_mul(t518, acc, t2);
    p521_felem_sqr(acc, t518);
    p521_felem_mul(t519, acc, t1);
    p521_felem_sqr(acc, t519);
    p521_felem_sqr(acc, acc);
    p521_felem_mul(output, acc, t1);
}

static void p521_point_double(p521_felem x_out,
                              p521_felem y_out,
                              p521_felem z_out,
                              const p521_felem x_in,
                              const p521_felem y_in,
                              const p521_felem z_in) {
  ec_nistp_point_double(p521_methods(), x_out, y_out, z_out, x_in, y_in, z_in);
}

// p521_point_add calculates (x1, y1, z1) + (x2, y2, z2)
//
// The method is taken from:
//   http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#addition-add-2007-bl
// adapted for mixed addition (z2 = 1, or z2 = 0 for the point at infinity).
//
// Coq transcription and correctness proof:
// <https://github.com/davidben/fiat-crypto/blob/c7b95f62b2a54b559522573310e9b487327d219a/src/Curves/Weierstrass/Jacobian.v#L467>
// <https://github.com/davidben/fiat-crypto/blob/c7b95f62b2a54b559522573310e9b487327d219a/src/Curves/Weierstrass/Jacobian.v#L544>
static void p521_point_add(p521_felem x3, p521_felem y3, p521_felem z3,
                           const p521_felem x1,
                           const p521_felem y1,
                           const p521_felem z1,
                           const int mixed,
                           const p521_felem x2,
                           const p521_felem y2,
                           const p521_felem z2) {
  ec_nistp_point_add(p521_methods(), x3, y3, z3, x1, y1, z1, mixed, x2, y2, z2);
}

#if defined(EC_NISTP_USE_S2N_BIGNUM)
DEFINE_METHOD_FUNCTION(ec_nistp_meth, p521_methods) {
    out->felem_num_limbs = P521_NLIMBS;
    out->felem_add = bignum_add_p521;
    out->felem_sub = bignum_sub_p521;
    out->felem_mul = bignum_mul_p521_selector;
    out->felem_sqr = bignum_sqr_p521_selector;
    out->felem_nz  = p521_felem_nz;
    out->point_dbl = p521_point_double;
    out->point_add = p521_point_add;
}
#else
DEFINE_METHOD_FUNCTION(ec_nistp_meth, p521_methods) {
    out->felem_num_limbs = P521_NLIMBS;
    out->felem_add = fiat_secp521r1_carry_add;
    out->felem_sub = fiat_secp521r1_carry_sub;
    out->felem_mul = fiat_secp521r1_carry_mul;
    out->felem_sqr = fiat_secp521r1_carry_square;
    out->felem_nz  = p521_felem_nz;
    out->point_dbl = p521_point_double;
    out->point_add = p521_point_add;
}
#endif

// OPENSSL EC_METHOD FUNCTIONS

// Takes the Jacobian coordinates (X, Y, Z) of a point and returns:
//   (X', Y') = (X/Z^2, Y/Z^3).
static int ec_GFp_nistp521_point_get_affine_coordinates(
    const EC_GROUP *group, const EC_JACOBIAN *point,
    EC_FELEM *x_out, EC_FELEM *y_out) {

  if (constant_time_declassify_w(ec_GFp_simple_is_at_infinity(group, point))) {
    OPENSSL_PUT_ERROR(EC, EC_R_POINT_AT_INFINITY);
    return 0;
  }

  p521_felem z1, z2;
  p521_from_generic(z1, &point->Z);
  p521_felem_inv(z2, z1);
  p521_felem_sqr(z2, z2);

  if (x_out != NULL) {
    p521_felem x;
    p521_from_generic(x, &point->X);
    p521_felem_mul(x, x, z2);
    p521_to_generic(x_out, x);
  }

  if (y_out != NULL) {
    p521_felem y;
    p521_from_generic(y, &point->Y);
    p521_felem_sqr(z2, z2);  // z^-4
    p521_felem_mul(y, y, z1);   // y * z
    p521_felem_mul(y, y, z2);   // y * z^-3
    p521_to_generic(y_out, y);
  }

  return 1;
}

static void ec_GFp_nistp521_add(const EC_GROUP *group, EC_JACOBIAN *r,
                                const EC_JACOBIAN *a, const EC_JACOBIAN *b) {
  p521_felem x1, y1, z1, x2, y2, z2;
  p521_from_generic(x1, &a->X);
  p521_from_generic(y1, &a->Y);
  p521_from_generic(z1, &a->Z);
  p521_from_generic(x2, &b->X);
  p521_from_generic(y2, &b->Y);
  p521_from_generic(z2, &b->Z);
  p521_point_add(x1, y1, z1, x1, y1, z1, 0 /* both Jacobian */, x2, y2, z2);
  p521_to_generic(&r->X, x1);
  p521_to_generic(&r->Y, y1);
  p521_to_generic(&r->Z, z1);
}

static void ec_GFp_nistp521_dbl(const EC_GROUP *group, EC_JACOBIAN *r,
                                const EC_JACOBIAN *a) {
  p521_felem x, y, z;
  p521_from_generic(x, &a->X);
  p521_from_generic(y, &a->Y);
  p521_from_generic(z, &a->Z);
  p521_point_double(x, y, z, x, y, z);
  p521_to_generic(&r->X, x);
  p521_to_generic(&r->Y, y);
  p521_to_generic(&r->Z, z);
}

// ----------------------------------------------------------------------------
//                    SCALAR MULTIPLICATION OPERATIONS
// ----------------------------------------------------------------------------
//
// The method for computing scalar products in functions:
//   - |ec_GFp_nistp521_point_mul|,
//   - |ec_GFp_nistp521_point_mul_base|,
//   - |ec_GFp_nistp521_point_mul_public|,
// is adapted from ECCKiila project (https://arxiv.org/abs/2007.11481).
// The main difference is that we use a window of size 7 instead of 5 for the
// first two functions. The potential issue with window sizes is that for some
// sizes a scalar can be found such that a case of point doubling instead of
// point addition happens in the scalar multiplication. This would make the
// multiplication non constant-time. Therefore, such window sizes have to be
// avoided. The windows size of 7 is chosen based on analysis analogous to
// the one in |ec_GFp_nistp_recode_scalar_bits| function in |util.c| file.
// See the analysis at the bottom of this file.
//
// Moreover, the order in which the digits of the scalar are processed in
// |ec_GFp_nistp521_point_mul_base| is different from the ECCKiila project, to
// ensure that the least significant digit is processed last which together
// with the window size 7 guarantees constant-time execution of the function.
//
// Another difference is that in |ec_GFp_nistp521_point_mul_public| function we
// use window size 5 for the public point and 7 for the base point. Here it is
// ok to use window of size 5 since the scalar is public and therefore the
// function doesn't have to be constant-time.
//
// The precomputed table of base point multiples is generated by the code in
// |make_tables.go| script.

// Constants for scalar encoding in the scalar multiplication functions.
#define P521_MUL_WSIZE        (5) // window size w
// Assert the window size is 5 because the pre-computed table in |p521_table.h|
// is generated for window size 5.
OPENSSL_STATIC_ASSERT(P521_MUL_WSIZE == 5,
    p521_scalar_mul_window_size_is_not_equal_to_five)

#define P521_MUL_TWO_TO_WSIZE (1 << P521_MUL_WSIZE)

// Number of |P521_MUL_WSIZE|-bit windows in a 521-bit value
#define P521_MUL_NWINDOWS     ((521 + P521_MUL_WSIZE - 1)/P521_MUL_WSIZE)

// For the public point in |ec_GFp_nistp521_point_mul_public| function
// we use window size equal to 5.
#define P521_MUL_PUB_WSIZE    (5)

// We keep only odd multiples in tables, hence the table size is (2^w)/2
#define P521_MUL_TABLE_SIZE     (P521_MUL_TWO_TO_WSIZE >> 1)
#define P521_MUL_PUB_TABLE_SIZE (1 << (P521_MUL_PUB_WSIZE - 1))

// p521_select_point selects the |idx|-th projective point from the given
// precomputed table and copies it to |out| in constant time.
static void p521_select_point(p521_felem out[3],
                              size_t idx,
                              p521_felem table[][3],
                              size_t table_size) {
  OPENSSL_memset(out, 0, sizeof(p521_felem) * 3);
  for (size_t i = 0; i < table_size; i++) {
    p521_limb_t mismatch = i ^ idx;
    p521_felem_cmovznz(out[0], mismatch, table[i][0], out[0]);
    p521_felem_cmovznz(out[1], mismatch, table[i][1], out[1]);
    p521_felem_cmovznz(out[2], mismatch, table[i][2], out[2]);
  }
}

// p521_select_point_affine selects the |idx|-th affine point from
// the given precomputed table and copies it to |out| in constant-time.
static void p521_select_point_affine(p521_felem out[2],
                                     size_t idx,
                                     const p521_felem table[][2],
                                     size_t table_size) {
  OPENSSL_memset(out, 0, sizeof(p521_felem) * 2);
  for (size_t i = 0; i < table_size; i++) {
    p521_limb_t mismatch = i ^ idx;
    p521_felem_cmovznz(out[0], mismatch, table[i][0], out[0]);
    p521_felem_cmovznz(out[1], mismatch, table[i][1], out[1]);
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
// So we may assume that instead of the above-mentioned 16, we have 32 points:
//     [\pm 1]P, [\pm 3]P, [\pm 5]P, ..., [\pm 31]P.
//
// The 521-bit scalar is recoded (regular-wNAF encoding) into 105 signed digits
// each of length 5 bits, as explained in the |p521_felem_mul_scalar_rwnaf|
// function. Namely,
//     scalar' = s_0 + s_1*2^5 + s_2*2^10 + ... + s_104*2^520,
// where digits s_i are in [\pm 1, \pm 3, ..., \pm 31]. Note that for an odd
// scalar we have that scalar = scalar', while in the case of an even
// scalar we have that scalar = scalar' - 1.
//
// The required product, [scalar]P, is computed by the following algorithm.
//     1. Initialize the accumulator with the point from |p_pre_comp|
//        corresponding to the most significant digit s_104 of the scalar.
//     2. For digits s_i starting from s_104 down to s_0:
//     3.   Double the accumulator 5 times. (note that doubling a point [a]P
//          seven times results in [2^5*a]P).
//     4.   Read from |p_pre_comp| the point corresponding to abs(s_i),
//          negate it if s_i is negative, and add it to the accumulator.
//
// Note: this function is constant-time.
static void ec_GFp_nistp521_point_mul(const EC_GROUP *group, EC_JACOBIAN *r,
                                      const EC_JACOBIAN *p,
                                      const EC_SCALAR *scalar) {

  p521_felem res[3] = {{0}, {0}, {0}}, tmp[3] = {{0}, {0}, {0}}, ftmp;

  // Table of multiples of P:  [2i + 1]P for i in [0, 15].
  p521_felem p_pre_comp[P521_MUL_TABLE_SIZE][3];

  // Set the first point in the table to P.
  p521_from_generic(p_pre_comp[0][0], &p->X);
  p521_from_generic(p_pre_comp[0][1], &p->Y);
  p521_from_generic(p_pre_comp[0][2], &p->Z);

  // Compute tmp = [2]P.
  p521_point_double(tmp[0], tmp[1], tmp[2],
                    p_pre_comp[0][0], p_pre_comp[0][1], p_pre_comp[0][2]);

  // Generate the remaining 15 multiples of P.
  for (size_t i = 1; i < P521_MUL_TABLE_SIZE; i++) {
    p521_point_add(p_pre_comp[i][0], p_pre_comp[i][1], p_pre_comp[i][2],
                   tmp[0], tmp[1], tmp[2], 0 /* both Jacobian */,
                   p_pre_comp[i - 1][0],
                   p_pre_comp[i - 1][1],
                   p_pre_comp[i - 1][2]);
  }

  // Recode the scalar.
  int16_t rnaf[P521_MUL_NWINDOWS] = {0};
  scalar_rwnaf(rnaf, P521_MUL_WSIZE, scalar, 521);

  // Initialize the accumulator |res| with the table entry corresponding to
  // the most significant digit of the recoded scalar (note that this digit
  // can't be negative).
  int16_t idx = rnaf[P521_MUL_NWINDOWS - 1] >> 1;
  p521_select_point(res, idx, p_pre_comp, P521_MUL_TABLE_SIZE);

  // Process the remaining digits of the scalar.
  for (int i = P521_MUL_NWINDOWS - 2; i >= 0; i--) {
    // Double |res| 7 times in each iteration.
    for (size_t j = 0; j < P521_MUL_WSIZE; j++) {
      p521_point_double(res[0], res[1], res[2], res[0], res[1], res[2]);
    }

    int16_t d = rnaf[i];
    // is_neg = (d < 0) ? 1 : 0
    int16_t is_neg = (d >> 15) & 1;
    // d = abs(d)
    d = (d ^ -is_neg) + is_neg;

    idx = d >> 1;

    // Select the point to add, in constant time.
    p521_select_point(tmp, idx, p_pre_comp, P521_MUL_TABLE_SIZE);

    // Negate y coordinate of the point tmp = (x, y); ftmp = -y.
    p521_felem_opp(ftmp, tmp[1]);
    // Conditionally select y or -y depending on the sign of the digit |d|.
    p521_felem_cmovznz(tmp[1], is_neg, tmp[1], ftmp);

    // Add the point to the accumulator |res|.
    p521_point_add(res[0], res[1], res[2], res[0], res[1], res[2],
                   0 /* both Jacobian */, tmp[0], tmp[1], tmp[2]);

  }

  // Conditionally subtract P if the scalar is even, in constant-time.
  // First, compute |tmp| = |res| + (-P).
  p521_felem_copy(tmp[0], p_pre_comp[0][0]);
  p521_felem_opp(tmp[1], p_pre_comp[0][1]);
  p521_felem_copy(tmp[2], p_pre_comp[0][2]);
  p521_point_add(tmp[0], tmp[1], tmp[2], res[0], res[1], res[2],
                 0 /* both Jacobian */, tmp[0], tmp[1], tmp[2]);

  // Select |res| or |tmp| based on the |scalar| parity, in constant-time.
  p521_felem_cmovznz(res[0], scalar->words[0] & 1, tmp[0], res[0]);
  p521_felem_cmovznz(res[1], scalar->words[0] & 1, tmp[1], res[1]);
  p521_felem_cmovznz(res[2], scalar->words[0] & 1, tmp[2], res[2]);

  // Copy the result to the output.
  p521_to_generic(&r->X, res[0]);
  p521_to_generic(&r->Y, res[1]);
  p521_to_generic(&r->Z, res[2]);
}

// Include the precomputed table for the based point scalar multiplication.
#include "p521_table.h"

// Multiplication of the base point G of P-521 curve with the given scalar.
// The product is computed with the Comb method using the precomputed table
// |p521_g_pre_comp| from |p521_table.h| file and the regular-wNAF scalar
// encoding.
//
// The |p521_g_pre_comp| table has 27 sub-tables each holding 16 points:
//      0 :       [1]G,       [3]G,  ...,       [31]G
//      1 :  [1*2^20]G,  [3*2^20]G,  ...,  [31*2^20]G
//                         ...
//      i : [1*2^20i]G, [3*2^20i]G,  ..., [31*2^20i]G
//                         ...
//     26 :   [2^520]G, [3*2^520]G,  ..., [31*2^520]G
// Computing the negation of a point P = (x, y) is relatively easy:
//     -P = (x, -y).
// So we may assume that for each sub-table we have 32 points instead of 16:
//     [\pm 1*2^20i]G, [\pm 3*2^20i]G, ..., [\pm 31*2^20i]G.
//
// The 521-bit |scalar| is recoded (regular-wNAF encoding) into 105 signed
// digits, each of length 5 bits, as explained in the
// |p521_felem_mul_scalar_rwnaf| function. Namely,
//     scalar' = s_0 + s_1*2^5 + s_2*2^10 + ... + s_104*2^520,
// where digits s_i are in [\pm 1, \pm 3, ..., \pm 31]. Note that for an odd
// scalar we have that scalar = scalar', while in the case of an even
// scalar we have that scalar = scalar' - 1.
//
// To compute the required product, [scalar]G, we may do the following.
// Group the recoded digits of the scalar in 4 groups:
//                                            |   corresponding multiples in
//                  digits                    |   the recoded representation
//   -------------------------------------------------------------------------
//   (0): {s_0, s_4,  s_8, ..., s_100, s_104} |  { 2^0, 2^20, ..., 2^500, 2^520}
//   (1): {s_1, s_5,  s_9, ..., s_101}        |  { 2^5, 2^25, ..., 2^505}
//   (2): {s_2, s_6, s_10, ..., s_102}        |  {2^10, 2^30, ..., 2^510}
//   (3): {s_3, s_7, s_11, ..., s_103}        |  {2^15, 2^35, ..., 2^515}
//        corresponding sub-table lookup      |  {  T0,   T1, ...,   T25,   T26}
//
// The group (0) digits correspond precisely to the multiples of G that are
// held in the 27 precomputed sub-tables, so we may simply read the appropriate
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
static void ec_GFp_nistp521_point_mul_base(const EC_GROUP *group,
                                           EC_JACOBIAN *r,
                                           const EC_SCALAR *scalar) {

  p521_felem res[3] = {{0}, {0}, {0}}, tmp[3] = {{0}, {0}, {0}}, ftmp;
  int16_t rnaf[P521_MUL_NWINDOWS] = {0};

  // Recode the scalar.
  scalar_rwnaf(rnaf, P521_MUL_WSIZE, scalar, 521);

  // Process the 4 groups of digits starting from group (3) down to group (0).
  for (int i = 3; i >= 0; i--) {
    // Double |res| 5 times in each iteration, except in the first one.
    for (size_t j = 0; i != 3 && j < P521_MUL_WSIZE; j++) {
      p521_point_double(res[0], res[1], res[2], res[0], res[1], res[2]);
    }

    // Process the digits in the current group from the most to the least
    // significant one (this is a requirement to ensure that the case of point
    // doubling can't happen).
    // For group (3) we process digits s_103 to s_3, for group (2) s_102 to s_2,
    // group (1) s_101 to s_1, and for group (0) s_104 to s_0.
    const size_t start_idx = ((P521_MUL_NWINDOWS - i - 1)/4)*4 + i;

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
      p521_select_point_affine(tmp, idx, p521_g_pre_comp[j / 4],
                               P521_MUL_TABLE_SIZE);

      // Negate y coordinate of the point tmp = (x, y); ftmp = -y.
      p521_felem_opp(ftmp, tmp[1]);
      // Conditionally select y or -y depending on the sign of the digit |d|.
      p521_felem_cmovznz(tmp[1], is_neg, tmp[1], ftmp);

      // Add the point to the accumulator |res|.
      // Note that the points in the pre-computed table are given with affine
      // coordinates. The point addition function computes a sum of two points,
      // either both given in projective, or one in projective and the other one
      // in affine coordinates. The |mixed| flag indicates the latter option,
      // in which case we set the third coordinate of the second point to one.
      p521_point_add(res[0], res[1], res[2], res[0], res[1], res[2],
                     1 /* mixed */, tmp[0], tmp[1], p521_felem_one);
    }
  }

  // Conditionally subtract G if the scalar is even, in constant-time.
  // First, compute |tmp| = |res| + (-G).
  p521_felem_copy(tmp[0], p521_g_pre_comp[0][0][0]);
  p521_felem_opp(tmp[1], p521_g_pre_comp[0][0][1]);
  p521_point_add(tmp[0], tmp[1], tmp[2], res[0], res[1], res[2],
                 1 /* mixed */, tmp[0], tmp[1], p521_felem_one);

  // Select |res| or |tmp| based on the |scalar| parity.
  p521_felem_cmovznz(res[0], scalar->words[0] & 1, tmp[0], res[0]);
  p521_felem_cmovznz(res[1], scalar->words[0] & 1, tmp[1], res[1]);
  p521_felem_cmovznz(res[2], scalar->words[0] & 1, tmp[2], res[2]);

  // Copy the result to the output.
  p521_to_generic(&r->X, res[0]);
  p521_to_generic(&r->Y, res[1]);
  p521_to_generic(&r->Z, res[2]);
}

// Computes [g_scalar]G + [p_scalar]P, where G is the base point of the P-521
// curve, and P is the given point |p|.
//
// Both scalar products are computed by the same "textbook" wNAF method,
// with w = 5 for g_scalar and w = 5 for p_scalar.
// For the base point G product we use the first sub-table of the precomputed
// table |p521_g_pre_comp| from |p521_table.h| file, while for P we generate
// |p_pre_comp| table on-the-fly. The tables hold the first 16 odd multiples
// of G or P:
//     g_pre_comp = {[1]G, [3]G, ..., [31]G},
//     p_pre_comp = {[1]P, [3]P, ..., [31]P}.
// Computing the negation of a point P = (x, y) is relatively easy:
//     -P = (x, -y).
// So we may assume that we also have the negatives of the points in the tables.
//
// The 521-bit scalars are recoded by the textbook wNAF method to 522 digits,
// where a digit is either a zero or an odd integer in [-31, 31]. The method
// guarantees that each non-zero digit is followed by at least four
// zeroes.
//
// The result [g_scalar]G + [p_scalar]P is computed by the following algorithm:
//     1. Initialize the accumulator with the point-at-infinity.
//     2. For i starting from 521 down to 0:
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
static void ec_GFp_nistp521_point_mul_public(const EC_GROUP *group,
                                             EC_JACOBIAN *r,
                                             const EC_SCALAR *g_scalar,
                                             const EC_JACOBIAN *p,
                                             const EC_SCALAR *p_scalar) {

  p521_felem res[3] = {{0}, {0}, {0}}, two_p[3] = {{0}, {0}, {0}}, ftmp;

  // Table of multiples of P:  [2i + 1]P for i in [0, 15].
  p521_felem p_pre_comp[P521_MUL_PUB_TABLE_SIZE][3];

  // Set the first point in the table to P.
  p521_from_generic(p_pre_comp[0][0], &p->X);
  p521_from_generic(p_pre_comp[0][1], &p->Y);
  p521_from_generic(p_pre_comp[0][2], &p->Z);

  // Compute two_p = [2]P.
  p521_point_double(two_p[0], two_p[1], two_p[2],
                    p_pre_comp[0][0], p_pre_comp[0][1], p_pre_comp[0][2]);

  // Generate the remaining 15 multiples of P.
  for (size_t i = 1; i < P521_MUL_PUB_TABLE_SIZE; i++) {
    p521_point_add(p_pre_comp[i][0], p_pre_comp[i][1], p_pre_comp[i][2],
                   two_p[0], two_p[1], two_p[2], 0 /* both Jacobian */,
                   p_pre_comp[i - 1][0],
                   p_pre_comp[i - 1][1],
                   p_pre_comp[i - 1][2]);
  }

  // Recode the scalars.
  int8_t p_wnaf[522] = {0}, g_wnaf[522] = {0};
  ec_compute_wNAF(group, p_wnaf, p_scalar, 521, P521_MUL_PUB_WSIZE);
  ec_compute_wNAF(group, g_wnaf, g_scalar, 521, P521_MUL_WSIZE);

  // In the beginning res is set to point-at-infinity, so we set the flag.
  int16_t res_is_inf = 1;
  int16_t d, is_neg, idx;

  for (int i = 521; i >= 0; i--) {

    // If |res| is point-at-infinity there is no point in doubling so skip it.
    if (!res_is_inf) {
      p521_point_double(res[0], res[1], res[2], res[0], res[1], res[2]);
    }

    // Process the p_scalar digit.
    d = p_wnaf[i];
    if (d != 0) {
      is_neg = d < 0 ? 1 : 0;
      idx = (is_neg) ? (-d - 1) >> 1 : (d - 1) >> 1;

      if (res_is_inf) {
        // If |res| is point-at-infinity there is no need to add the new point,
        // we can simply copy it.
        p521_felem_copy(res[0], p_pre_comp[idx][0]);
        p521_felem_copy(res[1], p_pre_comp[idx][1]);
        p521_felem_copy(res[2], p_pre_comp[idx][2]);
        res_is_inf = 0;
      } else {
        // Otherwise, add to the accumulator either the point at position idx
        // in the table or its negation.
        if (is_neg) {
          p521_felem_opp(ftmp, p_pre_comp[idx][1]);
        } else {
          p521_felem_copy(ftmp, p_pre_comp[idx][1]);
        }
        p521_point_add(res[0], res[1], res[2],
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
        p521_felem_copy(res[0], p521_g_pre_comp[0][idx][0]);
        p521_felem_copy(res[1], p521_g_pre_comp[0][idx][1]);
        p521_felem_copy(res[2], p521_felem_one);
        res_is_inf = 0;
      } else {
        // Otherwise, add to the accumulator either the point at position idx
        // in the table or its negation.
        if (is_neg) {
          p521_felem_opp(ftmp, p521_g_pre_comp[0][idx][1]);
        } else {
          p521_felem_copy(ftmp, p521_g_pre_comp[0][idx][1]);
        }
        // Add the point to the accumulator |res|.
        // Note that the points in the pre-computed table are given with affine
        // coordinates. The point addition function computes a sum of two points,
        // either both given in projective, or one in projective and one in
        // affine coordinates. The |mixed| flag indicates the latter option,
        // in which case we set the third coordinate of the second point to one.
        p521_point_add(res[0], res[1], res[2],
                       res[0], res[1], res[2],
                       1 /* mixed */,
                       p521_g_pre_comp[0][idx][0], ftmp, p521_felem_one);
      }
    }
  }

  // Copy the result to the output.
  p521_to_generic(&r->X, res[0]);
  p521_to_generic(&r->Y, res[1]);
  p521_to_generic(&r->Z, res[2]);
}

static void ec_GFp_nistp521_felem_mul(const EC_GROUP *group, EC_FELEM *r,
                                      const EC_FELEM *a, const EC_FELEM *b) {
  p521_felem felem1, felem2, felem3;
  p521_from_generic(felem1, a);
  p521_from_generic(felem2, b);
  p521_felem_mul(felem3, felem1, felem2);
  p521_to_generic(r, felem3);
}

static void ec_GFp_nistp521_felem_sqr(const EC_GROUP *group, EC_FELEM *r,
                                      const EC_FELEM *a) {
  p521_felem felem1, felem2;
  p521_from_generic(felem1, a);
  p521_felem_sqr(felem2, felem1);
  p521_to_generic(r, felem2);
}

DEFINE_METHOD_FUNCTION(EC_METHOD, EC_GFp_nistp521_method) {
  out->point_get_affine_coordinates =
      ec_GFp_nistp521_point_get_affine_coordinates;
  out->add = ec_GFp_nistp521_add;
  out->dbl = ec_GFp_nistp521_dbl;
  out->mul = ec_GFp_nistp521_point_mul;
  out->mul_base = ec_GFp_nistp521_point_mul_base;
  out->mul_public = ec_GFp_nistp521_point_mul_public;
  out->felem_mul = ec_GFp_nistp521_felem_mul;
  out->felem_sqr = ec_GFp_nistp521_felem_sqr;
  out->felem_to_bytes = ec_GFp_simple_felem_to_bytes;
  out->felem_from_bytes = ec_GFp_simple_felem_from_bytes;
  out->scalar_inv0_montgomery = ec_simple_scalar_inv0_montgomery;
  out->scalar_to_montgomery_inv_vartime =
      ec_simple_scalar_to_montgomery_inv_vartime;
  out->cmp_x_coordinate = ec_GFp_simple_cmp_x_coordinate;
}

// ----------------------------------------------------------------------------
//  Analysis of the doubling case occurrence in the Joye-Tunstall recoding:
//  see the analysis at the bottom of the |p384.c| file.
#endif // !defined(OPENSSL_SMALL)
