// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// In this file we will implement elliptic curve point operations for
// NIST curves P-256, P-384, and P-521. The idea is to implement the operations
// in a generic way such that the code can be reused instead of having
// a separate implementation for each of the curves. We implement:
//   1. point addition,
//   2. point doubling,
//   3. scalar multiplication of a base point,
//   4. scalar multiplication of an arbitrary point,
//   5. scalar multiplication of a base and an arbitrary point.
//
// Matrix of what has been done so far:
// 
// | op | P-521 | P-384 | P-256 |
// |----------------------------|
// | 1. |   x   |   x   |   x*  |
// | 2. |   x   |   x   |   x*  |
// | 3. |       |       |       |
// | 4. |       |       |       |
// | 5. |       |       |       |
//  * For P-256, only the Fiat-crypto implementation in p256.c is replaced. 

#include "ec_nistp.h"

// Some of the functions below need temporary field element variables.
// To avoid dynamic allocation we define nistp_felem type to have the maximum
// size possible (which is currently P-521 curve). The values are hard-coded
// for the moment, this will be fixed when we migrate the whole P-521
// implementation to ec_nistp.c.
#if defined(EC_NISTP_USE_64BIT_LIMB)
#define NISTP_FELEM_MAX_NUM_OF_LIMBS (9)
#else
#define NISTP_FELEM_MAX_NUM_OF_LIMBS (19)
#endif
typedef ec_nistp_felem_limb ec_nistp_felem[NISTP_FELEM_MAX_NUM_OF_LIMBS];

// Conditional copy in constant-time (out = t == 0 ? z : nz).
static void cmovznz(ec_nistp_felem_limb *out,
                    size_t num_limbs,
                    ec_nistp_felem_limb t,
                    const ec_nistp_felem_limb *z,
                    const ec_nistp_felem_limb *nz) {
  ec_nistp_felem_limb mask = constant_time_is_zero_w(t);
  for (size_t i = 0; i < num_limbs; i++) {
    out[i] = constant_time_select_w(mask, z[i], nz[i]);
  }
}

// Group operations
// ----------------
//
// Building on top of the field operations we have the operations on the
// elliptic curve group itself. Points on the curve are represented in Jacobian
// coordinates.
//
// ec_nistp_point_double calculates 2*(x_in, y_in, z_in)
//
// The method is based on:
//   http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html#doubling-dbl-2001-b
// for which there is a Coq transcription and correctness proof:
//   <https://github.com/mit-plv/fiat-crypto/blob/79f8b5f39ed609339f0233098dee1a3c4e6b3080/src/Curves/Weierstrass/Jacobian.v#L93>
//   <https://github.com/mit-plv/fiat-crypto/blob/79f8b5f39ed609339f0233098dee1a3c4e6b3080/src/Curves/Weierstrass/Jacobian.v#L201>
//
// However, we slighty changed the computation for efficiency (see the full
// explanation within the function body), which makes the Coq proof above
// not applicable to our implementation.
// TODO(awslc): Write a Coq correctness proof for our version of the algorithm.
//
// Outputs can equal corresponding inputs, i.e., x_out == x_in is allowed;
// while x_out == y_in is not (maybe this works, but it's not tested).
void ec_nistp_point_double(const ec_nistp_meth *ctx,
                           ec_nistp_felem_limb *x_out,
                           ec_nistp_felem_limb *y_out,
                           ec_nistp_felem_limb *z_out,
                           const ec_nistp_felem_limb *x_in,
                           const ec_nistp_felem_limb *y_in,
                           const ec_nistp_felem_limb *z_in) {
  ec_nistp_felem delta, gamma, beta, ftmp, ftmp2, tmptmp, alpha, fourbeta;
  // delta = z^2
  ctx->felem_sqr(delta, z_in);
  // gamma = y^2
  ctx->felem_sqr(gamma, y_in);
  // beta = x*gamma
  ctx->felem_mul(beta, x_in, gamma);

  // alpha = 3*(x-delta)*(x+delta)
  ctx->felem_sub(ftmp, x_in, delta);
  ctx->felem_add(ftmp2, x_in, delta);

  ctx->felem_add(tmptmp, ftmp2, ftmp2);
  ctx->felem_add(ftmp2, ftmp2, tmptmp);
  ctx->felem_mul(alpha, ftmp, ftmp2);

  // x' = alpha^2 - 8*beta
  ctx->felem_sqr(x_out, alpha);
  ctx->felem_add(fourbeta, beta, beta);
  ctx->felem_add(fourbeta, fourbeta, fourbeta);
  ctx->felem_add(tmptmp, fourbeta, fourbeta);
  ctx->felem_sub(x_out, x_out, tmptmp);

  // z' = (y + z)^2 - gamma - delta
  // The following calculation differs from the Coq proof cited above.
  // The proof is for:
  //   add(delta, gamma, delta);
  //   add(ftmp, y_in, z_in);
  //   square(z_out, ftmp);
  //   sub(z_out, z_out, delta);
  // Our operations sequence is a bit more efficient because it saves us
  // a certain number of conditional moves.
  ctx->felem_add(ftmp, y_in, z_in);
  ctx->felem_sqr(z_out, ftmp);
  ctx->felem_sub(z_out, z_out, gamma);
  ctx->felem_sub(z_out, z_out, delta);

  // y' = alpha*(4*beta - x') - 8*gamma^2
  ctx->felem_sub(y_out, fourbeta, x_out);
  ctx->felem_add(gamma, gamma, gamma);
  ctx->felem_sqr(gamma, gamma);
  ctx->felem_mul(y_out, alpha, y_out);
  ctx->felem_add(gamma, gamma, gamma);
  ctx->felem_sub(y_out, y_out, gamma);
}

// ec_nistp_point_add calculates (x1, y1, z1) + (x2, y2, z2)
//
// The method is taken from:
//   http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#addition-add-2007-bl
// adapted for mixed addition (z2 = 1, or z2 = 0 for the point at infinity).
//
// Coq transcription and correctness proof:
// <https://github.com/davidben/fiat-crypto/blob/c7b95f62b2a54b559522573310e9b487327d219a/src/Curves/Weierstrass/Jacobian.v#L467>
// <https://github.com/davidben/fiat-crypto/blob/c7b95f62b2a54b559522573310e9b487327d219a/src/Curves/Weierstrass/Jacobian.v#L544>
//
// This function includes a branch for checking whether the two input points
// are equal, (while not equal to the point at infinity). This case should
// never happen during single point multiplication, so there is no timing leak
// for ECDH and ECDSA.
void ec_nistp_point_add(const ec_nistp_meth *ctx,
                        ec_nistp_felem_limb *x3,
                        ec_nistp_felem_limb *y3,
                        ec_nistp_felem_limb *z3,
                        const ec_nistp_felem_limb *x1,
                        const ec_nistp_felem_limb *y1,
                        const ec_nistp_felem_limb *z1,
                        const int mixed,
                        const ec_nistp_felem_limb *x2,
                        const ec_nistp_felem_limb *y2,
                        const ec_nistp_felem_limb *z2) {
  ec_nistp_felem x_out, y_out, z_out;

  ec_nistp_felem_limb z1nz = ctx->felem_nz(z1);
  ec_nistp_felem_limb z2nz = ctx->felem_nz(z2);

  // z1z1 = z1**2
  ec_nistp_felem z1z1;
  ctx->felem_sqr(z1z1, z1);

  ec_nistp_felem u1, s1, two_z1z2;
  if (!mixed) {
    // z2z2 = z2**2
    ec_nistp_felem z2z2;
    ctx->felem_sqr(z2z2, z2);

    // u1 = x1*z2z2
    ctx->felem_mul(u1, x1, z2z2);

    // two_z1z2 = (z1 + z2)**2 - (z1z1 + z2z2) = 2z1z2
    ctx->felem_add(two_z1z2, z1, z2);
    ctx->felem_sqr(two_z1z2, two_z1z2);
    ctx->felem_sub(two_z1z2, two_z1z2, z1z1);
    ctx->felem_sub(two_z1z2, two_z1z2, z2z2);

    // s1 = y1 * z2**3
    ctx->felem_mul(s1, z2, z2z2);
    ctx->felem_mul(s1, s1, y1);
  } else {
    // We'll assume z2 = 1 (special case z2 = 0 is handled later).

    // u1 = x1*z2z2
    OPENSSL_memcpy(u1, x1, ctx->felem_num_limbs * sizeof(ec_nistp_felem_limb));
    // two_z1z2 = 2z1z2
    ctx->felem_add(two_z1z2, z1, z1);
    // s1 = y1 * z2**3
    OPENSSL_memcpy(s1, y1, ctx->felem_num_limbs * sizeof(ec_nistp_felem_limb));
  }

  // u2 = x2*z1z1
  ec_nistp_felem u2;
  ctx->felem_mul(u2, x2, z1z1);

  // h = u2 - u1
  ec_nistp_felem h;
  ctx->felem_sub(h, u2, u1);

  ec_nistp_felem_limb xneq = ctx->felem_nz(h);

  // z_out = two_z1z2 * h
  ctx->felem_mul(z_out, h, two_z1z2);

  // z1z1z1 = z1 * z1z1
  ec_nistp_felem z1z1z1;
  ctx->felem_mul(z1z1z1, z1, z1z1);

  // s2 = y2 * z1**3
  ec_nistp_felem s2;
  ctx->felem_mul(s2, y2, z1z1z1);

  // r = (s2 - s1)*2
  ec_nistp_felem r;
  ctx->felem_sub(r, s2, s1);
  ctx->felem_add(r, r, r);

  ec_nistp_felem_limb yneq = ctx->felem_nz(r);

  // This case will never occur in the constant-time |ec_GFp_mont_mul|.
  ec_nistp_felem_limb is_nontrivial_double =
                                     constant_time_is_zero_w(xneq | yneq) &
                                    ~constant_time_is_zero_w(z1nz) &
                                    ~constant_time_is_zero_w(z2nz);
  if (constant_time_declassify_w(is_nontrivial_double)) {
    ec_nistp_point_double(ctx, x3, y3, z3, x1, y1, z1);
    return;
  }

  // I = (2h)**2
  ec_nistp_felem i;
  ctx->felem_add(i, h, h);
  ctx->felem_sqr(i, i);

  // J = h * I
  ec_nistp_felem j;
  ctx->felem_mul(j, h, i);

  // V = U1 * I
  ec_nistp_felem v;
  ctx->felem_mul(v, u1, i);

  // x_out = r**2 - J - 2V
  ctx->felem_sqr(x_out, r);
  ctx->felem_sub(x_out, x_out, j);
  ctx->felem_sub(x_out, x_out, v);
  ctx->felem_sub(x_out, x_out, v);

  // y_out = r(V-x_out) - 2 * s1 * J
  ctx->felem_sub(y_out, v, x_out);
  ctx->felem_mul(y_out, y_out, r);
  ec_nistp_felem s1j;
  ctx->felem_mul(s1j, s1, j);
  ctx->felem_sub(y_out, y_out, s1j);
  ctx->felem_sub(y_out, y_out, s1j);

  cmovznz(x_out, ctx->felem_num_limbs, z1nz, x2, x_out);
  cmovznz(y_out, ctx->felem_num_limbs, z1nz, y2, y_out);
  cmovznz(z_out, ctx->felem_num_limbs, z1nz, z2, z_out);
  cmovznz(x3, ctx->felem_num_limbs, z2nz, x1, x_out);
  cmovznz(y3, ctx->felem_num_limbs, z2nz, y1, y_out);
  cmovznz(z3, ctx->felem_num_limbs, z2nz, z1, z_out);
}

// Returns i-th bit of the scalar (zero or one).
// The caller is responsible for making sure i is within bounds of the scalar. 
static int16_t get_bit(const EC_SCALAR *in, size_t i) {
// |in->words| is an array of BN_ULONGs which can be either 8 or 4 bytes long.
#if defined(OPENSSL_64_BIT)
  OPENSSL_STATIC_ASSERT(sizeof(BN_ULONG) == 8, bn_ulong_not_eight_bytes);
  return (in->words[i >> 6] >> (i & 63)) & 1;
#else
  OPENSSL_STATIC_ASSERT(sizeof(BN_ULONG) == 4, bn_ulong_not_four_bytes);
  return (in->words[i >> 5] >> (i & 31)) & 1;
#endif
}

#define DIV_AND_CEIL(a, b) ((a + b - 1) / b)

// Compute "regular" wNAF representation of a scalar, see
// Joye, Tunstall, "Exponent Recoding and Regular Exponentiation Algorithms",
// AfricaCrypt 2009, Alg 6.
// It forces an odd scalar and outputs digits in
// {\pm 1, \pm 3, \pm 5, \pm 7, \pm 9, ...}
// i.e. signed odd digits with _no zeroes_ -- that makes it "regular".
void scalar_rwnaf(int16_t *out, size_t window_size,
                  const EC_SCALAR *scalar, size_t scalar_bit_size) {
  assert(window_size < 14);

  // The assert above ensures this works correctly.
  const int16_t window_mask = (1 << (window_size + 1)) - 1;
  int16_t window = (int16_t)(scalar->words[0] & (BN_ULONG)window_mask);
  window |= 1;

  const size_t num_windows = DIV_AND_CEIL(scalar_bit_size, window_size);
  for (size_t i = 0; i < num_windows - 1; i++) {
    int16_t d = (window & window_mask) - (int16_t)(1 << window_size);
    out[i] = d;
    window = (window - d) >> window_size;
    for (size_t j = 1; j <= window_size; j++) {
      size_t idx = (i + 1) * window_size + j;
      if (idx < scalar_bit_size) {
        window |= get_bit(scalar, idx) << j;
      }
    }
  }
  out[num_windows - 1] = window;
}
