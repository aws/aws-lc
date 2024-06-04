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
void ec_nistp_point_double(const ec_nistp_felem_meth *ctx,
                           ec_nistp_felem_limb *x_out,
                           ec_nistp_felem_limb *y_out,
                           ec_nistp_felem_limb *z_out,
                           const ec_nistp_felem_limb *x_in,
                           const ec_nistp_felem_limb *y_in,
                           const ec_nistp_felem_limb *z_in) {
  ec_nistp_felem delta, gamma, beta, ftmp, ftmp2, tmptmp, alpha, fourbeta;
  // delta = z^2
  ctx->sqr(delta, z_in);
  // gamma = y^2
  ctx->sqr(gamma, y_in);
  // beta = x*gamma
  ctx->mul(beta, x_in, gamma);

  // alpha = 3*(x-delta)*(x+delta)
  ctx->sub(ftmp, x_in, delta);
  ctx->add(ftmp2, x_in, delta);

  ctx->add(tmptmp, ftmp2, ftmp2);
  ctx->add(ftmp2, ftmp2, tmptmp);
  ctx->mul(alpha, ftmp, ftmp2);

  // x' = alpha^2 - 8*beta
  ctx->sqr(x_out, alpha);
  ctx->add(fourbeta, beta, beta);
  ctx->add(fourbeta, fourbeta, fourbeta);
  ctx->add(tmptmp, fourbeta, fourbeta);
  ctx->sub(x_out, x_out, tmptmp);

  // z' = (y + z)^2 - gamma - delta
  // The following calculation differs from the Coq proof cited above.
  // The proof is for:
  //   add(delta, gamma, delta);
  //   add(ftmp, y_in, z_in);
  //   square(z_out, ftmp);
  //   sub(z_out, z_out, delta);
  // Our operations sequence is a bit more efficient because it saves us
  // a certain number of conditional moves.
  ctx->add(ftmp, y_in, z_in);
  ctx->sqr(z_out, ftmp);
  ctx->sub(z_out, z_out, gamma);
  ctx->sub(z_out, z_out, delta);

  // y' = alpha*(4*beta - x') - 8*gamma^2
  ctx->sub(y_out, fourbeta, x_out);
  ctx->add(gamma, gamma, gamma);
  ctx->sqr(gamma, gamma);
  ctx->mul(y_out, alpha, y_out);
  ctx->add(gamma, gamma, gamma);
  ctx->sub(y_out, y_out, gamma);
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
void ec_nistp_point_add(const ec_nistp_felem_meth *ctx,
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

  ec_nistp_felem_limb z1nz = ctx->nz(z1);
  ec_nistp_felem_limb z2nz = ctx->nz(z2);

  // z1z1 = z1**2
  ec_nistp_felem z1z1;
  ctx->sqr(z1z1, z1);

  ec_nistp_felem u1, s1, two_z1z2;
  if (!mixed) {
    // z2z2 = z2**2
    ec_nistp_felem z2z2;
    ctx->sqr(z2z2, z2);

    // u1 = x1*z2z2
    ctx->mul(u1, x1, z2z2);

    // two_z1z2 = (z1 + z2)**2 - (z1z1 + z2z2) = 2z1z2
    ctx->add(two_z1z2, z1, z2);
    ctx->sqr(two_z1z2, two_z1z2);
    ctx->sub(two_z1z2, two_z1z2, z1z1);
    ctx->sub(two_z1z2, two_z1z2, z2z2);

    // s1 = y1 * z2**3
    ctx->mul(s1, z2, z2z2);
    ctx->mul(s1, s1, y1);
  } else {
    // We'll assume z2 = 1 (special case z2 = 0 is handled later).

    // u1 = x1*z2z2
    OPENSSL_memcpy(u1, x1, ctx->felem_num_limbs * sizeof(ec_nistp_felem_limb));
    // two_z1z2 = 2z1z2
    ctx->add(two_z1z2, z1, z1);
    // s1 = y1 * z2**3
    OPENSSL_memcpy(s1, y1, ctx->felem_num_limbs * sizeof(ec_nistp_felem_limb));
  }

  // u2 = x2*z1z1
  ec_nistp_felem u2;
  ctx->mul(u2, x2, z1z1);

  // h = u2 - u1
  ec_nistp_felem h;
  ctx->sub(h, u2, u1);

  ec_nistp_felem_limb xneq = ctx->nz(h);

  // z_out = two_z1z2 * h
  ctx->mul(z_out, h, two_z1z2);

  // z1z1z1 = z1 * z1z1
  ec_nistp_felem z1z1z1;
  ctx->mul(z1z1z1, z1, z1z1);

  // s2 = y2 * z1**3
  ec_nistp_felem s2;
  ctx->mul(s2, y2, z1z1z1);

  // r = (s2 - s1)*2
  ec_nistp_felem r;
  ctx->sub(r, s2, s1);
  ctx->add(r, r, r);

  ec_nistp_felem_limb yneq = ctx->nz(r);

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
  ctx->add(i, h, h);
  ctx->sqr(i, i);

  // J = h * I
  ec_nistp_felem j;
  ctx->mul(j, h, i);

  // V = U1 * I
  ec_nistp_felem v;
  ctx->mul(v, u1, i);

  // x_out = r**2 - J - 2V
  ctx->sqr(x_out, r);
  ctx->sub(x_out, x_out, j);
  ctx->sub(x_out, x_out, v);
  ctx->sub(x_out, x_out, v);

  // y_out = r(V-x_out) - 2 * s1 * J
  ctx->sub(y_out, v, x_out);
  ctx->mul(y_out, y_out, r);
  ec_nistp_felem s1j;
  ctx->mul(s1j, s1, j);
  ctx->sub(y_out, y_out, s1j);
  ctx->sub(y_out, y_out, s1j);

  cmovznz(x_out, ctx->felem_num_limbs, z1nz, x2, x_out);
  cmovznz(y_out, ctx->felem_num_limbs, z1nz, y2, y_out);
  cmovznz(z_out, ctx->felem_num_limbs, z1nz, z2, z_out);
  cmovznz(x3, ctx->felem_num_limbs, z2nz, x1, x_out);
  cmovznz(y3, ctx->felem_num_limbs, z2nz, y1, y_out);
  cmovznz(z3, ctx->felem_num_limbs, z2nz, z1, z_out);
}

