/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0 OR ISC
------------------------------------------------------------------------------------
*/

#if !defined(OPENSSL_SMALL)
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
// | 2. |       |       |       |
// | 3. |       |       |       |
// | 4. |       |       |       |
// | 5. |       |       |       |
//  * For P-256, only the Fiat-crypto implementation in p256.c is replaced. 

#include "ec_nistp.h"

// Some of the functions in below need temporary field element variables.
// To avoid dynamic allocation we define nistp_felem type to have the maximum
// size possible (which is currently P-521 curve). The values are hard-coded
// for the moment, this will be fixed when we migrate the whole P-521
// implementation to ec_nistp.c.
#if defined(EC_NISTP_USE_64BIT_LIMB)
#define NISTP_FELEM_MAX_NUM_OF_LIMBS (9)
#else
#define NISTP_FELEM_MAX_NUM_OF_LIMBS (19)
#endif
typedef felem_limb nistp_felem[NISTP_FELEM_MAX_NUM_OF_LIMBS];

// Group operations
// ----------------
//
// Building on top of the field operations we have the operations on the
// elliptic curve group itself. Points on the curve are represented in Jacobian
// coordinates.
//
// p521_point_double calculates 2*(x_in, y_in, z_in)
//
// The method is taken from:
//   http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html#doubling-dbl-2001-b
//
// Coq transcription and correctness proof:
// <https://github.com/mit-plv/fiat-crypto/blob/79f8b5f39ed609339f0233098dee1a3c4e6b3080/src/Curves/Weierstrass/Jacobian.v#L93>
// <https://github.com/mit-plv/fiat-crypto/blob/79f8b5f39ed609339f0233098dee1a3c4e6b3080/src/Curves/Weierstrass/Jacobian.v#L201>
// Outputs can equal corresponding inputs, i.e., x_out == x_in is allowed;
// while x_out == y_in is not (maybe this works, but it's not tested).
void nistp_point_double(nistp_felem_methods *ctx,
                        felem_limb *x_out,
                        felem_limb *y_out,
                        felem_limb *z_out,
                        const felem_limb *x_in,
                        const felem_limb *y_in,
                        const felem_limb *z_in) {
  nistp_felem delta, gamma, beta, ftmp, ftmp2, tmptmp, alpha, fourbeta;
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

#endif // OPENSSL_SMALL
