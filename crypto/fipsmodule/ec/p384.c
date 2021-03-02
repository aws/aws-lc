/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0
------------------------------------------------------------------------------------
*/

// Implementation of P-384 that uses Fiat-crypto for the field arithmetic
// found in third_party/fiat, similarly to p256.c

#include <openssl/ec.h>

#include <openssl/bn.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include "../bn/internal.h"
#include "../delocate.h"
#include "internal.h"

#if defined(BORINGSSL_HAS_UINT128)
#define BORINGSSL_NISTP384_64BIT 1
#include "../../../third_party/fiat/p384_64.h"
#else
#include "../../../third_party/fiat/p384_32.h"
#endif

#if defined(BORINGSSL_NISTP384_64BIT)
#define FIAT_P384_NLIMBS 6
typedef uint64_t fiat_p384_limb_t;
typedef uint64_t fiat_p384_felem[FIAT_P384_NLIMBS];
static const fiat_p384_felem fiat_p384_one = {0xffffffff00000001, 0xffffffff,
                                              0x1, 0x0, 0x0, 0x0};
#else  // 64BIT; else 32BIT
#define FIAT_P384_NLIMBS 12
typedef uint32_t fiat_p384_limb_t;
typedef uint32_t fiat_p384_felem[FIAT_P384_NLIMBS];
static const fiat_p384_felem fiat_p384_one = {
    0x1, 0xffffffff, 0xffffffff, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0};
#endif  // 64BIT

static fiat_p384_limb_t fiat_p384_nz(
    const fiat_p384_limb_t in1[FIAT_P384_NLIMBS]) {
  fiat_p384_limb_t ret;
  fiat_p384_nonzero(&ret, in1);
  return ret;
}

static void fiat_p384_copy(fiat_p384_limb_t out[FIAT_P384_NLIMBS],
                           const fiat_p384_limb_t in1[FIAT_P384_NLIMBS]) {
  for (size_t i = 0; i < FIAT_P384_NLIMBS; i++) {
    out[i] = in1[i];
  }
}

static void fiat_p384_cmovznz(fiat_p384_limb_t out[FIAT_P384_NLIMBS],
                              fiat_p384_limb_t t,
                              const fiat_p384_limb_t z[FIAT_P384_NLIMBS],
                              const fiat_p384_limb_t nz[FIAT_P384_NLIMBS]) {
  fiat_p384_selectznz(out, !!t, z, nz);
}

static void fiat_p384_from_generic(fiat_p384_felem out, const EC_FELEM *in) {
  fiat_p384_from_bytes(out, in->bytes);
}

static void fiat_p384_to_generic(EC_FELEM *out, const fiat_p384_felem in) {
  // This works because 384 is a multiple of 64, so there are no excess bytes to
  // zero when rounding up to |BN_ULONG|s.
  OPENSSL_STATIC_ASSERT(
      384 / 8 == sizeof(BN_ULONG) * ((384 + BN_BITS2 - 1) / BN_BITS2),
      fiat_p384_to_bytes_leaves_bytes_uninitialized);
  fiat_p384_to_bytes(out->bytes, in);
}

// fiat_p384_inv_square calculates |out| = |in|^{-2}
//
// Based on Fermat's Little Theorem:
//   a^p = a (mod p)
//   a^{p-1} = 1 (mod p)
//   a^{p-3} = a^{-2} (mod p)
// p = 2^384 - 2^128 - 2^96 + 2^32 - 1
// Hexadecimal representation of p − 3:
// p-3 = ffffffff ffffffff ffffffff ffffffff ffffffff ffffffff ffffffff fffffffe
//       ffffffff 00000000 00000000 fffffffc
static void fiat_p384_inv_square(fiat_p384_felem out,
                                 const fiat_p384_felem in) {
  // This implements the addition chain described in
  // https://briansmith.org/ecc-inversion-addition-chains-01#p384_field_inversion
  // The side comments show the value of the exponent:
  // squaring the element => doubling the exponent
  // multiplying by an element => adding to the exponent the power of that element
  fiat_p384_felem x2, x3, x6, x12, x15, x30, x60, x120;
  fiat_p384_square(x2, in);   // 2^2 - 2^1
  fiat_p384_mul(x2, x2, in);  // 2^2 - 2^0

  fiat_p384_square(x3, x2);   // 2^3 - 2^1
  fiat_p384_mul(x3, x3, in);  // 2^3 - 2^0

  fiat_p384_square(x6, x3);
  for (int i = 1; i < 3; i++) {
    fiat_p384_square(x6, x6);
  }                           // 2^6 - 2^3
  fiat_p384_mul(x6, x6, x3);  // 2^6 - 2^0

  fiat_p384_square(x12, x6);
  for (int i = 1; i < 6; i++) {
    fiat_p384_square(x12, x12);
  }                             // 2^12 - 2^6
  fiat_p384_mul(x12, x12, x6);  // 2^12 - 2^0

  fiat_p384_square(x15, x12);
  for (int i = 1; i < 3; i++) {
    fiat_p384_square(x15, x15);
  }                             // 2^15 - 2^3
  fiat_p384_mul(x15, x15, x3);  // 2^15 - 2^0

  fiat_p384_square(x30, x15);
  for (int i = 1; i < 15; i++) {
    fiat_p384_square(x30, x30);
  }                              // 2^30 - 2^15
  fiat_p384_mul(x30, x30, x15);  // 2^30 - 2^0

  fiat_p384_square(x60, x30);
  for (int i = 1; i < 30; i++) {
    fiat_p384_square(x60, x60);
  }                              // 2^60 - 2^30
  fiat_p384_mul(x60, x60, x30);  // 2^60 - 2^0

  fiat_p384_square(x120, x60);
  for (int i = 1; i < 60; i++) {
    fiat_p384_square(x120, x120);
  }                                // 2^120 - 2^60
  fiat_p384_mul(x120, x120, x60);  // 2^120 - 2^0

  fiat_p384_felem ret;
  fiat_p384_square(ret, x120);
  for (int i = 1; i < 120; i++) {
    fiat_p384_square(ret, ret);
  }                                // 2^240 - 2^120
  fiat_p384_mul(ret, ret, x120);   // 2^240 - 2^0

  for (int i = 0; i < 15; i++) {
    fiat_p384_square(ret, ret);
  }                                // 2^255 - 2^15
  fiat_p384_mul(ret, ret, x15);    // 2^255 - 2^0

  // Why (1 + 30) in the loop?
  // This is as expressed in https://briansmith.org/ecc-inversion-addition-chains-01#p384_field_inversion
  // My guess is to say that we're going to shift 31 bits, but this time we won't add x31
  // to make all the new bits 1s, as was done in previous steps,
  // but we're going to add x30 so there will be 255 1s, then a 0, then 30 1s to form this pattern:
  // ffffffff ffffffff ffffffff ffffffff ffffffff ffffffff ffffffff fffffffe ffffffff
  // (the last 2 1s are appended in the following step).
  for (int i = 0; i < (1 + 30); i++) {
    fiat_p384_square(ret, ret);
  }                                // 2^286 - 2^31
  fiat_p384_mul(ret, ret, x30);    // 2^286 - 2^30 - 2^0

  fiat_p384_square(ret, ret);
  fiat_p384_square(ret, ret);      // 2^288 - 2^32 - 2^2
  fiat_p384_mul(ret, ret, x2);     // 2^288 - 2^32 - 2^0

  // Why not 94 instead of (64 + 30) in the loop?
  // Similarly to the comment above, there is a shift of 94 bits but what will be added is x30,
  // which will cause 64 of those bits to be 64 0s and 30 1s to complete the pattern above with:
  // 00000000 00000000 fffffffc
  // (the last 2 0s are appended by the last 2 shifts).
  for (int i = 0; i < (64 + 30); i++) {
    fiat_p384_square(ret, ret);
  }                                // 2^382 - 2^126 - 2^94
  fiat_p384_mul(ret, ret, x30);    // 2^382 - 2^126 - 2^94 + 2^30 - 2^0

  fiat_p384_square(ret, ret);
  fiat_p384_square(out, ret);      // 2^384 - 2^128 - 2^96 + 2^32 - 2^2 = p - 3
}

// Group operations
// ----------------
//
// Building on top of the field operations we have the operations on the
// elliptic curve group itself. Points on the curve are represented in Jacobian
// coordinates.
//
// fiat_p384_point_double calculates 2*(x_in, y_in, z_in)
//
// The method is taken from:
//   http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html#doubling-dbl-2001-b
//
// Coq transcription and correctness proof:
// <https://github.com/mit-plv/fiat-crypto/blob/79f8b5f39ed609339f0233098dee1a3c4e6b3080/src/Curves/Weierstrass/Jacobian.v#L93>
// <https://github.com/mit-plv/fiat-crypto/blob/79f8b5f39ed609339f0233098dee1a3c4e6b3080/src/Curves/Weierstrass/Jacobian.v#L201>
// Outputs can equal corresponding inputs, i.e., x_out == x_in is allowed.
// while x_out == y_in is not (maybe this works, but it's not tested).
static void fiat_p384_point_double(fiat_p384_felem x_out, fiat_p384_felem y_out,
                                   fiat_p384_felem z_out,
                                   const fiat_p384_felem x_in,
                                   const fiat_p384_felem y_in,
                                   const fiat_p384_felem z_in) {
  fiat_p384_felem delta, gamma, beta, ftmp, ftmp2, tmptmp, alpha, fourbeta;
  // delta = z^2
  fiat_p384_square(delta, z_in);
  // gamma = y^2
  fiat_p384_square(gamma, y_in);
  // beta = x*gamma
  fiat_p384_mul(beta, x_in, gamma);

  // alpha = 3*(x-delta)*(x+delta)
  fiat_p384_sub(ftmp, x_in, delta);
  fiat_p384_add(ftmp2, x_in, delta);

  fiat_p384_add(tmptmp, ftmp2, ftmp2);
  fiat_p384_add(ftmp2, ftmp2, tmptmp);
  fiat_p384_mul(alpha, ftmp, ftmp2);

  // x' = alpha^2 - 8*beta
  fiat_p384_square(x_out, alpha);
  fiat_p384_add(fourbeta, beta, beta);
  fiat_p384_add(fourbeta, fourbeta, fourbeta);
  fiat_p384_add(tmptmp, fourbeta, fourbeta);
  fiat_p384_sub(x_out, x_out, tmptmp);

  // z' = (y + z)^2 - gamma - delta
  fiat_p384_add(delta, gamma, delta);
  fiat_p384_add(ftmp, y_in, z_in);
  fiat_p384_square(z_out, ftmp);
  fiat_p384_sub(z_out, z_out, delta);

  // y' = alpha*(4*beta - x') - 8*gamma^2
  fiat_p384_sub(y_out, fourbeta, x_out);
  fiat_p384_add(gamma, gamma, gamma);
  fiat_p384_square(gamma, gamma);
  fiat_p384_mul(y_out, alpha, y_out);
  fiat_p384_add(gamma, gamma, gamma);
  fiat_p384_sub(y_out, y_out, gamma);
}

// fiat_p384_point_add calculates (x1, y1, z1) + (x2, y2, z2)
//
// The method is taken from:
//   http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#addition-add-2007-bl
// adapted for mixed addition (z2 = 1, or z2 = 0 for the point at infinity).
//
// Coq transcription and correctness proof:
// <https://github.com/davidben/fiat-crypto/blob/c7b95f62b2a54b559522573310e9b487327d219a/src/Curves/Weierstrass/Jacobian.v#L467>
// <https://github.com/davidben/fiat-crypto/blob/c7b95f62b2a54b559522573310e9b487327d219a/src/Curves/Weierstrass/Jacobian.v#L544>
static void fiat_p384_point_add(fiat_p384_felem x3, fiat_p384_felem y3,
                                fiat_p384_felem z3, const fiat_p384_felem x1,
                                const fiat_p384_felem y1,
                                const fiat_p384_felem z1, const int mixed,
                                const fiat_p384_felem x2,
                                const fiat_p384_felem y2,
                                const fiat_p384_felem z2) {
  fiat_p384_felem x_out, y_out, z_out;
  fiat_p384_limb_t z1nz = fiat_p384_nz(z1);
  fiat_p384_limb_t z2nz = fiat_p384_nz(z2);

  // z1z1 = z1z1 = z1**2
  fiat_p384_felem z1z1;
  fiat_p384_square(z1z1, z1);

  fiat_p384_felem u1, s1, two_z1z2;
  if (!mixed) {
    // z2z2 = z2**2
    fiat_p384_felem z2z2;
    fiat_p384_square(z2z2, z2);

    // u1 = x1*z2z2
    fiat_p384_mul(u1, x1, z2z2);

    // two_z1z2 = (z1 + z2)**2 - (z1z1 + z2z2) = 2z1z2
    fiat_p384_add(two_z1z2, z1, z2);
    fiat_p384_square(two_z1z2, two_z1z2);
    fiat_p384_sub(two_z1z2, two_z1z2, z1z1);
    fiat_p384_sub(two_z1z2, two_z1z2, z2z2);

    // s1 = y1 * z2**3
    fiat_p384_mul(s1, z2, z2z2);
    fiat_p384_mul(s1, s1, y1);
  } else {
    // We'll assume z2 = 1 (special case z2 = 0 is handled later).

    // u1 = x1*z2z2
    fiat_p384_copy(u1, x1);
    // two_z1z2 = 2z1z2
    fiat_p384_add(two_z1z2, z1, z1);
    // s1 = y1 * z2**3
    fiat_p384_copy(s1, y1);
  }

  // u2 = x2*z1z1
  fiat_p384_felem u2;
  fiat_p384_mul(u2, x2, z1z1);

  // h = u2 - u1
  fiat_p384_felem h;
  fiat_p384_sub(h, u2, u1);

  fiat_p384_limb_t xneq = fiat_p384_nz(h);

  // z_out = two_z1z2 * h
  fiat_p384_mul(z_out, h, two_z1z2);

  // z1z1z1 = z1 * z1z1
  fiat_p384_felem z1z1z1;
  fiat_p384_mul(z1z1z1, z1, z1z1);

  // s2 = y2 * z1**3
  fiat_p384_felem s2;
  fiat_p384_mul(s2, y2, z1z1z1);

  // r = (s2 - s1)*2
  fiat_p384_felem r;
  fiat_p384_sub(r, s2, s1);
  fiat_p384_add(r, r, r);

  fiat_p384_limb_t yneq = fiat_p384_nz(r);

  // This case will never occur in the constant-time |ec_GFp_mont_mul|.
  fiat_p384_limb_t is_nontrivial_double = constant_time_is_zero_w(xneq | yneq) &
                                          ~constant_time_is_zero_w(z1nz) &
                                          ~constant_time_is_zero_w(z2nz);
  if (is_nontrivial_double) {
    fiat_p384_point_double(x3, y3, z3, x1, y1, z1);
    return;
  }

  // I = (2h)**2
  fiat_p384_felem i;
  fiat_p384_add(i, h, h);
  fiat_p384_square(i, i);

  // J = h * I
  fiat_p384_felem j;
  fiat_p384_mul(j, h, i);

  // V = U1 * I
  fiat_p384_felem v;
  fiat_p384_mul(v, u1, i);

  // x_out = r**2 - J - 2V
  fiat_p384_square(x_out, r);
  fiat_p384_sub(x_out, x_out, j);
  fiat_p384_sub(x_out, x_out, v);
  fiat_p384_sub(x_out, x_out, v);

  // y_out = r(V-x_out) - 2 * s1 * J
  fiat_p384_sub(y_out, v, x_out);
  fiat_p384_mul(y_out, y_out, r);
  fiat_p384_felem s1j;
  fiat_p384_mul(s1j, s1, j);
  fiat_p384_sub(y_out, y_out, s1j);
  fiat_p384_sub(y_out, y_out, s1j);

  fiat_p384_cmovznz(x_out, z1nz, x2, x_out);
  fiat_p384_cmovznz(x3, z2nz, x1, x_out);
  fiat_p384_cmovznz(y_out, z1nz, y2, y_out);
  fiat_p384_cmovznz(y3, z2nz, y1, y_out);
  fiat_p384_cmovznz(z_out, z1nz, z2, z_out);
  fiat_p384_cmovznz(z3, z2nz, z1, z_out);
}

// OPENSSL EC_METHOD FUNCTIONS

// Takes the Jacobian coordinates (X, Y, Z) of a point and returns (X', Y') =
// (X/Z^2, Y/Z^3).
static int ec_GFp_nistp384_point_get_affine_coordinates(
    const EC_GROUP *group, const EC_RAW_POINT *point, EC_FELEM *x_out,
    EC_FELEM *y_out) {
  if (ec_GFp_simple_is_at_infinity(group, point)) {
    OPENSSL_PUT_ERROR(EC, EC_R_POINT_AT_INFINITY);
    return 0;
  }

  fiat_p384_felem z1, z2;
  fiat_p384_from_generic(z1, &point->Z);
  fiat_p384_inv_square(z2, z1);

  if (x_out != NULL) {
    fiat_p384_felem x;
    fiat_p384_from_generic(x, &point->X);
    fiat_p384_mul(x, x, z2);
    fiat_p384_to_generic(x_out, x);
  }

  if (y_out != NULL) {
    fiat_p384_felem y;
    fiat_p384_from_generic(y, &point->Y);
    fiat_p384_square(z2, z2);  // z^-4
    fiat_p384_mul(y, y, z1);   // y * z
    fiat_p384_mul(y, y, z2);   // y * z^-3
    fiat_p384_to_generic(y_out, y);
  }

  return 1;
}

static void ec_GFp_nistp384_add(const EC_GROUP *group, EC_RAW_POINT *r,
                                const EC_RAW_POINT *a, const EC_RAW_POINT *b) {
  fiat_p384_felem x1, y1, z1, x2, y2, z2;
  fiat_p384_from_generic(x1, &a->X);
  fiat_p384_from_generic(y1, &a->Y);
  fiat_p384_from_generic(z1, &a->Z);
  fiat_p384_from_generic(x2, &b->X);
  fiat_p384_from_generic(y2, &b->Y);
  fiat_p384_from_generic(z2, &b->Z);
  fiat_p384_point_add(x1, y1, z1, x1, y1, z1, 0 /* both Jacobian */, x2, y2,
                      z2);
  fiat_p384_to_generic(&r->X, x1);
  fiat_p384_to_generic(&r->Y, y1);
  fiat_p384_to_generic(&r->Z, z1);
}

static void ec_GFp_nistp384_dbl(const EC_GROUP *group, EC_RAW_POINT *r,
                                const EC_RAW_POINT *a) {
  fiat_p384_felem x, y, z;
  fiat_p384_from_generic(x, &a->X);
  fiat_p384_from_generic(y, &a->Y);
  fiat_p384_from_generic(z, &a->Z);
  fiat_p384_point_double(x, y, z, x, y, z);
  fiat_p384_to_generic(&r->X, x);
  fiat_p384_to_generic(&r->Y, y);
  fiat_p384_to_generic(&r->Z, z);
}

DEFINE_METHOD_FUNCTION(EC_METHOD, EC_GFp_nistp384_method) {
  out->group_init = ec_GFp_mont_group_init;
  out->group_finish = ec_GFp_mont_group_finish;
  out->group_set_curve = ec_GFp_mont_group_set_curve;
  out->point_get_affine_coordinates =
      ec_GFp_nistp384_point_get_affine_coordinates;
  out->jacobian_to_affine_batch =
      ec_GFp_mont_jacobian_to_affine_batch; // needed for TrustToken tests
  out->add = ec_GFp_nistp384_add;
  out->dbl = ec_GFp_nistp384_dbl;
  out->mul = ec_GFp_mont_mul;
  out->mul_base = ec_GFp_mont_mul_base;
  out->mul_batch = ec_GFp_mont_mul_batch; // needed for TrustToken tests
  out->mul_public_batch = ec_GFp_mont_mul_public_batch;
  out->init_precomp = ec_GFp_mont_init_precomp;
  out->mul_precomp = ec_GFp_mont_mul_precomp;
  out->felem_mul = ec_GFp_mont_felem_mul;
  out->felem_sqr = ec_GFp_mont_felem_sqr;
  out->felem_to_bytes = ec_GFp_mont_felem_to_bytes;
  out->felem_from_bytes = ec_GFp_mont_felem_from_bytes;
  out->felem_reduce = ec_GFp_mont_felem_reduce;
  out->felem_exp = ec_GFp_mont_felem_exp;
  out->scalar_inv0_montgomery = ec_simple_scalar_inv0_montgomery;
  out->scalar_to_montgomery_inv_vartime =
      ec_simple_scalar_to_montgomery_inv_vartime;
  out->cmp_x_coordinate = ec_GFp_mont_cmp_x_coordinate;
}
