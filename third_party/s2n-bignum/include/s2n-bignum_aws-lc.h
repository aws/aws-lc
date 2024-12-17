/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */
#ifndef S2N_BIGNUM_AWS_LC_H
#define S2N_BIGNUM_AWS_LC_H

#if defined(_MSC_VER) || !defined(__STDC_VERSION__) || __STDC_VERSION__ < 199901L || defined(__STDC_NO_VLA__)
  #define S2N_BIGNUM_STATIC
#else
  #define S2N_BIGNUM_STATIC static
#endif

// ----------------------------------------------------------------------------
// C prototypes for s2n-bignum functions used in AWS-LC
// ----------------------------------------------------------------------------

// For some functions there are additional variants with names ending in
// "_alt". These have the same core mathematical functionality as their
// non-"alt" versions, but can be better suited to some microarchitectures:
//
//      - On x86, the "_alt" forms avoid BMI and ADX instruction set
//        extensions, so will run on any x86_64 machine, even older ones
//
//      - On ARM, the "_alt" forms target machines with higher multiplier
//        throughput, generally offering higher performance there.
// For each of those, we define a _selector function that selects, in runtime,
// the _alt or non-_alt version to run.

#if defined(OPENSSL_X86_64)
// On x86_64 platforms s2n-bignum uses bmi2 and adx instruction sets
// for some of the functions. These instructions are not supported by
// every x86 CPU so we have to check if they are available and in case
// they are not we fallback to slightly slower but generic implementation.
static inline uint8_t use_s2n_bignum_alt(void) {
  return (!CRYPTO_is_BMI2_capable() || !CRYPTO_is_ADX_capable());
}
#else
// On aarch64 platforms s2n-bignum has two implementations of certain
// functions -- the default one and the alternative (suffixed _alt).
// Depending on the architecture one version is faster than the other.
// Generally, the "_alt" functions are faster on architectures with higher
// multiplier throughput, for example, Graviton 3, Apple's M1 and iPhone chips.
static inline uint8_t use_s2n_bignum_alt(void) {
  return CRYPTO_is_ARMv8_wide_multiplier_capable();
}
#endif

extern void p256_montjscalarmul(uint64_t res[S2N_BIGNUM_STATIC 12], const uint64_t scalar[S2N_BIGNUM_STATIC 4], uint64_t point[S2N_BIGNUM_STATIC 12]);
extern void p256_montjscalarmul_alt(uint64_t res[S2N_BIGNUM_STATIC 12], const uint64_t scalar[S2N_BIGNUM_STATIC 4], uint64_t point[S2N_BIGNUM_STATIC 12]);
static inline void p256_montjscalarmul_selector(uint64_t res[S2N_BIGNUM_STATIC 12], const uint64_t scalar[S2N_BIGNUM_STATIC 4], uint64_t point[S2N_BIGNUM_STATIC 12]) {
  if (use_s2n_bignum_alt()) { p256_montjscalarmul_alt(res, scalar, point); }
  else { p256_montjscalarmul(res, scalar, point); }
}

// Montgomery inverse modulo p_256 = 2^256 - 2^224 + 2^192 + 2^96 - 1
//   z = x^-1 mod p_256.
// The function is constant-time.
extern void bignum_montinv_p256(uint64_t z[S2N_BIGNUM_STATIC 4], const uint64_t x[S2N_BIGNUM_STATIC 4]);

// Add modulo p_384, z := (x + y) mod p_384, assuming x and y reduced
// Inputs x[6], y[6]; output z[6]
extern void bignum_add_p384(uint64_t z[S2N_BIGNUM_STATIC 6], const uint64_t x[S2N_BIGNUM_STATIC 6], const uint64_t y[S2N_BIGNUM_STATIC 6]);

// Convert from almost-Montgomery form, z := (x / 2^384) mod p_384
// Input x[6]; output z[6]
extern void bignum_deamont_p384(uint64_t z[S2N_BIGNUM_STATIC 6], const uint64_t x[S2N_BIGNUM_STATIC 6]);
extern void bignum_deamont_p384_alt(uint64_t z[S2N_BIGNUM_STATIC 6], const uint64_t x[S2N_BIGNUM_STATIC 6]);
static inline void bignum_deamont_p384_selector(uint64_t z[S2N_BIGNUM_STATIC 6], const uint64_t x[S2N_BIGNUM_STATIC 6]) {
  if (use_s2n_bignum_alt()) { bignum_deamont_p384_alt(z, x); }
  else { bignum_deamont_p384(z, x); }
}

// Montgomery multiply, z := (x * y / 2^384) mod p_384 
// Inputs x[6], y[6]; output z[6]
extern void bignum_montmul_p384(uint64_t z[S2N_BIGNUM_STATIC 6], const uint64_t x[S2N_BIGNUM_STATIC 6], const uint64_t y[S2N_BIGNUM_STATIC 6]);
extern void bignum_montmul_p384_alt(uint64_t z[S2N_BIGNUM_STATIC 6], const uint64_t x[S2N_BIGNUM_STATIC 6], const uint64_t y[S2N_BIGNUM_STATIC 6]);
static inline void bignum_montmul_p384_selector(uint64_t z[S2N_BIGNUM_STATIC 6], const uint64_t x[S2N_BIGNUM_STATIC 6], const uint64_t y[S2N_BIGNUM_STATIC 6]) {
  if (use_s2n_bignum_alt()) { bignum_montmul_p384_alt(z, x, y); }
  else { bignum_montmul_p384(z, x, y); }
}

// Montgomery square, z := (x^2 / 2^384) mod p_384
// Input x[6]; output z[6]
extern void bignum_montsqr_p384(uint64_t z[S2N_BIGNUM_STATIC 6], const uint64_t x[S2N_BIGNUM_STATIC 6]);
extern void bignum_montsqr_p384_alt(uint64_t z[S2N_BIGNUM_STATIC 6], const uint64_t x[S2N_BIGNUM_STATIC 6]);
static inline void bignum_montsqr_p384_selector(uint64_t z[S2N_BIGNUM_STATIC 6], const uint64_t x[S2N_BIGNUM_STATIC 6]) {
  if (use_s2n_bignum_alt()) { bignum_montsqr_p384_alt(z, x); }
  else { bignum_montsqr_p384(z, x); }
}

// Negate modulo p_384, z := (-x) mod p_384, assuming x reduced
// Input x[6]; output z[6]
extern void bignum_neg_p384(uint64_t z[S2N_BIGNUM_STATIC 6], const uint64_t x[S2N_BIGNUM_STATIC 6]);

// Subtract modulo p_384, z := (x - y) mod p_384
// Inputs x[6], y[6]; output z[6]
extern void bignum_sub_p384(uint64_t z[S2N_BIGNUM_STATIC 6], const uint64_t x[S2N_BIGNUM_STATIC 6], const uint64_t y[S2N_BIGNUM_STATIC 6]);

// Convert to Montgomery form z := (2^384 * x) mod p_384 */
// Input x[6]; output z[6] */
extern void bignum_tomont_p384(uint64_t z[S2N_BIGNUM_STATIC 6], const uint64_t x[S2N_BIGNUM_STATIC 6]);
extern void bignum_tomont_p384_alt(uint64_t z[S2N_BIGNUM_STATIC 6], const uint64_t x[S2N_BIGNUM_STATIC 6]);
static inline void bignum_tomont_p384_selector(uint64_t z[S2N_BIGNUM_STATIC 6], const uint64_t x[S2N_BIGNUM_STATIC 6]) {
  if (use_s2n_bignum_alt()) { bignum_tomont_p384_alt(z, x); }
  else { bignum_tomont_p384(z, x); }
}
extern void p384_montjdouble(uint64_t p3[S2N_BIGNUM_STATIC 18],uint64_t p1[S2N_BIGNUM_STATIC 18]);
extern void p384_montjdouble_alt(uint64_t p3[S2N_BIGNUM_STATIC 18],uint64_t p1[S2N_BIGNUM_STATIC 18]);
static inline void p384_montjdouble_selector(uint64_t p3[S2N_BIGNUM_STATIC 18],uint64_t p1[S2N_BIGNUM_STATIC 18]) {
    if (use_s2n_bignum_alt()) { p384_montjdouble_alt(p3, p1); }
    else { p384_montjdouble(p3, p1); }
}

extern void p384_montjscalarmul(uint64_t res[S2N_BIGNUM_STATIC 18], const uint64_t scalar[S2N_BIGNUM_STATIC 6], uint64_t point[S2N_BIGNUM_STATIC 18]);
extern void p384_montjscalarmul_alt(uint64_t res[S2N_BIGNUM_STATIC 18], const uint64_t scalar[S2N_BIGNUM_STATIC 6], uint64_t point[S2N_BIGNUM_STATIC 18]);
static inline void p384_montjscalarmul_selector(uint64_t res[S2N_BIGNUM_STATIC 18], const uint64_t scalar[S2N_BIGNUM_STATIC 6], uint64_t point[S2N_BIGNUM_STATIC 18]) {
  if (use_s2n_bignum_alt()) { p384_montjscalarmul_alt(res, scalar, point); }
  else { p384_montjscalarmul(res, scalar, point); }
}

// Montgomery inverse modulo p_384 = 2^384 - 2^128 - 2^96 + 2^32 - 1
//   z = x^-1 mod p_384.
// The function is constant-time.
extern void bignum_montinv_p384(uint64_t z[S2N_BIGNUM_STATIC 6], const uint64_t x[S2N_BIGNUM_STATIC 6]);

// Convert 6-digit (384-bit) bignum from little-endian form
// Input x[6]; output z[6]
extern void bignum_fromlebytes_6(uint64_t z[S2N_BIGNUM_STATIC 6], const uint8_t x[S2N_BIGNUM_STATIC 48]);

// Convert 6-digit (384-bit) bignum to little-endian form
// Input x[6]; output z[6]
extern void bignum_tolebytes_6(uint8_t z[S2N_BIGNUM_STATIC 48], const uint64_t x[S2N_BIGNUM_STATIC 6]);

// 384-bit nonzeroness test, returning 1 if x is nonzero, 0 if x is zero
// Input x[6]; output function return
extern uint64_t bignum_nonzero_6(const uint64_t x[S2N_BIGNUM_STATIC 6]);

// Add modulo p_521, z := (x + y) mod p_521, assuming x and y reduced
// Inputs x[9], y[9]; output z[9]
extern void bignum_add_p521(uint64_t z[S2N_BIGNUM_STATIC 9], const uint64_t x[S2N_BIGNUM_STATIC 9], const uint64_t y[S2N_BIGNUM_STATIC 9]);

// Subtract modulo p_521, z := (x - y) mod p_521
// Inputs x[9], y[9]; output z[9]
extern void bignum_sub_p521(uint64_t z[S2N_BIGNUM_STATIC 9], const uint64_t x[S2N_BIGNUM_STATIC 9], const uint64_t y[S2N_BIGNUM_STATIC 9]);

// Negate modulo p_521, z := (-x) mod p_521, assuming x reduced
// Input x[9]; output z[9]
extern void bignum_neg_p521(uint64_t z[S2N_BIGNUM_STATIC 9], const uint64_t x[S2N_BIGNUM_STATIC 9]);

// Multiply modulo p_521, z := (x * y) mod p_521, assuming x and y reduced
// Inputs x[9], y[9]; output z[9]
extern void bignum_mul_p521(uint64_t z[S2N_BIGNUM_STATIC 9], const uint64_t x[S2N_BIGNUM_STATIC 9], const uint64_t y[S2N_BIGNUM_STATIC 9]);
extern void bignum_mul_p521_alt(uint64_t z[S2N_BIGNUM_STATIC 9], const uint64_t x[S2N_BIGNUM_STATIC 9], const uint64_t y[S2N_BIGNUM_STATIC 9]);
static inline void bignum_mul_p521_selector(uint64_t z[S2N_BIGNUM_STATIC 9], const uint64_t x[S2N_BIGNUM_STATIC 9], const uint64_t y[S2N_BIGNUM_STATIC 9]) {
  if (use_s2n_bignum_alt()) { bignum_mul_p521_alt(z, x, y); }
  else { bignum_mul_p521(z, x, y); }
}

// Square modulo p_521, z := (x^2) mod p_521, assuming x reduced
// Input x[9]; output z[9]
extern void bignum_sqr_p521(uint64_t z[S2N_BIGNUM_STATIC 9], const uint64_t x[S2N_BIGNUM_STATIC 9]);
extern void bignum_sqr_p521_alt(uint64_t z[S2N_BIGNUM_STATIC 9], const uint64_t x[S2N_BIGNUM_STATIC 9]);
static inline void bignum_sqr_p521_selector(uint64_t z[S2N_BIGNUM_STATIC 9], const uint64_t x[S2N_BIGNUM_STATIC 9]) {
  if (use_s2n_bignum_alt()) { bignum_sqr_p521_alt(z, x); }
  else { bignum_sqr_p521(z, x); }
}

// Convert little-endian bytes to 9-digit 528-bit bignum
extern void bignum_fromlebytes_p521(uint64_t z[S2N_BIGNUM_STATIC 9], const uint8_t x[S2N_BIGNUM_STATIC 66]);

// Convert 9-digit 528-bit bignum to little-endian bytes
extern void bignum_tolebytes_p521(uint8_t z[S2N_BIGNUM_STATIC 66], const uint64_t x[S2N_BIGNUM_STATIC 9]);

extern void p521_jdouble(uint64_t p3[S2N_BIGNUM_STATIC 27],uint64_t p1[S2N_BIGNUM_STATIC 27]);
extern void p521_jdouble_alt(uint64_t p3[S2N_BIGNUM_STATIC 27],uint64_t p1[S2N_BIGNUM_STATIC 27]);
static inline void p521_jdouble_selector(uint64_t p3[S2N_BIGNUM_STATIC 27],uint64_t p1[S2N_BIGNUM_STATIC 27]) {
    if (use_s2n_bignum_alt()) { p521_jdouble_alt(p3, p1); }
    else { p521_jdouble(p3, p1); }
}
extern void p521_jscalarmul(uint64_t res[S2N_BIGNUM_STATIC 27], const uint64_t scalar[S2N_BIGNUM_STATIC 9], const uint64_t point[S2N_BIGNUM_STATIC 27]);
extern void p521_jscalarmul_alt(uint64_t res[S2N_BIGNUM_STATIC 27], const uint64_t scalar[S2N_BIGNUM_STATIC 9], const uint64_t point[S2N_BIGNUM_STATIC 27]);
static inline void p521_jscalarmul_selector(uint64_t res[S2N_BIGNUM_STATIC 27], const uint64_t scalar[S2N_BIGNUM_STATIC 9], const uint64_t point[S2N_BIGNUM_STATIC 27]) {
    if (use_s2n_bignum_alt()) { p521_jscalarmul_alt(res, scalar, point); }
    else { p521_jscalarmul(res, scalar, point); }
}

// Modular inverse modulo p_521 =  2^521 - 1
//   z = x^-1 mod p_521.
// The function is constant-time.
extern void bignum_inv_p521(uint64_t z[S2N_BIGNUM_STATIC 9], const uint64_t x[S2N_BIGNUM_STATIC 9]);

// curve25519_x25519_byte and curve25519_x25519_byte_alt computes the x25519
// function specified in https://www.rfc-editor.org/rfc/rfc7748. |scalar| is the
// scalar, |point| is the u-coordinate of the elliptic curve
// point. The result, another u-coordinate, is saved in |res|.
extern void curve25519_x25519_byte(uint8_t res[S2N_BIGNUM_STATIC 32], const uint8_t scalar[S2N_BIGNUM_STATIC 32], const uint8_t point[S2N_BIGNUM_STATIC 32]);
extern void curve25519_x25519_byte_alt(uint8_t res[S2N_BIGNUM_STATIC 32], const uint8_t scalar[S2N_BIGNUM_STATIC 32], const uint8_t point[S2N_BIGNUM_STATIC 32]);
static inline void curve25519_x25519_byte_selector(uint8_t res[S2N_BIGNUM_STATIC 32], const uint8_t scalar[S2N_BIGNUM_STATIC 32], const uint8_t point[S2N_BIGNUM_STATIC 32]) {
  if (use_s2n_bignum_alt()) { curve25519_x25519_byte_alt(res, scalar, point); }
  else { curve25519_x25519_byte(res, scalar, point); }
}

// curve25519_x25519base_byte and curve25519_x25519base_byte_alt computes the
// x25519 function specified in https://www.rfc-editor.org/rfc/rfc7748 using the
// basepoint specified in section 4.1. |scalar| is the scalar. The result,
// another u-coordinate, is saved in |res|.
extern void curve25519_x25519base_byte(uint8_t res[S2N_BIGNUM_STATIC 32], const uint8_t scalar[S2N_BIGNUM_STATIC 32]);
extern void curve25519_x25519base_byte_alt(uint8_t res[S2N_BIGNUM_STATIC 32], const uint8_t scalar[S2N_BIGNUM_STATIC 32]);
static inline void curve25519_x25519base_byte_selector(uint8_t res[S2N_BIGNUM_STATIC 32], const uint8_t scalar[S2N_BIGNUM_STATIC 32]) {
  if (use_s2n_bignum_alt()) { curve25519_x25519base_byte_alt(res, scalar); }
  else { curve25519_x25519base_byte(res, scalar); }
}

// Evaluate z := x^2 where x is a 2048-bit integer.
// Input: x[32]; output: z[64]; temporary buffer: t[>=72]
#define S2NBIGNUM_KSQR_32_64_TEMP_NWORDS 72
extern void
bignum_ksqr_32_64(uint64_t z[S2N_BIGNUM_STATIC 64], const uint64_t x[S2N_BIGNUM_STATIC 32],
                  uint64_t t[S2N_BIGNUM_STATIC S2NBIGNUM_KSQR_32_64_TEMP_NWORDS]);
extern void
bignum_ksqr_32_64_neon(uint64_t z[S2N_BIGNUM_STATIC 64], const uint64_t x[S2N_BIGNUM_STATIC 32],
                       uint64_t t[S2N_BIGNUM_STATIC S2NBIGNUM_KSQR_32_64_TEMP_NWORDS]);

// Evaluate z := x^2 where x is a 1024-bit integer.
// Input: x[16]; output: z[32]; temporary buffer: t[>=24]
#define S2NBIGNUM_KSQR_16_32_TEMP_NWORDS 24
extern void
bignum_ksqr_16_32(uint64_t z[S2N_BIGNUM_STATIC 32], const uint64_t x[S2N_BIGNUM_STATIC 16],
                  uint64_t t[S2N_BIGNUM_STATIC S2NBIGNUM_KSQR_16_32_TEMP_NWORDS]);
extern void
bignum_ksqr_16_32_neon(uint64_t z[S2N_BIGNUM_STATIC 32], const uint64_t x[S2N_BIGNUM_STATIC 16],
                       uint64_t t[S2N_BIGNUM_STATIC S2NBIGNUM_KSQR_16_32_TEMP_NWORDS]);

// Evaluate z := x * y where x and y are 2048-bit integers.
// Inputs: x[32], y[32]; output: z[64]; temporary buffer t[>=96]
#define S2NBIGNUM_KMUL_32_64_TEMP_NWORDS 96
extern void
bignum_kmul_32_64(uint64_t z[S2N_BIGNUM_STATIC 64], const uint64_t x[S2N_BIGNUM_STATIC 32],
                  const uint64_t y[S2N_BIGNUM_STATIC 32],
                  uint64_t t[S2N_BIGNUM_STATIC S2NBIGNUM_KMUL_32_64_TEMP_NWORDS]);
extern void
bignum_kmul_32_64_neon(uint64_t z[S2N_BIGNUM_STATIC 64], const uint64_t x[S2N_BIGNUM_STATIC 32],
                       const uint64_t y[S2N_BIGNUM_STATIC 32],
                       uint64_t t[S2N_BIGNUM_STATIC S2NBIGNUM_KMUL_32_64_TEMP_NWORDS]);

// Evaluate z := x * y where x and y are 1024-bit integers.
// Inputs: x[16], y[16]; output: z[32]; temporary buffer t[>=32]
#define S2NBIGNUM_KMUL_16_32_TEMP_NWORDS 32
extern void
bignum_kmul_16_32(uint64_t z[S2N_BIGNUM_STATIC 32], const uint64_t x[S2N_BIGNUM_STATIC 16],
                  const uint64_t y[S2N_BIGNUM_STATIC 16],
                  uint64_t t[S2N_BIGNUM_STATIC S2NBIGNUM_KMUL_16_32_TEMP_NWORDS]);
extern void
bignum_kmul_16_32_neon(uint64_t z[S2N_BIGNUM_STATIC 32], const uint64_t x[S2N_BIGNUM_STATIC 16],
                       const uint64_t y[S2N_BIGNUM_STATIC 16],
                       uint64_t t[S2N_BIGNUM_STATIC S2NBIGNUM_KMUL_16_32_TEMP_NWORDS]);

// Extended Montgomery reduce in 8-digit blocks.
// Assumes that z initially holds a 2k-digit bignum z_0, m is a k-digit odd
// bignum and m * w == -1 (mod 2^64). This function also uses z for the output
// as well as returning a carry c of 0 or 1. This encodes two numbers: in the
// lower half of the z buffer we have q = z[0..k-1], while the upper half
// together with the carry gives r = 2^{64k}*c + z[k..2k-1]. These values
// satisfy z_0 + q * m = 2^{64k} * r, i.e. r gives a raw (unreduced) Montgomery
// reduction while q gives the multiplier that was used.
// Note that q = (z_0 mod 2^{64k}) * (-m^-1 mod 2^{64k}) mod 2^{64k}.
//    z_0 + q * m = 0           mod 2^{64k}
//          q * m = -z_0        mod 2^{64k}
//          q     = -z_0 * m^-1 mod 2^{64k}
//                = (z_0 mod 2^{64k}) * (-m^-1 mod 2^{64k}) mod 2^{64k}
// q is uniquely determined because q must be in the range of [0, 2^{64k}-1].
// Inputs: z[2*k], m[k], w; outputs: function return (extra result bit) and z[2*k]
extern uint64_t bignum_emontredc_8n(uint64_t k, uint64_t *z, const uint64_t *m,
                                    uint64_t w);
extern uint64_t bignum_emontredc_8n_neon(uint64_t k, uint64_t *z, const uint64_t *m,
                                         uint64_t w);

// Optionally subtract, z := x - y (if p nonzero) or z := x (if p zero)
// Inputs: x[k], p, y[k]; outputs: function return (carry-out) and z[k]
extern uint64_t bignum_optsub(uint64_t k, uint64_t *z, const uint64_t *x, uint64_t p,
                              const uint64_t *y);

// Compare bignums, x >= y.
// Inputs: x[m], y[n]; output: function return (1 if x >= y)
extern uint64_t bignum_ge(uint64_t m, const uint64_t *x, uint64_t n, const uint64_t *y);

// General big-integer multiplication (z := x * y).
// Inputs: x[m], y[n]; output: z[k]. If k < m+n, the result is truncated.
extern void bignum_mul(uint64_t k, uint64_t *z, uint64_t m, const uint64_t *x,
                       uint64_t n, const uint64_t *y);

// General big-integer squaring (z := x^2).
// Inputs: x[m]; output: z[k]. If k < 2m, the result is truncated.
extern void bignum_sqr(uint64_t k, uint64_t *z, uint64_t m, const uint64_t *x);

// Given table: uint64_t[height*width], copy table[idx*width...(idx+1)*width-1]
// into z[0..row-1].
// This function is constant-time with respect to the value of `idx`. This is
// achieved by reading the whole table and using the bit-masking to get the
// `idx`-th row.
// Input table[height*width]; output z[width]
extern void bignum_copy_row_from_table (uint64_t *z, const uint64_t *table,
        uint64_t height, uint64_t width, uint64_t idx);

// Given table: uint64_t[height*width], copy table[idx*width...(idx+1)*width-1]
// into z[0..row-1]. width must be a multiple of 8.
// This function is constant-time with respect to the value of `idx`. This is
// achieved by reading the whole table and using the bit-masking to get the
// `idx`-th row.
// Input table[height*width]; output z[width]
extern void bignum_copy_row_from_table_8n_neon (uint64_t *z, const uint64_t *table,
        uint64_t height, uint64_t width, uint64_t idx);

// Given table: uint64_t[height*16], copy table[idx*16...(idx+1)*16-1] into z[0..row-1].
// This function is constant-time with respect to the value of `idx`. This is
// achieved by reading the whole table and using the bit-masking to get the
// `idx`-th row.
// Input table[height*16]; output z[16]
extern void bignum_copy_row_from_table_16_neon (uint64_t *z, const uint64_t *table,
        uint64_t height, uint64_t idx);

// Given table: uint64_t[height*32], copy table[idx*32...(idx+1)*32-1] into z[0..row-1].
// This function is constant-time with respect to the value of `idx`. This is
// achieved by reading the whole table and using the bit-masking to get the
// `idx`-th row.
// Input table[height*32]; output z[32]
extern void bignum_copy_row_from_table_32_neon (uint64_t *z, const uint64_t *table,
        uint64_t height, uint64_t idx);

// Reduction is modulo the order of the curve25519/edwards25519 basepoint,
// which is n_25519 = 2^252 + 27742317777372353535851937790883648493.
// Reduce modulo basepoint order, z := x mod n_25519
// Input x[k]; output z[4]
extern void bignum_mod_n25519(uint64_t z[S2N_BIGNUM_STATIC 4], uint64_t k, uint64_t *x);

// Negate modulo p_25519, z := (-x) mod p_25519, assuming x reduced
// Input x[4]; output z[4]
extern void bignum_neg_p25519(uint64_t z[S2N_BIGNUM_STATIC 4], uint64_t x[S2N_BIGNUM_STATIC 4]);

// Performs z := (x * y + c) mod n_25519, where the modulus is
// n_25519 = 2^252 + 27742317777372353535851937790883648493, the
// order of the curve25519/edwards25519 basepoint. The result z
// and the inputs x, y and c are all 4 digits (256 bits).
// Inputs x[4], y[4], c[4]; output z[4]
extern void bignum_madd_n25519(uint64_t z[S2N_BIGNUM_STATIC 4], uint64_t x[S2N_BIGNUM_STATIC 4],
        uint64_t y[S2N_BIGNUM_STATIC 4], uint64_t c[S2N_BIGNUM_STATIC 4]);
extern void bignum_madd_n25519_alt(uint64_t z[S2N_BIGNUM_STATIC 4], uint64_t x[S2N_BIGNUM_STATIC 4],
        uint64_t y[S2N_BIGNUM_STATIC 4], uint64_t c[S2N_BIGNUM_STATIC 4]);
static inline void bignum_madd_n25519_selector(uint64_t z[S2N_BIGNUM_STATIC 4], uint64_t x[S2N_BIGNUM_STATIC 4], uint64_t y[S2N_BIGNUM_STATIC 4], uint64_t c[S2N_BIGNUM_STATIC 4]) {
  if (use_s2n_bignum_alt()) { bignum_madd_n25519_alt(z, x, y, c); }
  else { bignum_madd_n25519(z, x, y, c); }
}

// This assumes that the input buffer p points to a pair of 256-bit
// numbers x (at p) and y (at p+4) representing a point (x,y) on the
// edwards25519 curve. It is assumed that both x and y are < p_25519
// but there is no checking of this, nor of the fact that (x,y) is
// in fact on the curve.
//
// The output in z is a little-endian array of bytes corresponding to
// the standard compressed encoding of a point as 2^255 * x_0 + y
// where x_0 is the least significant bit of x.
// See "https://datatracker.ietf.org/doc/html/rfc8032#section-5.1.2"
// In this implementation, y is simply truncated to 255 bits, but if
// it is reduced mod p_25519 as expected this does not affect values.
extern void edwards25519_encode(uint8_t z[S2N_BIGNUM_STATIC 32], uint64_t p[S2N_BIGNUM_STATIC 8]);

// This interprets the input byte string as a little-endian number
// representing a point (x,y) on the edwards25519 curve, encoded as
// 2^255 * x_0 + y where x_0 is the least significant bit of x. It
// returns the full pair of coordinates x (at z) and y (at z+4). The
// return code is 0 for success and 1 for failure, which means that
// the input does not correspond to the encoding of any edwards25519
// point. This can happen for three reasons, where y = the lowest
// 255 bits of the input:
//
//  * y >= p_25519
//    Input y coordinate is not reduced
//  * (y^2 - 1) * (1 + d_25519 * y^2) has no modular square root
//    There is no x such that (x,y) is on the curve
//  * y^2 = 1 and top bit of input is set
//    Cannot be the canonical encoding of (0,1) or (0,-1)
//
// Input c[32] (bytes); output function return and z[8]
extern uint64_t edwards25519_decode(uint64_t z[S2N_BIGNUM_STATIC 8], const uint8_t c[S2N_BIGNUM_STATIC 32]);
extern uint64_t edwards25519_decode_alt(uint64_t z[S2N_BIGNUM_STATIC 8], const uint8_t c[S2N_BIGNUM_STATIC 32]);
static inline uint64_t edwards25519_decode_selector(uint64_t z[S2N_BIGNUM_STATIC 8], const uint8_t c[S2N_BIGNUM_STATIC 32]) {
  if (use_s2n_bignum_alt()) { return edwards25519_decode_alt(z, c); }
  else { return edwards25519_decode(z, c); }
}

// Given a scalar n, returns point (X,Y) = n * B where B = (...,4/5) is
// the standard basepoint for the edwards25519 (Ed25519) curve.
// Input scalar[4]; output res[8]
extern void edwards25519_scalarmulbase(uint64_t res[S2N_BIGNUM_STATIC 8], uint64_t scalar[S2N_BIGNUM_STATIC 4]);
extern void edwards25519_scalarmulbase_alt(uint64_t res[S2N_BIGNUM_STATIC 8], uint64_t scalar[S2N_BIGNUM_STATIC 4]);
static inline void edwards25519_scalarmulbase_selector(uint64_t res[S2N_BIGNUM_STATIC 8], uint64_t scalar[S2N_BIGNUM_STATIC 4]) {
  if (use_s2n_bignum_alt()) { edwards25519_scalarmulbase_alt(res, scalar); }
  else { edwards25519_scalarmulbase(res, scalar); }
}

// Given scalar = n, point = P and bscalar = m, returns in res
// the point (X,Y) = n * P + m * B where B = (...,4/5) is
// the standard basepoint for the edwards25519 (Ed25519) curve.
//
// Both 256-bit coordinates of the input point P are implicitly
// reduced modulo 2^255-19 if they are not already in reduced form,
// but the conventional usage is that they *are* already reduced.
// The scalars can be arbitrary 256-bit numbers but may also be
// considered as implicitly reduced modulo the group order.
//
// Input scalar[4], point[8], bscalar[4]; output res[8]
extern void edwards25519_scalarmuldouble(uint64_t res[S2N_BIGNUM_STATIC 8], uint64_t scalar[S2N_BIGNUM_STATIC 4],
        uint64_t point[S2N_BIGNUM_STATIC 8], uint64_t bscalar[S2N_BIGNUM_STATIC 4]);
extern void edwards25519_scalarmuldouble_alt(uint64_t res[S2N_BIGNUM_STATIC 8], uint64_t scalar[S2N_BIGNUM_STATIC 4],
        uint64_t point[S2N_BIGNUM_STATIC 8], uint64_t bscalar[S2N_BIGNUM_STATIC 4]);
static inline void edwards25519_scalarmuldouble_selector(uint64_t res[S2N_BIGNUM_STATIC 8], uint64_t scalar[S2N_BIGNUM_STATIC 4], uint64_t point[S2N_BIGNUM_STATIC 8], uint64_t bscalar[S2N_BIGNUM_STATIC 4]) {
  if (use_s2n_bignum_alt()) { edwards25519_scalarmuldouble_alt(res, scalar, point, bscalar); }
  else { edwards25519_scalarmuldouble(res, scalar, point, bscalar); }
}

#endif
