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

// Add modulo p_384, z := (x + y) mod p_384, assuming x and y reduced
// Inputs x[6], y[6]; output z[6]
extern void bignum_add_p384(uint64_t z[static 6], const uint64_t x[static 6], const uint64_t y[static 6]);

// Convert from almost-Montgomery form, z := (x / 2^384) mod p_384
// Input x[6]; output z[6]
extern void bignum_deamont_p384(uint64_t z[static 6], const uint64_t x[static 6]);

// Convert from almost-Montgomery form, z := (x / 2^384) mod p_384
// Input x[6]; output z[6]
extern void bignum_deamont_p384_alt(uint64_t z[static 6], const uint64_t x[static 6]);

// Montgomery multiply, z := (x * y / 2^384) mod p_384 
// Inputs x[6], y[6]; output z[6]
extern void bignum_montmul_p384(uint64_t z[static 6], const uint64_t x[static 6], const uint64_t y[static 6]);

// Montgomery multiply, z := (x * y / 2^384) mod p_384 
// Inputs x[6], y[6]; output z[6]
extern void bignum_montmul_p384_alt(uint64_t z[static 6], const uint64_t x[static 6], const uint64_t y[static 6]);

// Montgomery square, z := (x^2 / 2^384) mod p_384
// Input x[6]; output z[6]
extern void bignum_montsqr_p384(uint64_t z[static 6], const uint64_t x[static 6]);

// Montgomery square, z := (x^2 / 2^384) mod p_384
// Input x[6]; output z[6]
extern void bignum_montsqr_p384_alt(uint64_t z[static 6], const uint64_t x[static 6]);

// Negate modulo p_384, z := (-x) mod p_384, assuming x reduced
// Input x[6]; output z[6]
extern void bignum_neg_p384(uint64_t z[static 6], const uint64_t x[static 6]);

// Subtract modulo p_384, z := (x - y) mod p_384
// Inputs x[6], y[6]; output z[6]
extern void bignum_sub_p384(uint64_t z[static 6], const uint64_t x[static 6], const uint64_t y[static 6]); 

// Convert to Montgomery form z := (2^384 * x) mod p_384 */
// Input x[6]; output z[6] */
extern void bignum_tomont_p384(uint64_t z[static 6], const uint64_t x[static 6]);

// Convert to Montgomery form z := (2^384 * x) mod p_384 */
// Input x[6]; output z[6] */
extern void bignum_tomont_p384_alt(uint64_t z[static 6], const uint64_t x[static 6]);

// Convert 6-digit (384-bit) bignum from little-endian form
// Input x[6]; output z[6]
extern void bignum_fromlebytes_6(uint64_t z[static 6], const uint8_t x[static 48]);

// Convert 6-digit (384-bit) bignum to little-endian form
// Input x[6]; output z[6]
extern void bignum_tolebytes_6(uint8_t z[static 48], const uint64_t x[static 6]);

// 384-bit nonzeroness test, returning 1 if x is nonzero, 0 if x is zero
// Input x[6]; output function return
extern uint64_t bignum_nonzero_6(const uint64_t x[static 6]);

// Add modulo p_521, z := (x + y) mod p_521, assuming x and y reduced
// Inputs x[9], y[9]; output z[9]
extern void bignum_add_p521(uint64_t z[static 9], const uint64_t x[static 9], const uint64_t y[static 9]);

// Subtract modulo p_521, z := (x - y) mod p_521
// Inputs x[9], y[9]; output z[9]
extern void bignum_sub_p521(uint64_t z[static 9], const uint64_t x[static 9], const uint64_t y[static 9]);

// Negate modulo p_521, z := (-x) mod p_521, assuming x reduced
// Input x[9]; output z[9]
extern void bignum_neg_p521(uint64_t z[static 9], const uint64_t x[static 9]);

// Multiply modulo p_521, z := (x * y) mod p_521, assuming x and y reduced
// Inputs x[9], y[9]; output z[9]
extern void bignum_mul_p521(uint64_t z[static 9], const uint64_t x[static 9], const uint64_t y[static 9]);

// Multiply modulo p_521, z := (x * y) mod p_521, assuming x and y reduced
// Inputs x[9], y[9]; output z[9]
extern void bignum_mul_p521_alt(uint64_t z[static 9], const uint64_t x[static 9], const uint64_t y[static 9]);

// Square modulo p_521, z := (x^2) mod p_521, assuming x reduced
// Input x[9]; output z[9]
extern void bignum_sqr_p521(uint64_t z[static 9], const uint64_t x[static 9]);

// Square modulo p_521, z := (x^2) mod p_521, assuming x reduced
// Input x[9]; output z[9]
extern void bignum_sqr_p521_alt(uint64_t z[static 9], const uint64_t x[static 9]);

// Convert little-endian bytes to 9-digit 528-bit bignum
extern void bignum_fromlebytes_p521(uint64_t z[static 9], const uint8_t x[static 66]);

// Convert 9-digit 528-bit bignum to little-endian bytes
extern void bignum_tolebytes_p521(uint8_t z[static 66], const uint64_t x[static 9]);

// curve25519_x25519_byte and curve25519_x25519_byte_alt computes the x25519
// function specified in https://www.rfc-editor.org/rfc/rfc7748. |scalar| is the
// scalar, |point| is the u-coordinate of the elliptic curve
// point. The result, another u-coordinate, is saved in |res|.
extern void curve25519_x25519_byte(uint8_t res[static 32], const uint8_t scalar[static 32], const uint8_t point[static 32]);
extern void curve25519_x25519_byte_alt(uint8_t res[static 32], const uint8_t scalar[static 32], const uint8_t point[static 32]);

// curve25519_x25519base_byte and curve25519_x25519base_byte_alt computes the
// x25519 function specified in https://www.rfc-editor.org/rfc/rfc7748 using the
// basepoint specified in section 4.1. |scalar| is the scalar. The result,
// another u-coordinate, is saved in |res|.
extern void curve25519_x25519base_byte(uint8_t res[static 32], const uint8_t scalar[static 32]);
extern void curve25519_x25519base_byte_alt(uint8_t res[static 32], const uint8_t scalar[static 32]);
