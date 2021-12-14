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
// Square modulo p_256k1, z := (x^2) mod p_256k1
// Input x[4]; output z[4]
//
//    extern void bignum_sqr_p256k1
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------

        .globl  bignum_sqr_p256k1
        .text
        .balign 4

#define z x0
#define x x1

// Variables

#define u0 x2
#define u1 x3
#define u2 x4
#define u3 x5
#define u4 x6
#define u5 x7
#define u6 x8
#define u7 x9

#define a0 x10
#define a1 x11
#define a2 x12
#define b0 x13
#define b1 x14
#define b3 x15
#define c x16
#define d x17

// Some additional aliases

#define l u4
#define h u5
#define b2 u6
#define q u4
#define a3 u7

bignum_sqr_p256k1:

// First just a near-clone of bignum_sqr_4_8 to get the square, using
// different registers to collect full product without writeback.

                ldp     u4, u5, [x]
                ldp     x10, x11, [x, #16]
                mul     u2, u4, x10
                mul     u7, u5, x11
                umulh   x12, u4, x10
                subs    x13, u4, u5
                cneg    x13, x13, cc
                csetm   u1, cc
                subs    u0, x11, x10
                cneg    u0, u0, cc
                mul     u6, x13, u0
                umulh   u0, x13, u0
                cinv    u1, u1, cc
                eor     u6, u6, u1
                eor     u0, u0, u1
                adds    u3, u2, x12
                adc     x12, x12, xzr
                umulh   x13, u5, x11
                adds    u3, u3, u7
                adcs    x12, x12, x13
                adc     x13, x13, xzr
                adds    x12, x12, u7
                adc     x13, x13, xzr
                cmn     u1, #0x1
                adcs    u3, u3, u6
                adcs    x12, x12, u0
                adc     x13, x13, u1
                adds    u2, u2, u2
                adcs    u3, u3, u3
                adcs    x12, x12, x12
                adcs    x13, x13, x13
                adc     x14, xzr, xzr
                mul     u0, u4, u4
                mul     u6, u5, u5
                mul     x15, u4, u5
                umulh   u1, u4, u4
                umulh   u7, u5, u5
                umulh   x16, u4, u5
                adds    u1, u1, x15
                adcs    u6, u6, x16
                adc     u7, u7, xzr
                adds    u1, u1, x15
                adcs    u6, u6, x16
                adc     u7, u7, xzr
                adds    u2, u2, u6
                adcs    u3, u3, u7
                adcs    x12, x12, xzr
                adcs    x13, x13, xzr
                adc     x14, x14, xzr
                mul     u4, x10, x10
                mul     u6, x11, x11
                mul     x15, x10, x11
                umulh   u5, x10, x10
                umulh   u7, x11, x11
                umulh   x16, x10, x11
                adds    u5, u5, x15
                adcs    u6, u6, x16
                adc     u7, u7, xzr
                adds    u5, u5, x15
                adcs    u6, u6, x16
                adc     u7, u7, xzr
                adds    u4, u4, x12
                adcs    u5, u5, x13
                adcs    u6, u6, x14
                adc     u7, u7, xzr

// Now we have the full 8-digit product 2^256 * h + l where
// h = [u7,u6,u5,u4] and l = [u3,u2,u1,u0]
// and this is == 4294968273 * h + l (mod p_256k1)
// Some of the word products are done straightforwardly using mul + umulh
// while others are broken down in a more complicated way as
// (2^32 + 977) * (2^32 * h + l) = 2^64 * h + 2^32 * (d * h + l) + d * l


                mov     d, #977
                orr     c, d, #0x100000000

                mul     a0, c, u4
                umulh   b0, c, u4

                and     l, u5, #0xFFFFFFFF
                lsr     h, u5, #32
                mul     a1, d, l
                madd    l, d, h, l
                adds    a1, a1, l, lsl #32
                lsr     l, l, #32
                adc     b1, h, l

                mul     a2, c, u6
                umulh   b2, c, u6

                and     l, u7, #0xFFFFFFFF
                lsr     h, u7, #32
                mul     a3, d, l
                madd    l, d, h, l
                adds    a3, a3, l, lsl #32
                lsr     l, l, #32
                adc     b3, h, l

                adds    u0, u0, a0
                adcs    u1, u1, a1
                adcs    u2, u2, a2
                adcs    u3, u3, a3
                cset    u4, cs

                adds    u1, u1, b0
                adcs    u2, u2, b1
                adcs    u3, u3, b2
                adc     u4, u4, b3

// Now we have reduced to 5 digits, 2^256 * h + l = [u4,u3,u2,u1,u0]
// Use q = h + 1 as the initial quotient estimate, either right or 1 too big.
// Since q <= 2^33 we do 4294968273 * q = (q<<32) + 977 * q to avoid umulh

                add     q, u4, #1
                mul     a0, d, q
                lsr     a1, q, #32
                adds    a0, a0, q, lsl #32
                adc     a1, xzr, a1
                adds    u0, u0, a0
                adcs    u1, u1, a1
                adcs    u2, u2, xzr
                adcs    u3, u3, xzr

// Now the effective answer is 2^256 * (CF - 1) + [u3,u2,u1,u0]
// So we correct if CF = 0 by subtracting 4294968273, i.e. by
// adding p_256k1 to the "full" answer

                csel    c, c, xzr, cc
                subs    u0, u0, c
                sbcs    u1, u1, xzr
                sbcs    u2, u2, xzr
                sbc     u3, u3, xzr

// Write back

                stp     u0, u1, [x0]
                stp     u2, u3, [x0, #16]

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
