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
// Multiply z := x * y
// Inputs x[4], y[4]; output z[8]
//
//    extern void bignum_mul_4_8_alt
//      (uint64_t z[static 8], uint64_t x[static 4], uint64_t y[static 4]);
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = y
// ----------------------------------------------------------------------------

        .globl  bignum_mul_4_8_alt
        .text
        .balign 4

#define z x0
#define x x1
#define y x2

#define a0 x3
#define a1 x4
#define a2 x5
#define a3 x6
#define b0 x7
#define b1 x8
#define b2 x9
#define b3 x10

#define h x11
#define l x12

#define u0 x13
#define u1 x14
#define u2 x15
#define u3 x16

// These alias to the input arguments when no longer needed

#define u4 a0
#define u5 a1
#define u6 a2
#define u7 a3

bignum_mul_4_8_alt:

// Load operands and set up row 0 = [u4;...;u0] = a0 * [b3;...;b0]

                ldp     a0, a1, [x]
                ldp     b0, b1, [y]

                mul     u0, a0, b0
                umulh   u1, a0, b0
                mul     l, a0, b1
                umulh   u2, a0, b1
                adds    u1, u1, l

                ldp     b2, b3, [y, #16]

                mul     l, a0, b2
                umulh   u3, a0, b2
                adcs    u2, u2, l

                mul     l, a0, b3
                umulh   u4, a0, b3
                adcs    u3, u3, l
                adc     u4, u4, xzr

                ldp     a2, a3, [x, #16]

// Row 1 = [u5;...;u0] = [a1;a0] * [b3;...;b0]

                mul     l, a1, b0
                umulh   h, a1, b0
                adds    u1, u1, l

                adcs    u2, u2, h
                mul     l, a1, b1
                umulh   h, a1, b1
                adc     h, h, xzr
                adds    u2, u2, l

                adcs    u3, u3, h
                mul     l, a1, b2
                umulh   h, a1, b2
                adc     h, h, xzr
                adds    u3, u3, l

                adcs    u4, u4, h
                mul     l, a1, b3
                umulh   h, a1, b3
                adc     h, h, xzr
                adds    u4, u4, l
                adc     u5, h, xzr

// Row 2 = [u6;...;u0] = [a2;a1;a0] * [b3;...;b0]

                mul     l, a2, b0
                umulh   h, a2, b0
                adds    u2, u2, l

                adcs    u3, u3, h
                mul     l, a2, b1
                umulh   h, a2, b1
                adc     h, h, xzr
                adds    u3, u3, l

                adcs    u4, u4, h
                mul     l, a2, b2
                umulh   h, a2, b2
                adc     h, h, xzr
                adds    u4, u4, l

                adcs    u5, u5, h
                mul     l, a2, b3
                umulh   h, a2, b3
                adc     h, h, xzr
                adds    u5, u5, l
                adc     u6, h, xzr

// Row 3 = [u7;...;u0] = [a3;...a0] * [b3;...;b0]

                mul     l, a3, b0
                umulh   h, a3, b0
                adds    u3, u3, l

                adcs    u4, u4, h
                mul     l, a3, b1
                umulh   h, a3, b1
                adc     h, h, xzr
                adds    u4, u4, l

                adcs    u5, u5, h
                mul     l, a3, b2
                umulh   h, a3, b2
                adc     h, h, xzr
                adds    u5, u5, l

                adcs    u6, u6, h
                mul     l, a3, b3
                umulh   h, a3, b3
                adc     h, h, xzr
                adds    u6, u6, l
                adc     u7, h, xzr

// Store back final result [a3;...a0] * [b3;...;b0] = a * b

                stp     u0, u1, [z]
                stp     u2, u3, [z, #16]
                stp     u4, u5, [z, #32]
                stp     u6, u7, [z, #48]

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
