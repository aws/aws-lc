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
//    extern void bignum_mul_4_8
//      (uint64_t z[static 8], uint64_t x[static 4], uint64_t y[static 4]);
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = y
// ----------------------------------------------------------------------------

.globl bignum_mul_4_8

// ---------------------------------------------------------------------------
// Macro computing [c,b,a] := [b,a] + (x - y) * (w - z), adding with carry
// to the [b,a] components but leaving CF aligned with the c term, which is
// a sign bitmask for (x - y) * (w - z). Continued add-with-carry operations
// with [c,...,c] will continue the carry chain correctly starting from
// the c position if desired to add to a longer term of the form [...,b,a].
//
// c,h,l,t should all be different and t,h should not overlap w,z.
// ---------------------------------------------------------------------------

.macro muldiffnadd b,a, c,h,l,t, x,y, w,z
        subs    \t, \x, \y
        cneg    \t, \t, cc
        csetm   \c, cc
        subs    \h, \w, \z
        cneg    \h, \h, cc
        mul     \l, \t, \h
        umulh   \h, \t, \h
        cinv    \c, \c, cc
        adds    xzr, \c, 1
        eor     \l, \l, \c
        adcs    \a, \a, \l
        eor     \h, \h, \c
        adcs    \b, \b, \h
.endm

// ---------------------------------------------------------------------------
// ADK version of 4x4->8
// ---------------------------------------------------------------------------

#define a0 x3
#define a1 x4
#define a2 x5
#define a3 x6
#define b0 x7
#define b1 x8
#define b2 x9
#define b3 x10

#define s0 x11
#define s1 x12
#define s2 x13
#define s3 x14
#define s4 x15

#define m x15

#define t0 x11
#define t1 x16
#define t2 x12
#define t3 x13
#define t4 x14
#define t5 x15

#define u0 x11
#define u1 x16
#define u2 x1
#define u3 x2
#define u4 x12
#define u5 x13
#define u6 x14
#define u7 x15

#define c x11
#define h x17
#define l x19
#define t x20

bignum_mul_4_8:

                stp     x19, x20, [sp, -16]!

// Load operands

                ldp     a0, a1, [x1]
                ldp     b0, b1, [x2]
                ldp     a2, a3, [x1, 16]
                ldp     b2, b3, [x2, 16]

// First accumulate all the "simple" products as [s4,s3,s2,s1,s0]

                mul     s0, a0, b0
                mul     s1, a1, b1
                mul     s2, a2, b2
                mul     s3, a3, b3

                umulh   m, a0, b0
                adds    s1, s1, m
                umulh   m, a1, b1
                adcs    s2, s2, m
                umulh   m, a2, b2
                adcs    s3, s3, m
                umulh   m, a3, b3
                adc     s4, m, xzr

// Multiply by B + 1 to get [t5;t4;t3;t2;t1;t0] where t0 == s0

                adds    t1, s1, s0
                adcs    t2, s2, s1
                adcs    t3, s3, s2
                adcs    t4, s4, s3
                adc     t5, xzr, s4

// Multiply by B^2 + 1 to get [u6;u5;u4;u3;u2;u1;-], writing back LSD
// u0 == t0 == s0 and u1 == t1

                str     u0, [x0]
                adds    u2, t2, t0
                adcs    u3, t3, t1
                adcs    u4, t4, t2
                adcs    u5, t5, t3
                adcs    u6, xzr, t4
                adc     u7, xzr, t5

// Now add in all the "complicated" terms.

                muldiffnadd u6,u5, c,h,l,t, a2,a3, b3,b2
                adc     u7, u7, c

                muldiffnadd u2,u1, c,h,l,t, a0,a1, b1,b0
                str     u1, [x0, 8]
                adcs    u3, u3, c
                adcs    u4, u4, c
                adcs    u5, u5, c
                adcs    u6, u6, c
                adc     u7, u7, c

                muldiffnadd u5,u4, c,h,l,t, a1,a3, b3,b1
                adcs    u6, u6, c
                adc     u7, u7, c

                muldiffnadd u3,u2, c,h,l,t, a0,a2, b2,b0
                adcs    u4, u4, c
                adcs    u5, u5, c
                adcs    u6, u6, c
                adc     u7, u7, c

                muldiffnadd u4,u3, c,h,l,t, a0,a3, b3,b0
                adcs    u5, u5, c
                adcs    u6, u6, c
                adc     u7, u7, c
                muldiffnadd u4,u3, c,h,l,t, a1,a2, b2,b1
                adcs    u5, u5, c
                adcs    u6, u6, c
                adc     u7, u7, c

                stp     u2, u3, [x0, 16]
                stp     u4, u5, [x0, 32]
                stp     u6, u7, [x0, 48]

// Restore regs and return

                ldp     x19, x20, [sp], 16

                ret
