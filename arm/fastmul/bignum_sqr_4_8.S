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
// Square, z := x^2
// Input x[4]; output z[8]
//
//    extern void bignum_sqr_4_8 (uint64_t z[static 8], uint64_t x[static 4]);
//
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------

        .globl  bignum_sqr_4_8
        .text
        .balign 4

// ---------------------------------------------------------------------------
// Macro returning (c,h,l) = 3-word 1s complement (x - y) * (w - z)
// c,h,l,t should all be different
// t,h should not overlap w,z
// ---------------------------------------------------------------------------

.macro muldiffn c,h,l, t, x,y, w,z
        subs    \t, \x, \y
        cneg    \t, \t, cc
        csetm   \c, cc
        subs    \h, \w, \z
        cneg    \h, \h, cc
        mul     \l, \t, \h
        umulh   \h, \t, \h
        cinv    \c, \c, cc
        eor     \l, \l, \c
        eor     \h, \h, \c
.endm

// ---------------------------------------------------------------------------
// Start with ADK version of 2x2->4 mul
// Then we double that and add the two sub-squares
// ---------------------------------------------------------------------------

#define a0 x2
#define a1 x3
#define a2 x4
#define a3 x5

#define m0 x6
#define m1 x7
#define m2 x8
#define m3 x9
#define m4 x10

#define c1 x11
#define h1 x12
#define l1 x13
#define l2 x14

bignum_sqr_4_8:

// Load all the elements

        ldp     a0, a1, [x1]
        ldp     a2, a3, [x1,#16]

// Do a 2x2->4 mul of the cross product, retaining in m4 + [m3,m2,m1,m0]

        mul     m0, a0, a2
        mul     l2, a1, a3
        umulh   m2, a0, a2
        muldiffn c1,h1,l1, m3, a0,a1, a3,a2

        adds    m1, m0, m2
        adc     m2, m2, xzr

        umulh   m3, a1, a3

        adds    m1, m1, l2
        adcs    m2, m2, m3
        adc     m3, m3, xzr
        adds    m2, m2, l2
        adc     m3, m3, xzr

        adds    xzr, c1, #1
        adcs    m1, m1, l1
        adcs    m2, m2, h1
        adc     m3, m3, c1

// Double that

        adds    m0, m0, m0
        adcs    m1, m1, m1
        adcs    m2, m2, m2
        adcs    m3, m3, m3
        adc     m4, xzr, xzr

// Compute square of lower half

#define c0 x12
#define c2 x13
#define c3 x14
#define d1 x15
#define d2 x16

        mul     c0, a0, a0
        mul     c2, a1, a1
        mul     d1, a0, a1

        umulh   c1, a0, a0
        umulh   c3, a1, a1
        umulh   d2, a0, a1

        adds    c1, c1, d1
        adcs    c2, c2, d2
        adc     c3, c3, xzr

        adds    c1, c1, d1
        adcs    c2, c2, d2
        adc     c3, c3, xzr

// Write back lower part, add upper part to mid-term

        stp     c0, c1, [x0]

        adds    m0, m0, c2
        adcs    m1, m1, c3
        adcs    m2, m2, xzr
        adcs    m3, m3, xzr
        adc     m4, m4, xzr

        stp     m0, m1, [x0, #16]

// Compute square of upper half as [c3,c2,c1,c0]

        mul     c0, a2, a2
        mul     c2, a3, a3
        mul     d1, a2, a3

        umulh   c1, a2, a2
        umulh   c3, a3, a3
        umulh   d2, a2, a3

        adds    c1, c1, d1
        adcs    c2, c2, d2
        adc     c3, c3, xzr

        adds    c1, c1, d1
        adcs    c2, c2, d2
        adc     c3, c3, xzr

// Add up and write back

        adds    c0, c0, m2
        adcs    c1, c1, m3
        stp     c0, c1, [x0,#32]
        adcs    c2, c2, m4
        adc     c3, c3, xzr
        stp     c2, c3, [x0,#48]

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
