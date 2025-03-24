// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point doubling on NIST curve P-521 in Jacobian coordinates
//
//    extern void p521_jdouble_alt
//      (uint64_t p3[static 27],uint64_t p1[static 27]);
//
// Does p3 := 2 * p1 where all points are regarded as Jacobian triples.
// A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3).
// It is assumed that all coordinates of the input point are fully
// reduced mod p_521 and that the z coordinate is not zero.
//
// Standard ARM ABI: X0 = p3, X1 = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p521_jdouble_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p521_jdouble_alt)

        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 72

// Stable homes for input arguments during main code sequence

#define input_z x26
#define input_x x27

// Pointer-offset pairs for inputs and outputs

#define x_1 input_x, #0
#define y_1 input_x, #NUMSIZE
#define z_1 input_x, #(2*NUMSIZE)

#define x_3 input_z, #0
#define y_3 input_z, #NUMSIZE
#define z_3 input_z, #(2*NUMSIZE)

// Pointer-offset pairs for temporaries

#define z2 sp, #(NUMSIZE*0)
#define y2 sp, #(NUMSIZE*1)
#define x2p sp, #(NUMSIZE*2)
#define xy2 sp, #(NUMSIZE*3)

#define y4 sp, #(NUMSIZE*4)
#define t2 sp, #(NUMSIZE*4)

#define dx2 sp, #(NUMSIZE*5)
#define t1 sp, #(NUMSIZE*5)

#define d sp, #(NUMSIZE*6)
#define x4p sp, #(NUMSIZE*6)

// NUMSIZE*7 is not 16-aligned so we round it up

#define NSPACE (NUMSIZE*7+8)

// Corresponds exactly to bignum_mul_p521_alt

#define mul_p521(P0,P1,P2)                      \
        ldp     x3, x4, [P1] ASM_LINE_END                   \
        ldp     x5, x6, [P2] ASM_LINE_END                   \
        mul     x15, x3, x5 ASM_LINE_END                    \
        umulh   x16, x3, x5 ASM_LINE_END                    \
        mul     x14, x3, x6 ASM_LINE_END                    \
        umulh   x17, x3, x6 ASM_LINE_END                    \
        adds    x16, x16, x14 ASM_LINE_END                  \
        ldp     x7, x8, [P2+16] ASM_LINE_END                \
        mul     x14, x3, x7 ASM_LINE_END                    \
        umulh   x19, x3, x7 ASM_LINE_END                    \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        mul     x14, x3, x8 ASM_LINE_END                    \
        umulh   x20, x3, x8 ASM_LINE_END                    \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        ldp     x9, x10, [P2+32] ASM_LINE_END               \
        mul     x14, x3, x9 ASM_LINE_END                    \
        umulh   x21, x3, x9 ASM_LINE_END                    \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        mul     x14, x3, x10 ASM_LINE_END                   \
        umulh   x22, x3, x10 ASM_LINE_END                   \
        adcs    x21, x21, x14 ASM_LINE_END                  \
        ldp     x11, x12, [P2+48] ASM_LINE_END              \
        mul     x14, x3, x11 ASM_LINE_END                   \
        umulh   x23, x3, x11 ASM_LINE_END                   \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        ldr     x13, [P2+64] ASM_LINE_END                   \
        mul     x14, x3, x12 ASM_LINE_END                   \
        umulh   x24, x3, x12 ASM_LINE_END                   \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        mul     x14, x3, x13 ASM_LINE_END                   \
        umulh   x1, x3, x13 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        adc     x1, x1, xzr ASM_LINE_END                    \
        mul     x14, x4, x5 ASM_LINE_END                    \
        adds    x16, x16, x14 ASM_LINE_END                  \
        mul     x14, x4, x6 ASM_LINE_END                    \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        mul     x14, x4, x7 ASM_LINE_END                    \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        mul     x14, x4, x8 ASM_LINE_END                    \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        mul     x14, x4, x9 ASM_LINE_END                    \
        adcs    x21, x21, x14 ASM_LINE_END                  \
        mul     x14, x4, x10 ASM_LINE_END                   \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        mul     x14, x4, x11 ASM_LINE_END                   \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        mul     x14, x4, x12 ASM_LINE_END                   \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        mul     x14, x4, x13 ASM_LINE_END                   \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        cset    x0, hs ASM_LINE_END                         \
        umulh   x14, x4, x5 ASM_LINE_END                    \
        adds    x17, x17, x14 ASM_LINE_END                  \
        umulh   x14, x4, x6 ASM_LINE_END                    \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        umulh   x14, x4, x7 ASM_LINE_END                    \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        umulh   x14, x4, x8 ASM_LINE_END                    \
        adcs    x21, x21, x14 ASM_LINE_END                  \
        umulh   x14, x4, x9 ASM_LINE_END                    \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        umulh   x14, x4, x10 ASM_LINE_END                   \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        umulh   x14, x4, x11 ASM_LINE_END                   \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        umulh   x14, x4, x12 ASM_LINE_END                   \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        umulh   x14, x4, x13 ASM_LINE_END                   \
        adc     x0, x0, x14 ASM_LINE_END                    \
        stp     x15, x16, [P0] ASM_LINE_END                 \
        ldp     x3, x4, [P1+16] ASM_LINE_END                \
        mul     x14, x3, x5 ASM_LINE_END                    \
        adds    x17, x17, x14 ASM_LINE_END                  \
        mul     x14, x3, x6 ASM_LINE_END                    \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        mul     x14, x3, x7 ASM_LINE_END                    \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        mul     x14, x3, x8 ASM_LINE_END                    \
        adcs    x21, x21, x14 ASM_LINE_END                  \
        mul     x14, x3, x9 ASM_LINE_END                    \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        mul     x14, x3, x10 ASM_LINE_END                   \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        mul     x14, x3, x11 ASM_LINE_END                   \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        mul     x14, x3, x12 ASM_LINE_END                   \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        mul     x14, x3, x13 ASM_LINE_END                   \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        cset    x15, hs ASM_LINE_END                        \
        umulh   x14, x3, x5 ASM_LINE_END                    \
        adds    x19, x19, x14 ASM_LINE_END                  \
        umulh   x14, x3, x6 ASM_LINE_END                    \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        umulh   x14, x3, x7 ASM_LINE_END                    \
        adcs    x21, x21, x14 ASM_LINE_END                  \
        umulh   x14, x3, x8 ASM_LINE_END                    \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        umulh   x14, x3, x9 ASM_LINE_END                    \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        umulh   x14, x3, x10 ASM_LINE_END                   \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        umulh   x14, x3, x11 ASM_LINE_END                   \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        umulh   x14, x3, x12 ASM_LINE_END                   \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        umulh   x14, x3, x13 ASM_LINE_END                   \
        adc     x15, x15, x14 ASM_LINE_END                  \
        mul     x14, x4, x5 ASM_LINE_END                    \
        adds    x19, x19, x14 ASM_LINE_END                  \
        mul     x14, x4, x6 ASM_LINE_END                    \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        mul     x14, x4, x7 ASM_LINE_END                    \
        adcs    x21, x21, x14 ASM_LINE_END                  \
        mul     x14, x4, x8 ASM_LINE_END                    \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        mul     x14, x4, x9 ASM_LINE_END                    \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        mul     x14, x4, x10 ASM_LINE_END                   \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        mul     x14, x4, x11 ASM_LINE_END                   \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        mul     x14, x4, x12 ASM_LINE_END                   \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        mul     x14, x4, x13 ASM_LINE_END                   \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        cset    x16, hs ASM_LINE_END                        \
        umulh   x14, x4, x5 ASM_LINE_END                    \
        adds    x20, x20, x14 ASM_LINE_END                  \
        umulh   x14, x4, x6 ASM_LINE_END                    \
        adcs    x21, x21, x14 ASM_LINE_END                  \
        umulh   x14, x4, x7 ASM_LINE_END                    \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        umulh   x14, x4, x8 ASM_LINE_END                    \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        umulh   x14, x4, x9 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        umulh   x14, x4, x10 ASM_LINE_END                   \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        umulh   x14, x4, x11 ASM_LINE_END                   \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        umulh   x14, x4, x12 ASM_LINE_END                   \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        umulh   x14, x4, x13 ASM_LINE_END                   \
        adc     x16, x16, x14 ASM_LINE_END                  \
        stp     x17, x19, [P0+16] ASM_LINE_END              \
        ldp     x3, x4, [P1+32] ASM_LINE_END                \
        mul     x14, x3, x5 ASM_LINE_END                    \
        adds    x20, x20, x14 ASM_LINE_END                  \
        mul     x14, x3, x6 ASM_LINE_END                    \
        adcs    x21, x21, x14 ASM_LINE_END                  \
        mul     x14, x3, x7 ASM_LINE_END                    \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        mul     x14, x3, x8 ASM_LINE_END                    \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        mul     x14, x3, x9 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        mul     x14, x3, x10 ASM_LINE_END                   \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        mul     x14, x3, x11 ASM_LINE_END                   \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        mul     x14, x3, x12 ASM_LINE_END                   \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        mul     x14, x3, x13 ASM_LINE_END                   \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        cset    x17, hs ASM_LINE_END                        \
        umulh   x14, x3, x5 ASM_LINE_END                    \
        adds    x21, x21, x14 ASM_LINE_END                  \
        umulh   x14, x3, x6 ASM_LINE_END                    \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        umulh   x14, x3, x7 ASM_LINE_END                    \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        umulh   x14, x3, x8 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        umulh   x14, x3, x9 ASM_LINE_END                    \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        umulh   x14, x3, x10 ASM_LINE_END                   \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        umulh   x14, x3, x11 ASM_LINE_END                   \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        umulh   x14, x3, x12 ASM_LINE_END                   \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        umulh   x14, x3, x13 ASM_LINE_END                   \
        adc     x17, x17, x14 ASM_LINE_END                  \
        mul     x14, x4, x5 ASM_LINE_END                    \
        adds    x21, x21, x14 ASM_LINE_END                  \
        mul     x14, x4, x6 ASM_LINE_END                    \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        mul     x14, x4, x7 ASM_LINE_END                    \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        mul     x14, x4, x8 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        mul     x14, x4, x9 ASM_LINE_END                    \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        mul     x14, x4, x10 ASM_LINE_END                   \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        mul     x14, x4, x11 ASM_LINE_END                   \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        mul     x14, x4, x12 ASM_LINE_END                   \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        mul     x14, x4, x13 ASM_LINE_END                   \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        cset    x19, hs ASM_LINE_END                        \
        umulh   x14, x4, x5 ASM_LINE_END                    \
        adds    x22, x22, x14 ASM_LINE_END                  \
        umulh   x14, x4, x6 ASM_LINE_END                    \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        umulh   x14, x4, x7 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        umulh   x14, x4, x8 ASM_LINE_END                    \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        umulh   x14, x4, x9 ASM_LINE_END                    \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        umulh   x14, x4, x10 ASM_LINE_END                   \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        umulh   x14, x4, x11 ASM_LINE_END                   \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        umulh   x14, x4, x12 ASM_LINE_END                   \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        umulh   x14, x4, x13 ASM_LINE_END                   \
        adc     x19, x19, x14 ASM_LINE_END                  \
        stp     x20, x21, [P0+32] ASM_LINE_END              \
        ldp     x3, x4, [P1+48] ASM_LINE_END                \
        mul     x14, x3, x5 ASM_LINE_END                    \
        adds    x22, x22, x14 ASM_LINE_END                  \
        mul     x14, x3, x6 ASM_LINE_END                    \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        mul     x14, x3, x7 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        mul     x14, x3, x8 ASM_LINE_END                    \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        mul     x14, x3, x9 ASM_LINE_END                    \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        mul     x14, x3, x10 ASM_LINE_END                   \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        mul     x14, x3, x11 ASM_LINE_END                   \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        mul     x14, x3, x12 ASM_LINE_END                   \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        mul     x14, x3, x13 ASM_LINE_END                   \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        cset    x20, hs ASM_LINE_END                        \
        umulh   x14, x3, x5 ASM_LINE_END                    \
        adds    x23, x23, x14 ASM_LINE_END                  \
        umulh   x14, x3, x6 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        umulh   x14, x3, x7 ASM_LINE_END                    \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        umulh   x14, x3, x8 ASM_LINE_END                    \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        umulh   x14, x3, x9 ASM_LINE_END                    \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        umulh   x14, x3, x10 ASM_LINE_END                   \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        umulh   x14, x3, x11 ASM_LINE_END                   \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        umulh   x14, x3, x12 ASM_LINE_END                   \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        umulh   x14, x3, x13 ASM_LINE_END                   \
        adc     x20, x20, x14 ASM_LINE_END                  \
        mul     x14, x4, x5 ASM_LINE_END                    \
        adds    x23, x23, x14 ASM_LINE_END                  \
        mul     x14, x4, x6 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        mul     x14, x4, x7 ASM_LINE_END                    \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        mul     x14, x4, x8 ASM_LINE_END                    \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        mul     x14, x4, x9 ASM_LINE_END                    \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        mul     x14, x4, x10 ASM_LINE_END                   \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        mul     x14, x4, x11 ASM_LINE_END                   \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        mul     x14, x4, x12 ASM_LINE_END                   \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        mul     x14, x4, x13 ASM_LINE_END                   \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        cset    x21, hs ASM_LINE_END                        \
        umulh   x14, x4, x5 ASM_LINE_END                    \
        adds    x24, x24, x14 ASM_LINE_END                  \
        umulh   x14, x4, x6 ASM_LINE_END                    \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        umulh   x14, x4, x7 ASM_LINE_END                    \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        umulh   x14, x4, x8 ASM_LINE_END                    \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        umulh   x14, x4, x9 ASM_LINE_END                    \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        umulh   x14, x4, x10 ASM_LINE_END                   \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        umulh   x14, x4, x11 ASM_LINE_END                   \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        umulh   x14, x4, x12 ASM_LINE_END                   \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        umulh   x14, x4, x13 ASM_LINE_END                   \
        adc     x21, x21, x14 ASM_LINE_END                  \
        stp     x22, x23, [P0+48] ASM_LINE_END              \
        ldr     x3, [P1+64] ASM_LINE_END                    \
        mul     x14, x3, x5 ASM_LINE_END                    \
        adds    x24, x24, x14 ASM_LINE_END                  \
        mul     x14, x3, x6 ASM_LINE_END                    \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        mul     x14, x3, x7 ASM_LINE_END                    \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        mul     x14, x3, x8 ASM_LINE_END                    \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        mul     x14, x3, x9 ASM_LINE_END                    \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        mul     x14, x3, x10 ASM_LINE_END                   \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        mul     x14, x3, x11 ASM_LINE_END                   \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        mul     x14, x3, x12 ASM_LINE_END                   \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        mul     x14, x3, x13 ASM_LINE_END                   \
        adc     x21, x21, x14 ASM_LINE_END                  \
        umulh   x14, x3, x5 ASM_LINE_END                    \
        adds    x1, x1, x14 ASM_LINE_END                    \
        umulh   x14, x3, x6 ASM_LINE_END                    \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        umulh   x14, x3, x7 ASM_LINE_END                    \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        umulh   x14, x3, x8 ASM_LINE_END                    \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        umulh   x14, x3, x9 ASM_LINE_END                    \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        umulh   x14, x3, x10 ASM_LINE_END                   \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        umulh   x14, x3, x11 ASM_LINE_END                   \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        umulh   x14, x3, x12 ASM_LINE_END                   \
        adc     x21, x21, x14 ASM_LINE_END                  \
        cmp     xzr, xzr ASM_LINE_END                       \
        ldp     x5, x6, [P0] ASM_LINE_END                   \
        extr    x14, x1, x24, #9 ASM_LINE_END               \
        adcs    x5, x5, x14 ASM_LINE_END                    \
        extr    x14, x0, x1, #9 ASM_LINE_END                \
        adcs    x6, x6, x14 ASM_LINE_END                    \
        ldp     x7, x8, [P0+16] ASM_LINE_END                \
        extr    x14, x15, x0, #9 ASM_LINE_END               \
        adcs    x7, x7, x14 ASM_LINE_END                    \
        extr    x14, x16, x15, #9 ASM_LINE_END              \
        adcs    x8, x8, x14 ASM_LINE_END                    \
        ldp     x9, x10, [P0+32] ASM_LINE_END               \
        extr    x14, x17, x16, #9 ASM_LINE_END              \
        adcs    x9, x9, x14 ASM_LINE_END                    \
        extr    x14, x19, x17, #9 ASM_LINE_END              \
        adcs    x10, x10, x14 ASM_LINE_END                  \
        ldp     x11, x12, [P0+48] ASM_LINE_END              \
        extr    x14, x20, x19, #9 ASM_LINE_END              \
        adcs    x11, x11, x14 ASM_LINE_END                  \
        extr    x14, x21, x20, #9 ASM_LINE_END              \
        adcs    x12, x12, x14 ASM_LINE_END                  \
        orr     x13, x24, #0xfffffffffffffe00 ASM_LINE_END  \
        lsr     x14, x21, #9 ASM_LINE_END                   \
        adcs    x13, x13, x14 ASM_LINE_END                  \
        sbcs    x5, x5, xzr ASM_LINE_END                    \
        sbcs    x6, x6, xzr ASM_LINE_END                    \
        sbcs    x7, x7, xzr ASM_LINE_END                    \
        sbcs    x8, x8, xzr ASM_LINE_END                    \
        sbcs    x9, x9, xzr ASM_LINE_END                    \
        sbcs    x10, x10, xzr ASM_LINE_END                  \
        sbcs    x11, x11, xzr ASM_LINE_END                  \
        sbcs    x12, x12, xzr ASM_LINE_END                  \
        sbc     x13, x13, xzr ASM_LINE_END                  \
        and     x13, x13, #0x1ff ASM_LINE_END               \
        stp     x5, x6, [P0] ASM_LINE_END                   \
        stp     x7, x8, [P0+16] ASM_LINE_END                \
        stp     x9, x10, [P0+32] ASM_LINE_END               \
        stp     x11, x12, [P0+48] ASM_LINE_END              \
        str     x13, [P0+64]

// Corresponds exactly to bignum_sqr_p521_alt

#define sqr_p521(P0,P1)                         \
        ldp     x2, x3, [P1] ASM_LINE_END                   \
        mul     x11, x2, x3 ASM_LINE_END                    \
        umulh   x12, x2, x3 ASM_LINE_END                    \
        ldp     x4, x5, [P1+16] ASM_LINE_END                \
        mul     x10, x2, x4 ASM_LINE_END                    \
        umulh   x13, x2, x4 ASM_LINE_END                    \
        adds    x12, x12, x10 ASM_LINE_END                  \
        ldp     x6, x7, [P1+32] ASM_LINE_END                \
        mul     x10, x2, x5 ASM_LINE_END                    \
        umulh   x14, x2, x5 ASM_LINE_END                    \
        adcs    x13, x13, x10 ASM_LINE_END                  \
        ldp     x8, x9, [P1+48] ASM_LINE_END                \
        mul     x10, x2, x6 ASM_LINE_END                    \
        umulh   x15, x2, x6 ASM_LINE_END                    \
        adcs    x14, x14, x10 ASM_LINE_END                  \
        mul     x10, x2, x7 ASM_LINE_END                    \
        umulh   x16, x2, x7 ASM_LINE_END                    \
        adcs    x15, x15, x10 ASM_LINE_END                  \
        mul     x10, x2, x8 ASM_LINE_END                    \
        umulh   x17, x2, x8 ASM_LINE_END                    \
        adcs    x16, x16, x10 ASM_LINE_END                  \
        mul     x10, x2, x9 ASM_LINE_END                    \
        umulh   x19, x2, x9 ASM_LINE_END                    \
        adcs    x17, x17, x10 ASM_LINE_END                  \
        adc     x19, x19, xzr ASM_LINE_END                  \
        mul     x10, x3, x4 ASM_LINE_END                    \
        adds    x13, x13, x10 ASM_LINE_END                  \
        mul     x10, x3, x5 ASM_LINE_END                    \
        adcs    x14, x14, x10 ASM_LINE_END                  \
        mul     x10, x3, x6 ASM_LINE_END                    \
        adcs    x15, x15, x10 ASM_LINE_END                  \
        mul     x10, x3, x7 ASM_LINE_END                    \
        adcs    x16, x16, x10 ASM_LINE_END                  \
        mul     x10, x3, x8 ASM_LINE_END                    \
        adcs    x17, x17, x10 ASM_LINE_END                  \
        mul     x10, x3, x9 ASM_LINE_END                    \
        adcs    x19, x19, x10 ASM_LINE_END                  \
        cset    x20, hs ASM_LINE_END                        \
        umulh   x10, x3, x4 ASM_LINE_END                    \
        adds    x14, x14, x10 ASM_LINE_END                  \
        umulh   x10, x3, x5 ASM_LINE_END                    \
        adcs    x15, x15, x10 ASM_LINE_END                  \
        umulh   x10, x3, x6 ASM_LINE_END                    \
        adcs    x16, x16, x10 ASM_LINE_END                  \
        umulh   x10, x3, x7 ASM_LINE_END                    \
        adcs    x17, x17, x10 ASM_LINE_END                  \
        umulh   x10, x3, x8 ASM_LINE_END                    \
        adcs    x19, x19, x10 ASM_LINE_END                  \
        umulh   x10, x3, x9 ASM_LINE_END                    \
        adc     x20, x20, x10 ASM_LINE_END                  \
        mul     x10, x6, x7 ASM_LINE_END                    \
        umulh   x21, x6, x7 ASM_LINE_END                    \
        adds    x20, x20, x10 ASM_LINE_END                  \
        adc     x21, x21, xzr ASM_LINE_END                  \
        mul     x10, x4, x5 ASM_LINE_END                    \
        adds    x15, x15, x10 ASM_LINE_END                  \
        mul     x10, x4, x6 ASM_LINE_END                    \
        adcs    x16, x16, x10 ASM_LINE_END                  \
        mul     x10, x4, x7 ASM_LINE_END                    \
        adcs    x17, x17, x10 ASM_LINE_END                  \
        mul     x10, x4, x8 ASM_LINE_END                    \
        adcs    x19, x19, x10 ASM_LINE_END                  \
        mul     x10, x4, x9 ASM_LINE_END                    \
        adcs    x20, x20, x10 ASM_LINE_END                  \
        mul     x10, x6, x8 ASM_LINE_END                    \
        adcs    x21, x21, x10 ASM_LINE_END                  \
        cset    x22, hs ASM_LINE_END                        \
        umulh   x10, x4, x5 ASM_LINE_END                    \
        adds    x16, x16, x10 ASM_LINE_END                  \
        umulh   x10, x4, x6 ASM_LINE_END                    \
        adcs    x17, x17, x10 ASM_LINE_END                  \
        umulh   x10, x4, x7 ASM_LINE_END                    \
        adcs    x19, x19, x10 ASM_LINE_END                  \
        umulh   x10, x4, x8 ASM_LINE_END                    \
        adcs    x20, x20, x10 ASM_LINE_END                  \
        umulh   x10, x4, x9 ASM_LINE_END                    \
        adcs    x21, x21, x10 ASM_LINE_END                  \
        umulh   x10, x6, x8 ASM_LINE_END                    \
        adc     x22, x22, x10 ASM_LINE_END                  \
        mul     x10, x7, x8 ASM_LINE_END                    \
        umulh   x23, x7, x8 ASM_LINE_END                    \
        adds    x22, x22, x10 ASM_LINE_END                  \
        adc     x23, x23, xzr ASM_LINE_END                  \
        mul     x10, x5, x6 ASM_LINE_END                    \
        adds    x17, x17, x10 ASM_LINE_END                  \
        mul     x10, x5, x7 ASM_LINE_END                    \
        adcs    x19, x19, x10 ASM_LINE_END                  \
        mul     x10, x5, x8 ASM_LINE_END                    \
        adcs    x20, x20, x10 ASM_LINE_END                  \
        mul     x10, x5, x9 ASM_LINE_END                    \
        adcs    x21, x21, x10 ASM_LINE_END                  \
        mul     x10, x6, x9 ASM_LINE_END                    \
        adcs    x22, x22, x10 ASM_LINE_END                  \
        mul     x10, x7, x9 ASM_LINE_END                    \
        adcs    x23, x23, x10 ASM_LINE_END                  \
        cset    x24, hs ASM_LINE_END                        \
        umulh   x10, x5, x6 ASM_LINE_END                    \
        adds    x19, x19, x10 ASM_LINE_END                  \
        umulh   x10, x5, x7 ASM_LINE_END                    \
        adcs    x20, x20, x10 ASM_LINE_END                  \
        umulh   x10, x5, x8 ASM_LINE_END                    \
        adcs    x21, x21, x10 ASM_LINE_END                  \
        umulh   x10, x5, x9 ASM_LINE_END                    \
        adcs    x22, x22, x10 ASM_LINE_END                  \
        umulh   x10, x6, x9 ASM_LINE_END                    \
        adcs    x23, x23, x10 ASM_LINE_END                  \
        umulh   x10, x7, x9 ASM_LINE_END                    \
        adc     x24, x24, x10 ASM_LINE_END                  \
        mul     x10, x8, x9 ASM_LINE_END                    \
        umulh   x25, x8, x9 ASM_LINE_END                    \
        adds    x24, x24, x10 ASM_LINE_END                  \
        adc     x25, x25, xzr ASM_LINE_END                  \
        adds    x11, x11, x11 ASM_LINE_END                  \
        adcs    x12, x12, x12 ASM_LINE_END                  \
        adcs    x13, x13, x13 ASM_LINE_END                  \
        adcs    x14, x14, x14 ASM_LINE_END                  \
        adcs    x15, x15, x15 ASM_LINE_END                  \
        adcs    x16, x16, x16 ASM_LINE_END                  \
        adcs    x17, x17, x17 ASM_LINE_END                  \
        adcs    x19, x19, x19 ASM_LINE_END                  \
        adcs    x20, x20, x20 ASM_LINE_END                  \
        adcs    x21, x21, x21 ASM_LINE_END                  \
        adcs    x22, x22, x22 ASM_LINE_END                  \
        adcs    x23, x23, x23 ASM_LINE_END                  \
        adcs    x24, x24, x24 ASM_LINE_END                  \
        adcs    x25, x25, x25 ASM_LINE_END                  \
        cset    x0, hs ASM_LINE_END                         \
        umulh   x10, x2, x2 ASM_LINE_END                    \
        adds    x11, x11, x10 ASM_LINE_END                  \
        mul     x10, x3, x3 ASM_LINE_END                    \
        adcs    x12, x12, x10 ASM_LINE_END                  \
        umulh   x10, x3, x3 ASM_LINE_END                    \
        adcs    x13, x13, x10 ASM_LINE_END                  \
        mul     x10, x4, x4 ASM_LINE_END                    \
        adcs    x14, x14, x10 ASM_LINE_END                  \
        umulh   x10, x4, x4 ASM_LINE_END                    \
        adcs    x15, x15, x10 ASM_LINE_END                  \
        mul     x10, x5, x5 ASM_LINE_END                    \
        adcs    x16, x16, x10 ASM_LINE_END                  \
        umulh   x10, x5, x5 ASM_LINE_END                    \
        adcs    x17, x17, x10 ASM_LINE_END                  \
        mul     x10, x6, x6 ASM_LINE_END                    \
        adcs    x19, x19, x10 ASM_LINE_END                  \
        umulh   x10, x6, x6 ASM_LINE_END                    \
        adcs    x20, x20, x10 ASM_LINE_END                  \
        mul     x10, x7, x7 ASM_LINE_END                    \
        adcs    x21, x21, x10 ASM_LINE_END                  \
        umulh   x10, x7, x7 ASM_LINE_END                    \
        adcs    x22, x22, x10 ASM_LINE_END                  \
        mul     x10, x8, x8 ASM_LINE_END                    \
        adcs    x23, x23, x10 ASM_LINE_END                  \
        umulh   x10, x8, x8 ASM_LINE_END                    \
        adcs    x24, x24, x10 ASM_LINE_END                  \
        mul     x10, x9, x9 ASM_LINE_END                    \
        adcs    x25, x25, x10 ASM_LINE_END                  \
        umulh   x10, x9, x9 ASM_LINE_END                    \
        adc     x0, x0, x10 ASM_LINE_END                    \
        ldr     x1, [P1+64] ASM_LINE_END                    \
        add     x1, x1, x1 ASM_LINE_END                     \
        mul     x10, x1, x2 ASM_LINE_END                    \
        adds    x19, x19, x10 ASM_LINE_END                  \
        umulh   x10, x1, x2 ASM_LINE_END                    \
        adcs    x20, x20, x10 ASM_LINE_END                  \
        mul     x10, x1, x4 ASM_LINE_END                    \
        adcs    x21, x21, x10 ASM_LINE_END                  \
        umulh   x10, x1, x4 ASM_LINE_END                    \
        adcs    x22, x22, x10 ASM_LINE_END                  \
        mul     x10, x1, x6 ASM_LINE_END                    \
        adcs    x23, x23, x10 ASM_LINE_END                  \
        umulh   x10, x1, x6 ASM_LINE_END                    \
        adcs    x24, x24, x10 ASM_LINE_END                  \
        mul     x10, x1, x8 ASM_LINE_END                    \
        adcs    x25, x25, x10 ASM_LINE_END                  \
        umulh   x10, x1, x8 ASM_LINE_END                    \
        adcs    x0, x0, x10 ASM_LINE_END                    \
        lsr     x4, x1, #1 ASM_LINE_END                     \
        mul     x4, x4, x4 ASM_LINE_END                     \
        adc     x4, x4, xzr ASM_LINE_END                    \
        mul     x10, x1, x3 ASM_LINE_END                    \
        adds    x20, x20, x10 ASM_LINE_END                  \
        umulh   x10, x1, x3 ASM_LINE_END                    \
        adcs    x21, x21, x10 ASM_LINE_END                  \
        mul     x10, x1, x5 ASM_LINE_END                    \
        adcs    x22, x22, x10 ASM_LINE_END                  \
        umulh   x10, x1, x5 ASM_LINE_END                    \
        adcs    x23, x23, x10 ASM_LINE_END                  \
        mul     x10, x1, x7 ASM_LINE_END                    \
        adcs    x24, x24, x10 ASM_LINE_END                  \
        umulh   x10, x1, x7 ASM_LINE_END                    \
        adcs    x25, x25, x10 ASM_LINE_END                  \
        mul     x10, x1, x9 ASM_LINE_END                    \
        adcs    x0, x0, x10 ASM_LINE_END                    \
        umulh   x10, x1, x9 ASM_LINE_END                    \
        adc     x4, x4, x10 ASM_LINE_END                    \
        mul     x2, x2, x2 ASM_LINE_END                     \
        cmp     xzr, xzr ASM_LINE_END                       \
        extr    x10, x20, x19, #9 ASM_LINE_END              \
        adcs    x2, x2, x10 ASM_LINE_END                    \
        extr    x10, x21, x20, #9 ASM_LINE_END              \
        adcs    x11, x11, x10 ASM_LINE_END                  \
        extr    x10, x22, x21, #9 ASM_LINE_END              \
        adcs    x12, x12, x10 ASM_LINE_END                  \
        extr    x10, x23, x22, #9 ASM_LINE_END              \
        adcs    x13, x13, x10 ASM_LINE_END                  \
        extr    x10, x24, x23, #9 ASM_LINE_END              \
        adcs    x14, x14, x10 ASM_LINE_END                  \
        extr    x10, x25, x24, #9 ASM_LINE_END              \
        adcs    x15, x15, x10 ASM_LINE_END                  \
        extr    x10, x0, x25, #9 ASM_LINE_END               \
        adcs    x16, x16, x10 ASM_LINE_END                  \
        extr    x10, x4, x0, #9 ASM_LINE_END                \
        adcs    x17, x17, x10 ASM_LINE_END                  \
        orr     x19, x19, #0xfffffffffffffe00 ASM_LINE_END  \
        lsr     x10, x4, #9 ASM_LINE_END                    \
        adcs    x19, x19, x10 ASM_LINE_END                  \
        sbcs    x2, x2, xzr ASM_LINE_END                    \
        sbcs    x11, x11, xzr ASM_LINE_END                  \
        sbcs    x12, x12, xzr ASM_LINE_END                  \
        sbcs    x13, x13, xzr ASM_LINE_END                  \
        sbcs    x14, x14, xzr ASM_LINE_END                  \
        sbcs    x15, x15, xzr ASM_LINE_END                  \
        sbcs    x16, x16, xzr ASM_LINE_END                  \
        sbcs    x17, x17, xzr ASM_LINE_END                  \
        sbc     x19, x19, xzr ASM_LINE_END                  \
        and     x19, x19, #0x1ff ASM_LINE_END               \
        stp     x2, x11, [P0] ASM_LINE_END                  \
        stp     x12, x13, [P0+16] ASM_LINE_END              \
        stp     x14, x15, [P0+32] ASM_LINE_END              \
        stp     x16, x17, [P0+48] ASM_LINE_END              \
        str     x19, [P0+64]

// Corresponds exactly to bignum_add_p521

#define add_p521(P0,P1,P2)                      \
        cmp     xzr, xzr ASM_LINE_END                       \
        ldp     x5, x6, [P1] ASM_LINE_END                   \
        ldp     x4, x3, [P2] ASM_LINE_END                   \
        adcs    x5, x5, x4 ASM_LINE_END                     \
        adcs    x6, x6, x3 ASM_LINE_END                     \
        ldp     x7, x8, [P1+16] ASM_LINE_END                \
        ldp     x4, x3, [P2+16] ASM_LINE_END                \
        adcs    x7, x7, x4 ASM_LINE_END                     \
        adcs    x8, x8, x3 ASM_LINE_END                     \
        ldp     x9, x10, [P1+32] ASM_LINE_END               \
        ldp     x4, x3, [P2+32] ASM_LINE_END                \
        adcs    x9, x9, x4 ASM_LINE_END                     \
        adcs    x10, x10, x3 ASM_LINE_END                   \
        ldp     x11, x12, [P1+48] ASM_LINE_END              \
        ldp     x4, x3, [P2+48] ASM_LINE_END                \
        adcs    x11, x11, x4 ASM_LINE_END                   \
        adcs    x12, x12, x3 ASM_LINE_END                   \
        ldr     x13, [P1+64] ASM_LINE_END                   \
        ldr     x4, [P2+64] ASM_LINE_END                    \
        adc     x13, x13, x4 ASM_LINE_END                   \
        subs    x4, x13, #512 ASM_LINE_END                  \
        csetm   x4, hs ASM_LINE_END                         \
        sbcs    x5, x5, xzr ASM_LINE_END                    \
        and     x4, x4, #0x200 ASM_LINE_END                 \
        sbcs    x6, x6, xzr ASM_LINE_END                    \
        sbcs    x7, x7, xzr ASM_LINE_END                    \
        sbcs    x8, x8, xzr ASM_LINE_END                    \
        sbcs    x9, x9, xzr ASM_LINE_END                    \
        sbcs    x10, x10, xzr ASM_LINE_END                  \
        sbcs    x11, x11, xzr ASM_LINE_END                  \
        sbcs    x12, x12, xzr ASM_LINE_END                  \
        sbc     x13, x13, x4 ASM_LINE_END                   \
        stp     x5, x6, [P0] ASM_LINE_END                   \
        stp     x7, x8, [P0+16] ASM_LINE_END                \
        stp     x9, x10, [P0+32] ASM_LINE_END               \
        stp     x11, x12, [P0+48] ASM_LINE_END              \
        str     x13, [P0+64]

// Corresponds exactly to bignum_sub_p521

#define sub_p521(P0,P1,P2)                      \
        ldp     x5, x6, [P1] ASM_LINE_END                   \
        ldp     x4, x3, [P2] ASM_LINE_END                   \
        subs    x5, x5, x4 ASM_LINE_END                     \
        sbcs    x6, x6, x3 ASM_LINE_END                     \
        ldp     x7, x8, [P1+16] ASM_LINE_END                \
        ldp     x4, x3, [P2+16] ASM_LINE_END                \
        sbcs    x7, x7, x4 ASM_LINE_END                     \
        sbcs    x8, x8, x3 ASM_LINE_END                     \
        ldp     x9, x10, [P1+32] ASM_LINE_END               \
        ldp     x4, x3, [P2+32] ASM_LINE_END                \
        sbcs    x9, x9, x4 ASM_LINE_END                     \
        sbcs    x10, x10, x3 ASM_LINE_END                   \
        ldp     x11, x12, [P1+48] ASM_LINE_END              \
        ldp     x4, x3, [P2+48] ASM_LINE_END                \
        sbcs    x11, x11, x4 ASM_LINE_END                   \
        sbcs    x12, x12, x3 ASM_LINE_END                   \
        ldr     x13, [P1+64] ASM_LINE_END                   \
        ldr     x4, [P2+64] ASM_LINE_END                    \
        sbcs    x13, x13, x4 ASM_LINE_END                   \
        sbcs    x5, x5, xzr ASM_LINE_END                    \
        sbcs    x6, x6, xzr ASM_LINE_END                    \
        sbcs    x7, x7, xzr ASM_LINE_END                    \
        sbcs    x8, x8, xzr ASM_LINE_END                    \
        sbcs    x9, x9, xzr ASM_LINE_END                    \
        sbcs    x10, x10, xzr ASM_LINE_END                  \
        sbcs    x11, x11, xzr ASM_LINE_END                  \
        sbcs    x12, x12, xzr ASM_LINE_END                  \
        sbcs    x13, x13, xzr ASM_LINE_END                  \
        and     x13, x13, #0x1ff ASM_LINE_END               \
        stp     x5, x6, [P0] ASM_LINE_END                   \
        stp     x7, x8, [P0+16] ASM_LINE_END                \
        stp     x9, x10, [P0+32] ASM_LINE_END               \
        stp     x11, x12, [P0+48] ASM_LINE_END              \
        str     x13, [P0+64]

// Weak multiplication not fully reducing

#define weakmul_p521(P0,P1,P2)                  \
        ldp     x3, x4, [P1] ASM_LINE_END                   \
        ldp     x5, x6, [P2] ASM_LINE_END                   \
        mul     x15, x3, x5 ASM_LINE_END                    \
        umulh   x16, x3, x5 ASM_LINE_END                    \
        mul     x14, x3, x6 ASM_LINE_END                    \
        umulh   x17, x3, x6 ASM_LINE_END                    \
        adds    x16, x16, x14 ASM_LINE_END                  \
        ldp     x7, x8, [P2+16] ASM_LINE_END                \
        mul     x14, x3, x7 ASM_LINE_END                    \
        umulh   x19, x3, x7 ASM_LINE_END                    \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        mul     x14, x3, x8 ASM_LINE_END                    \
        umulh   x20, x3, x8 ASM_LINE_END                    \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        ldp     x9, x10, [P2+32] ASM_LINE_END               \
        mul     x14, x3, x9 ASM_LINE_END                    \
        umulh   x21, x3, x9 ASM_LINE_END                    \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        mul     x14, x3, x10 ASM_LINE_END                   \
        umulh   x22, x3, x10 ASM_LINE_END                   \
        adcs    x21, x21, x14 ASM_LINE_END                  \
        ldp     x11, x12, [P2+48] ASM_LINE_END              \
        mul     x14, x3, x11 ASM_LINE_END                   \
        umulh   x23, x3, x11 ASM_LINE_END                   \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        ldr     x13, [P2+64] ASM_LINE_END                   \
        mul     x14, x3, x12 ASM_LINE_END                   \
        umulh   x24, x3, x12 ASM_LINE_END                   \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        mul     x14, x3, x13 ASM_LINE_END                   \
        umulh   x1, x3, x13 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        adc     x1, x1, xzr ASM_LINE_END                    \
        mul     x14, x4, x5 ASM_LINE_END                    \
        adds    x16, x16, x14 ASM_LINE_END                  \
        mul     x14, x4, x6 ASM_LINE_END                    \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        mul     x14, x4, x7 ASM_LINE_END                    \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        mul     x14, x4, x8 ASM_LINE_END                    \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        mul     x14, x4, x9 ASM_LINE_END                    \
        adcs    x21, x21, x14 ASM_LINE_END                  \
        mul     x14, x4, x10 ASM_LINE_END                   \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        mul     x14, x4, x11 ASM_LINE_END                   \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        mul     x14, x4, x12 ASM_LINE_END                   \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        mul     x14, x4, x13 ASM_LINE_END                   \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        cset    x0, hs ASM_LINE_END                         \
        umulh   x14, x4, x5 ASM_LINE_END                    \
        adds    x17, x17, x14 ASM_LINE_END                  \
        umulh   x14, x4, x6 ASM_LINE_END                    \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        umulh   x14, x4, x7 ASM_LINE_END                    \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        umulh   x14, x4, x8 ASM_LINE_END                    \
        adcs    x21, x21, x14 ASM_LINE_END                  \
        umulh   x14, x4, x9 ASM_LINE_END                    \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        umulh   x14, x4, x10 ASM_LINE_END                   \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        umulh   x14, x4, x11 ASM_LINE_END                   \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        umulh   x14, x4, x12 ASM_LINE_END                   \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        umulh   x14, x4, x13 ASM_LINE_END                   \
        adc     x0, x0, x14 ASM_LINE_END                    \
        stp     x15, x16, [P0] ASM_LINE_END                 \
        ldp     x3, x4, [P1+16] ASM_LINE_END                \
        mul     x14, x3, x5 ASM_LINE_END                    \
        adds    x17, x17, x14 ASM_LINE_END                  \
        mul     x14, x3, x6 ASM_LINE_END                    \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        mul     x14, x3, x7 ASM_LINE_END                    \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        mul     x14, x3, x8 ASM_LINE_END                    \
        adcs    x21, x21, x14 ASM_LINE_END                  \
        mul     x14, x3, x9 ASM_LINE_END                    \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        mul     x14, x3, x10 ASM_LINE_END                   \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        mul     x14, x3, x11 ASM_LINE_END                   \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        mul     x14, x3, x12 ASM_LINE_END                   \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        mul     x14, x3, x13 ASM_LINE_END                   \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        cset    x15, hs ASM_LINE_END                        \
        umulh   x14, x3, x5 ASM_LINE_END                    \
        adds    x19, x19, x14 ASM_LINE_END                  \
        umulh   x14, x3, x6 ASM_LINE_END                    \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        umulh   x14, x3, x7 ASM_LINE_END                    \
        adcs    x21, x21, x14 ASM_LINE_END                  \
        umulh   x14, x3, x8 ASM_LINE_END                    \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        umulh   x14, x3, x9 ASM_LINE_END                    \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        umulh   x14, x3, x10 ASM_LINE_END                   \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        umulh   x14, x3, x11 ASM_LINE_END                   \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        umulh   x14, x3, x12 ASM_LINE_END                   \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        umulh   x14, x3, x13 ASM_LINE_END                   \
        adc     x15, x15, x14 ASM_LINE_END                  \
        mul     x14, x4, x5 ASM_LINE_END                    \
        adds    x19, x19, x14 ASM_LINE_END                  \
        mul     x14, x4, x6 ASM_LINE_END                    \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        mul     x14, x4, x7 ASM_LINE_END                    \
        adcs    x21, x21, x14 ASM_LINE_END                  \
        mul     x14, x4, x8 ASM_LINE_END                    \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        mul     x14, x4, x9 ASM_LINE_END                    \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        mul     x14, x4, x10 ASM_LINE_END                   \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        mul     x14, x4, x11 ASM_LINE_END                   \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        mul     x14, x4, x12 ASM_LINE_END                   \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        mul     x14, x4, x13 ASM_LINE_END                   \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        cset    x16, hs ASM_LINE_END                        \
        umulh   x14, x4, x5 ASM_LINE_END                    \
        adds    x20, x20, x14 ASM_LINE_END                  \
        umulh   x14, x4, x6 ASM_LINE_END                    \
        adcs    x21, x21, x14 ASM_LINE_END                  \
        umulh   x14, x4, x7 ASM_LINE_END                    \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        umulh   x14, x4, x8 ASM_LINE_END                    \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        umulh   x14, x4, x9 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        umulh   x14, x4, x10 ASM_LINE_END                   \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        umulh   x14, x4, x11 ASM_LINE_END                   \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        umulh   x14, x4, x12 ASM_LINE_END                   \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        umulh   x14, x4, x13 ASM_LINE_END                   \
        adc     x16, x16, x14 ASM_LINE_END                  \
        stp     x17, x19, [P0+16] ASM_LINE_END              \
        ldp     x3, x4, [P1+32] ASM_LINE_END                \
        mul     x14, x3, x5 ASM_LINE_END                    \
        adds    x20, x20, x14 ASM_LINE_END                  \
        mul     x14, x3, x6 ASM_LINE_END                    \
        adcs    x21, x21, x14 ASM_LINE_END                  \
        mul     x14, x3, x7 ASM_LINE_END                    \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        mul     x14, x3, x8 ASM_LINE_END                    \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        mul     x14, x3, x9 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        mul     x14, x3, x10 ASM_LINE_END                   \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        mul     x14, x3, x11 ASM_LINE_END                   \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        mul     x14, x3, x12 ASM_LINE_END                   \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        mul     x14, x3, x13 ASM_LINE_END                   \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        cset    x17, hs ASM_LINE_END                        \
        umulh   x14, x3, x5 ASM_LINE_END                    \
        adds    x21, x21, x14 ASM_LINE_END                  \
        umulh   x14, x3, x6 ASM_LINE_END                    \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        umulh   x14, x3, x7 ASM_LINE_END                    \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        umulh   x14, x3, x8 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        umulh   x14, x3, x9 ASM_LINE_END                    \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        umulh   x14, x3, x10 ASM_LINE_END                   \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        umulh   x14, x3, x11 ASM_LINE_END                   \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        umulh   x14, x3, x12 ASM_LINE_END                   \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        umulh   x14, x3, x13 ASM_LINE_END                   \
        adc     x17, x17, x14 ASM_LINE_END                  \
        mul     x14, x4, x5 ASM_LINE_END                    \
        adds    x21, x21, x14 ASM_LINE_END                  \
        mul     x14, x4, x6 ASM_LINE_END                    \
        adcs    x22, x22, x14 ASM_LINE_END                  \
        mul     x14, x4, x7 ASM_LINE_END                    \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        mul     x14, x4, x8 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        mul     x14, x4, x9 ASM_LINE_END                    \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        mul     x14, x4, x10 ASM_LINE_END                   \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        mul     x14, x4, x11 ASM_LINE_END                   \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        mul     x14, x4, x12 ASM_LINE_END                   \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        mul     x14, x4, x13 ASM_LINE_END                   \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        cset    x19, hs ASM_LINE_END                        \
        umulh   x14, x4, x5 ASM_LINE_END                    \
        adds    x22, x22, x14 ASM_LINE_END                  \
        umulh   x14, x4, x6 ASM_LINE_END                    \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        umulh   x14, x4, x7 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        umulh   x14, x4, x8 ASM_LINE_END                    \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        umulh   x14, x4, x9 ASM_LINE_END                    \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        umulh   x14, x4, x10 ASM_LINE_END                   \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        umulh   x14, x4, x11 ASM_LINE_END                   \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        umulh   x14, x4, x12 ASM_LINE_END                   \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        umulh   x14, x4, x13 ASM_LINE_END                   \
        adc     x19, x19, x14 ASM_LINE_END                  \
        stp     x20, x21, [P0+32] ASM_LINE_END              \
        ldp     x3, x4, [P1+48] ASM_LINE_END                \
        mul     x14, x3, x5 ASM_LINE_END                    \
        adds    x22, x22, x14 ASM_LINE_END                  \
        mul     x14, x3, x6 ASM_LINE_END                    \
        adcs    x23, x23, x14 ASM_LINE_END                  \
        mul     x14, x3, x7 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        mul     x14, x3, x8 ASM_LINE_END                    \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        mul     x14, x3, x9 ASM_LINE_END                    \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        mul     x14, x3, x10 ASM_LINE_END                   \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        mul     x14, x3, x11 ASM_LINE_END                   \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        mul     x14, x3, x12 ASM_LINE_END                   \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        mul     x14, x3, x13 ASM_LINE_END                   \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        cset    x20, hs ASM_LINE_END                        \
        umulh   x14, x3, x5 ASM_LINE_END                    \
        adds    x23, x23, x14 ASM_LINE_END                  \
        umulh   x14, x3, x6 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        umulh   x14, x3, x7 ASM_LINE_END                    \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        umulh   x14, x3, x8 ASM_LINE_END                    \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        umulh   x14, x3, x9 ASM_LINE_END                    \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        umulh   x14, x3, x10 ASM_LINE_END                   \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        umulh   x14, x3, x11 ASM_LINE_END                   \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        umulh   x14, x3, x12 ASM_LINE_END                   \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        umulh   x14, x3, x13 ASM_LINE_END                   \
        adc     x20, x20, x14 ASM_LINE_END                  \
        mul     x14, x4, x5 ASM_LINE_END                    \
        adds    x23, x23, x14 ASM_LINE_END                  \
        mul     x14, x4, x6 ASM_LINE_END                    \
        adcs    x24, x24, x14 ASM_LINE_END                  \
        mul     x14, x4, x7 ASM_LINE_END                    \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        mul     x14, x4, x8 ASM_LINE_END                    \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        mul     x14, x4, x9 ASM_LINE_END                    \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        mul     x14, x4, x10 ASM_LINE_END                   \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        mul     x14, x4, x11 ASM_LINE_END                   \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        mul     x14, x4, x12 ASM_LINE_END                   \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        mul     x14, x4, x13 ASM_LINE_END                   \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        cset    x21, hs ASM_LINE_END                        \
        umulh   x14, x4, x5 ASM_LINE_END                    \
        adds    x24, x24, x14 ASM_LINE_END                  \
        umulh   x14, x4, x6 ASM_LINE_END                    \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        umulh   x14, x4, x7 ASM_LINE_END                    \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        umulh   x14, x4, x8 ASM_LINE_END                    \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        umulh   x14, x4, x9 ASM_LINE_END                    \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        umulh   x14, x4, x10 ASM_LINE_END                   \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        umulh   x14, x4, x11 ASM_LINE_END                   \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        umulh   x14, x4, x12 ASM_LINE_END                   \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        umulh   x14, x4, x13 ASM_LINE_END                   \
        adc     x21, x21, x14 ASM_LINE_END                  \
        stp     x22, x23, [P0+48] ASM_LINE_END              \
        ldr     x3, [P1+64] ASM_LINE_END                    \
        mul     x14, x3, x5 ASM_LINE_END                    \
        adds    x24, x24, x14 ASM_LINE_END                  \
        mul     x14, x3, x6 ASM_LINE_END                    \
        adcs    x1, x1, x14 ASM_LINE_END                    \
        mul     x14, x3, x7 ASM_LINE_END                    \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        mul     x14, x3, x8 ASM_LINE_END                    \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        mul     x14, x3, x9 ASM_LINE_END                    \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        mul     x14, x3, x10 ASM_LINE_END                   \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        mul     x14, x3, x11 ASM_LINE_END                   \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        mul     x14, x3, x12 ASM_LINE_END                   \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        mul     x14, x3, x13 ASM_LINE_END                   \
        adc     x21, x21, x14 ASM_LINE_END                  \
        umulh   x14, x3, x5 ASM_LINE_END                    \
        adds    x1, x1, x14 ASM_LINE_END                    \
        umulh   x14, x3, x6 ASM_LINE_END                    \
        adcs    x0, x0, x14 ASM_LINE_END                    \
        umulh   x14, x3, x7 ASM_LINE_END                    \
        adcs    x15, x15, x14 ASM_LINE_END                  \
        umulh   x14, x3, x8 ASM_LINE_END                    \
        adcs    x16, x16, x14 ASM_LINE_END                  \
        umulh   x14, x3, x9 ASM_LINE_END                    \
        adcs    x17, x17, x14 ASM_LINE_END                  \
        umulh   x14, x3, x10 ASM_LINE_END                   \
        adcs    x19, x19, x14 ASM_LINE_END                  \
        umulh   x14, x3, x11 ASM_LINE_END                   \
        adcs    x20, x20, x14 ASM_LINE_END                  \
        umulh   x14, x3, x12 ASM_LINE_END                   \
        adc     x21, x21, x14 ASM_LINE_END                  \
        ldp     x5, x6, [P0] ASM_LINE_END                   \
        extr    x14, x1, x24, #9 ASM_LINE_END               \
        adds    x5, x5, x14 ASM_LINE_END                    \
        extr    x14, x0, x1, #9 ASM_LINE_END                \
        adcs    x6, x6, x14 ASM_LINE_END                    \
        ldp     x7, x8, [P0+16] ASM_LINE_END                \
        extr    x14, x15, x0, #9 ASM_LINE_END               \
        adcs    x7, x7, x14 ASM_LINE_END                    \
        extr    x14, x16, x15, #9 ASM_LINE_END              \
        adcs    x8, x8, x14 ASM_LINE_END                    \
        ldp     x9, x10, [P0+32] ASM_LINE_END               \
        extr    x14, x17, x16, #9 ASM_LINE_END              \
        adcs    x9, x9, x14 ASM_LINE_END                    \
        extr    x14, x19, x17, #9 ASM_LINE_END              \
        adcs    x10, x10, x14 ASM_LINE_END                  \
        ldp     x11, x12, [P0+48] ASM_LINE_END              \
        extr    x14, x20, x19, #9 ASM_LINE_END              \
        adcs    x11, x11, x14 ASM_LINE_END                  \
        extr    x14, x21, x20, #9 ASM_LINE_END              \
        adcs    x12, x12, x14 ASM_LINE_END                  \
        and     x13, x24, #0x1ff ASM_LINE_END               \
        lsr     x14, x21, #9 ASM_LINE_END                   \
        adc     x13, x13, x14 ASM_LINE_END                  \
        stp     x5, x6, [P0] ASM_LINE_END                   \
        stp     x7, x8, [P0+16] ASM_LINE_END                \
        stp     x9, x10, [P0+32] ASM_LINE_END               \
        stp     x11, x12, [P0+48] ASM_LINE_END              \
        str     x13, [P0+64]

// P0 = C * P1 - D * P2 == C * P1 + D * (p_521 - P2)

#define cmsub_p521(P0,C,P1,D,P2)                \
        ldp     x6, x7, [P1] ASM_LINE_END                   \
        mov     x1, #(C) ASM_LINE_END                       \
        mul     x3, x1, x6 ASM_LINE_END                     \
        mul     x4, x1, x7 ASM_LINE_END                     \
        umulh   x6, x1, x6 ASM_LINE_END                     \
        adds    x4, x4, x6 ASM_LINE_END                     \
        umulh   x7, x1, x7 ASM_LINE_END                     \
        ldp     x8, x9, [P1+16] ASM_LINE_END                \
        mul     x5, x1, x8 ASM_LINE_END                     \
        mul     x6, x1, x9 ASM_LINE_END                     \
        umulh   x8, x1, x8 ASM_LINE_END                     \
        adcs    x5, x5, x7 ASM_LINE_END                     \
        umulh   x9, x1, x9 ASM_LINE_END                     \
        adcs    x6, x6, x8 ASM_LINE_END                     \
        ldp     x10, x11, [P1+32] ASM_LINE_END              \
        mul     x7, x1, x10 ASM_LINE_END                    \
        mul     x8, x1, x11 ASM_LINE_END                    \
        umulh   x10, x1, x10 ASM_LINE_END                   \
        adcs    x7, x7, x9 ASM_LINE_END                     \
        umulh   x11, x1, x11 ASM_LINE_END                   \
        adcs    x8, x8, x10 ASM_LINE_END                    \
        ldp     x12, x13, [P1+48] ASM_LINE_END              \
        mul     x9, x1, x12 ASM_LINE_END                    \
        mul     x10, x1, x13 ASM_LINE_END                   \
        umulh   x12, x1, x12 ASM_LINE_END                   \
        adcs    x9, x9, x11 ASM_LINE_END                    \
        umulh   x13, x1, x13 ASM_LINE_END                   \
        adcs    x10, x10, x12 ASM_LINE_END                  \
        ldr     x14, [P1+64] ASM_LINE_END                   \
        mul     x11, x1, x14 ASM_LINE_END                   \
        adc     x11, x11, x13 ASM_LINE_END                  \
        mov     x1, #(D) ASM_LINE_END                       \
        ldp     x20, x21, [P2] ASM_LINE_END                 \
        mvn     x20, x20 ASM_LINE_END                       \
        mul     x0, x1, x20 ASM_LINE_END                    \
        umulh   x20, x1, x20 ASM_LINE_END                   \
        adds    x3, x3, x0 ASM_LINE_END                     \
        mvn     x21, x21 ASM_LINE_END                       \
        mul     x0, x1, x21 ASM_LINE_END                    \
        umulh   x21, x1, x21 ASM_LINE_END                   \
        adcs    x4, x4, x0 ASM_LINE_END                     \
        ldp     x22, x23, [P2+16] ASM_LINE_END              \
        mvn     x22, x22 ASM_LINE_END                       \
        mul     x0, x1, x22 ASM_LINE_END                    \
        umulh   x22, x1, x22 ASM_LINE_END                   \
        adcs    x5, x5, x0 ASM_LINE_END                     \
        mvn     x23, x23 ASM_LINE_END                       \
        mul     x0, x1, x23 ASM_LINE_END                    \
        umulh   x23, x1, x23 ASM_LINE_END                   \
        adcs    x6, x6, x0 ASM_LINE_END                     \
        ldp     x17, x19, [P2+32] ASM_LINE_END              \
        mvn     x17, x17 ASM_LINE_END                       \
        mul     x0, x1, x17 ASM_LINE_END                    \
        umulh   x17, x1, x17 ASM_LINE_END                   \
        adcs    x7, x7, x0 ASM_LINE_END                     \
        mvn     x19, x19 ASM_LINE_END                       \
        mul     x0, x1, x19 ASM_LINE_END                    \
        umulh   x19, x1, x19 ASM_LINE_END                   \
        adcs    x8, x8, x0 ASM_LINE_END                     \
        ldp     x2, x16, [P2+48] ASM_LINE_END               \
        mvn     x2, x2 ASM_LINE_END                         \
        mul     x0, x1, x2 ASM_LINE_END                     \
        umulh   x2, x1, x2 ASM_LINE_END                     \
        adcs    x9, x9, x0 ASM_LINE_END                     \
        mvn     x16, x16 ASM_LINE_END                       \
        mul     x0, x1, x16 ASM_LINE_END                    \
        umulh   x16, x1, x16 ASM_LINE_END                   \
        adcs    x10, x10, x0 ASM_LINE_END                   \
        ldr     x0, [P2+64] ASM_LINE_END                    \
        eor     x0, x0, #0x1ff ASM_LINE_END                 \
        mul     x0, x1, x0 ASM_LINE_END                     \
        adc     x11, x11, x0 ASM_LINE_END                   \
        adds    x4, x4, x20 ASM_LINE_END                    \
        adcs    x5, x5, x21 ASM_LINE_END                    \
        and     x15, x4, x5 ASM_LINE_END                    \
        adcs    x6, x6, x22 ASM_LINE_END                    \
        and     x15, x15, x6 ASM_LINE_END                   \
        adcs    x7, x7, x23 ASM_LINE_END                    \
        and     x15, x15, x7 ASM_LINE_END                   \
        adcs    x8, x8, x17 ASM_LINE_END                    \
        and     x15, x15, x8 ASM_LINE_END                   \
        adcs    x9, x9, x19 ASM_LINE_END                    \
        and     x15, x15, x9 ASM_LINE_END                   \
        adcs    x10, x10, x2 ASM_LINE_END                   \
        and     x15, x15, x10 ASM_LINE_END                  \
        adc     x11, x11, x16 ASM_LINE_END                  \
        lsr     x12, x11, #9 ASM_LINE_END                   \
        orr     x11, x11, #0xfffffffffffffe00 ASM_LINE_END  \
        cmp     xzr, xzr ASM_LINE_END                       \
        adcs    xzr, x3, x12 ASM_LINE_END                   \
        adcs    xzr, x15, xzr ASM_LINE_END                  \
        adcs    xzr, x11, xzr ASM_LINE_END                  \
        adcs    x3, x3, x12 ASM_LINE_END                    \
        adcs    x4, x4, xzr ASM_LINE_END                    \
        adcs    x5, x5, xzr ASM_LINE_END                    \
        adcs    x6, x6, xzr ASM_LINE_END                    \
        adcs    x7, x7, xzr ASM_LINE_END                    \
        adcs    x8, x8, xzr ASM_LINE_END                    \
        adcs    x9, x9, xzr ASM_LINE_END                    \
        adcs    x10, x10, xzr ASM_LINE_END                  \
        adc     x11, x11, xzr ASM_LINE_END                  \
        and     x11, x11, #0x1ff ASM_LINE_END               \
        stp     x3, x4, [P0] ASM_LINE_END                   \
        stp     x5, x6, [P0+16] ASM_LINE_END                \
        stp     x7, x8, [P0+32] ASM_LINE_END                \
        stp     x9, x10, [P0+48] ASM_LINE_END               \
        str     x11, [P0+64]

// P0 = 3 * P1 - 8 * P2 == 3 * P1 + 8 * (p_521 - P2)

#define cmsub38_p521(P0,P1,P2)                  \
        ldp     x6, x7, [P1] ASM_LINE_END                   \
        lsl     x3, x6, #1 ASM_LINE_END                     \
        adds    x3, x3, x6 ASM_LINE_END                     \
        extr    x4, x7, x6, #63 ASM_LINE_END                \
        adcs    x4, x4, x7 ASM_LINE_END                     \
        ldp     x8, x9, [P1+16] ASM_LINE_END                \
        extr    x5, x8, x7, #63 ASM_LINE_END                \
        adcs    x5, x5, x8 ASM_LINE_END                     \
        extr    x6, x9, x8, #63 ASM_LINE_END                \
        adcs    x6, x6, x9 ASM_LINE_END                     \
        ldp     x10, x11, [P1+32] ASM_LINE_END              \
        extr    x7, x10, x9, #63 ASM_LINE_END               \
        adcs    x7, x7, x10 ASM_LINE_END                    \
        extr    x8, x11, x10, #63 ASM_LINE_END              \
        adcs    x8, x8, x11 ASM_LINE_END                    \
        ldp     x12, x13, [P1+48] ASM_LINE_END              \
        extr    x9, x12, x11, #63 ASM_LINE_END              \
        adcs    x9, x9, x12 ASM_LINE_END                    \
        extr    x10, x13, x12, #63 ASM_LINE_END             \
        adcs    x10, x10, x13 ASM_LINE_END                  \
        ldr     x14, [P1+64] ASM_LINE_END                   \
        extr    x11, x14, x13, #63 ASM_LINE_END             \
        adc     x11, x11, x14 ASM_LINE_END                  \
        ldp     x20, x21, [P2] ASM_LINE_END                 \
        mvn     x20, x20 ASM_LINE_END                       \
        lsl     x0, x20, #3 ASM_LINE_END                    \
        adds    x3, x3, x0 ASM_LINE_END                     \
        mvn     x21, x21 ASM_LINE_END                       \
        extr    x0, x21, x20, #61 ASM_LINE_END              \
        adcs    x4, x4, x0 ASM_LINE_END                     \
        ldp     x22, x23, [P2+16] ASM_LINE_END              \
        mvn     x22, x22 ASM_LINE_END                       \
        extr    x0, x22, x21, #61 ASM_LINE_END              \
        adcs    x5, x5, x0 ASM_LINE_END                     \
        and     x15, x4, x5 ASM_LINE_END                    \
        mvn     x23, x23 ASM_LINE_END                       \
        extr    x0, x23, x22, #61 ASM_LINE_END              \
        adcs    x6, x6, x0 ASM_LINE_END                     \
        and     x15, x15, x6 ASM_LINE_END                   \
        ldp     x20, x21, [P2+32] ASM_LINE_END              \
        mvn     x20, x20 ASM_LINE_END                       \
        extr    x0, x20, x23, #61 ASM_LINE_END              \
        adcs    x7, x7, x0 ASM_LINE_END                     \
        and     x15, x15, x7 ASM_LINE_END                   \
        mvn     x21, x21 ASM_LINE_END                       \
        extr    x0, x21, x20, #61 ASM_LINE_END              \
        adcs    x8, x8, x0 ASM_LINE_END                     \
        and     x15, x15, x8 ASM_LINE_END                   \
        ldp     x22, x23, [P2+48] ASM_LINE_END              \
        mvn     x22, x22 ASM_LINE_END                       \
        extr    x0, x22, x21, #61 ASM_LINE_END              \
        adcs    x9, x9, x0 ASM_LINE_END                     \
        and     x15, x15, x9 ASM_LINE_END                   \
        mvn     x23, x23 ASM_LINE_END                       \
        extr    x0, x23, x22, #61 ASM_LINE_END              \
        adcs    x10, x10, x0 ASM_LINE_END                   \
        and     x15, x15, x10 ASM_LINE_END                  \
        ldr     x0, [P2+64] ASM_LINE_END                    \
        eor     x0, x0, #0x1ff ASM_LINE_END                 \
        extr    x0, x0, x23, #61 ASM_LINE_END               \
        adc     x11, x11, x0 ASM_LINE_END                   \
        lsr     x12, x11, #9 ASM_LINE_END                   \
        orr     x11, x11, #0xfffffffffffffe00 ASM_LINE_END  \
        cmp     xzr, xzr ASM_LINE_END                       \
        adcs    xzr, x3, x12 ASM_LINE_END                   \
        adcs    xzr, x15, xzr ASM_LINE_END                  \
        adcs    xzr, x11, xzr ASM_LINE_END                  \
        adcs    x3, x3, x12 ASM_LINE_END                    \
        adcs    x4, x4, xzr ASM_LINE_END                    \
        adcs    x5, x5, xzr ASM_LINE_END                    \
        adcs    x6, x6, xzr ASM_LINE_END                    \
        adcs    x7, x7, xzr ASM_LINE_END                    \
        adcs    x8, x8, xzr ASM_LINE_END                    \
        adcs    x9, x9, xzr ASM_LINE_END                    \
        adcs    x10, x10, xzr ASM_LINE_END                  \
        adc     x11, x11, xzr ASM_LINE_END                  \
        and     x11, x11, #0x1ff ASM_LINE_END               \
        stp     x3, x4, [P0] ASM_LINE_END                   \
        stp     x5, x6, [P0+16] ASM_LINE_END                \
        stp     x7, x8, [P0+32] ASM_LINE_END                \
        stp     x9, x10, [P0+48] ASM_LINE_END               \
        str     x11, [P0+64]

// P0 = 4 * P1 - P2 = 4 * P1 + (p_521 - P2)

#define cmsub41_p521(P0,P1,P2)                  \
        ldp     x6, x7, [P1] ASM_LINE_END                   \
        lsl     x3, x6, #2 ASM_LINE_END                     \
        extr    x4, x7, x6, #62 ASM_LINE_END                \
        ldp     x8, x9, [P1+16] ASM_LINE_END                \
        extr    x5, x8, x7, #62 ASM_LINE_END                \
        extr    x6, x9, x8, #62 ASM_LINE_END                \
        ldp     x10, x11, [P1+32] ASM_LINE_END              \
        extr    x7, x10, x9, #62 ASM_LINE_END               \
        extr    x8, x11, x10, #62 ASM_LINE_END              \
        ldp     x12, x13, [P1+48] ASM_LINE_END              \
        extr    x9, x12, x11, #62 ASM_LINE_END              \
        extr    x10, x13, x12, #62 ASM_LINE_END             \
        ldr     x14, [P1+64] ASM_LINE_END                   \
        extr    x11, x14, x13, #62 ASM_LINE_END             \
        ldp     x0, x1, [P2] ASM_LINE_END                   \
        mvn     x0, x0 ASM_LINE_END                         \
        adds    x3, x3, x0 ASM_LINE_END                     \
        sbcs    x4, x4, x1 ASM_LINE_END                     \
        ldp     x0, x1, [P2+16] ASM_LINE_END                \
        sbcs    x5, x5, x0 ASM_LINE_END                     \
        and     x15, x4, x5 ASM_LINE_END                    \
        sbcs    x6, x6, x1 ASM_LINE_END                     \
        and     x15, x15, x6 ASM_LINE_END                   \
        ldp     x0, x1, [P2+32] ASM_LINE_END                \
        sbcs    x7, x7, x0 ASM_LINE_END                     \
        and     x15, x15, x7 ASM_LINE_END                   \
        sbcs    x8, x8, x1 ASM_LINE_END                     \
        and     x15, x15, x8 ASM_LINE_END                   \
        ldp     x0, x1, [P2+48] ASM_LINE_END                \
        sbcs    x9, x9, x0 ASM_LINE_END                     \
        and     x15, x15, x9 ASM_LINE_END                   \
        sbcs    x10, x10, x1 ASM_LINE_END                   \
        and     x15, x15, x10 ASM_LINE_END                  \
        ldr     x0, [P2+64] ASM_LINE_END                    \
        eor     x0, x0, #0x1ff ASM_LINE_END                 \
        adc     x11, x11, x0 ASM_LINE_END                   \
        lsr     x12, x11, #9 ASM_LINE_END                   \
        orr     x11, x11, #0xfffffffffffffe00 ASM_LINE_END  \
        cmp     xzr, xzr ASM_LINE_END                       \
        adcs    xzr, x3, x12 ASM_LINE_END                   \
        adcs    xzr, x15, xzr ASM_LINE_END                  \
        adcs    xzr, x11, xzr ASM_LINE_END                  \
        adcs    x3, x3, x12 ASM_LINE_END                    \
        adcs    x4, x4, xzr ASM_LINE_END                    \
        adcs    x5, x5, xzr ASM_LINE_END                    \
        adcs    x6, x6, xzr ASM_LINE_END                    \
        adcs    x7, x7, xzr ASM_LINE_END                    \
        adcs    x8, x8, xzr ASM_LINE_END                    \
        adcs    x9, x9, xzr ASM_LINE_END                    \
        adcs    x10, x10, xzr ASM_LINE_END                  \
        adc     x11, x11, xzr ASM_LINE_END                  \
        and     x11, x11, #0x1ff ASM_LINE_END               \
        stp     x3, x4, [P0] ASM_LINE_END                   \
        stp     x5, x6, [P0+16] ASM_LINE_END                \
        stp     x7, x8, [P0+32] ASM_LINE_END                \
        stp     x9, x10, [P0+48] ASM_LINE_END               \
        str     x11, [P0+64]

S2N_BN_SYMBOL(p521_jdouble_alt):

// Save regs and make room on stack for temporary variables

        stp     x19, x20, [sp, #-16]!
        stp     x21, x22, [sp, #-16]!
        stp     x23, x24, [sp, #-16]!
        stp     x25, x26, [sp, #-16]!
        stp     x27, x28, [sp, #-16]!
        sub     sp, sp, NSPACE

// Move the input arguments to stable places

        mov     input_z, x0
        mov     input_x, x1

// Main code, just a sequence of basic field operations

// z2 = z^2
// y2 = y^2

        sqr_p521(z2,z_1)
        sqr_p521(y2,y_1)

// x2p = x^2 - z^4 = (x + z^2) * (x - z^2)

        add_p521(t1,x_1,z2)
        sub_p521(t2,x_1,z2)
        mul_p521(x2p,t1,t2)

// t1 = y + z
// x4p = x2p^2
// xy2 = x * y^2

        add_p521(t1,y_1,z_1)
        sqr_p521(x4p,x2p)
        weakmul_p521(xy2,x_1,y2)

// t2 = (y + z)^2

        sqr_p521(t2,t1)

// d = 12 * xy2 - 9 * x4p
// t1 = y^2 + 2 * y * z

        cmsub_p521(d,12,xy2,9,x4p)
        sub_p521(t1,t2,z2)

// y4 = y^4

        sqr_p521(y4,y2)

// z_3' = 2 * y * z
// dx2 = d * x2p

        sub_p521(z_3,t1,y2)
        weakmul_p521(dx2,d,x2p)

// x' = 4 * xy2 - d

        cmsub41_p521(x_3,xy2,d)

// y' = 3 * dx2 - 8 * y4

        cmsub38_p521(y_3,dx2,y4)

// Restore stack and registers

        add     sp, sp, NSPACE

        ldp     x27, x28, [sp], 16
        ldp     x25, x26, [sp], 16
        ldp     x23, x24, [sp], 16
        ldp     x21, x22, [sp], 16
        ldp     x19, x20, [sp], 16

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
