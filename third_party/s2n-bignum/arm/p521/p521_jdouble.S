// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// Point doubling on NIST curve P-521 in Jacobian coordinates
//
//    extern void p521_jdouble
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

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p521_jdouble)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p521_jdouble)

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
        ldp     x3, x4, [P1];                   \
        ldp     x5, x6, [P2];                   \
        mul     x15, x3, x5;                    \
        umulh   x16, x3, x5;                    \
        mul     x14, x3, x6;                    \
        umulh   x17, x3, x6;                    \
        adds    x16, x16, x14;                  \
        ldp     x7, x8, [P2+16];                \
        mul     x14, x3, x7;                    \
        umulh   x19, x3, x7;                    \
        adcs    x17, x17, x14;                  \
        mul     x14, x3, x8;                    \
        umulh   x20, x3, x8;                    \
        adcs    x19, x19, x14;                  \
        ldp     x9, x10, [P2+32];               \
        mul     x14, x3, x9;                    \
        umulh   x21, x3, x9;                    \
        adcs    x20, x20, x14;                  \
        mul     x14, x3, x10;                   \
        umulh   x22, x3, x10;                   \
        adcs    x21, x21, x14;                  \
        ldp     x11, x12, [P2+48];              \
        mul     x14, x3, x11;                   \
        umulh   x23, x3, x11;                   \
        adcs    x22, x22, x14;                  \
        ldr     x13, [P2+64];                   \
        mul     x14, x3, x12;                   \
        umulh   x24, x3, x12;                   \
        adcs    x23, x23, x14;                  \
        mul     x14, x3, x13;                   \
        umulh   x1, x3, x13;                    \
        adcs    x24, x24, x14;                  \
        adc     x1, x1, xzr;                    \
        mul     x14, x4, x5;                    \
        adds    x16, x16, x14;                  \
        mul     x14, x4, x6;                    \
        adcs    x17, x17, x14;                  \
        mul     x14, x4, x7;                    \
        adcs    x19, x19, x14;                  \
        mul     x14, x4, x8;                    \
        adcs    x20, x20, x14;                  \
        mul     x14, x4, x9;                    \
        adcs    x21, x21, x14;                  \
        mul     x14, x4, x10;                   \
        adcs    x22, x22, x14;                  \
        mul     x14, x4, x11;                   \
        adcs    x23, x23, x14;                  \
        mul     x14, x4, x12;                   \
        adcs    x24, x24, x14;                  \
        mul     x14, x4, x13;                   \
        adcs    x1, x1, x14;                    \
        cset    x0, hs;                         \
        umulh   x14, x4, x5;                    \
        adds    x17, x17, x14;                  \
        umulh   x14, x4, x6;                    \
        adcs    x19, x19, x14;                  \
        umulh   x14, x4, x7;                    \
        adcs    x20, x20, x14;                  \
        umulh   x14, x4, x8;                    \
        adcs    x21, x21, x14;                  \
        umulh   x14, x4, x9;                    \
        adcs    x22, x22, x14;                  \
        umulh   x14, x4, x10;                   \
        adcs    x23, x23, x14;                  \
        umulh   x14, x4, x11;                   \
        adcs    x24, x24, x14;                  \
        umulh   x14, x4, x12;                   \
        adcs    x1, x1, x14;                    \
        umulh   x14, x4, x13;                   \
        adc     x0, x0, x14;                    \
        stp     x15, x16, [P0];                 \
        ldp     x3, x4, [P1+16];                \
        mul     x14, x3, x5;                    \
        adds    x17, x17, x14;                  \
        mul     x14, x3, x6;                    \
        adcs    x19, x19, x14;                  \
        mul     x14, x3, x7;                    \
        adcs    x20, x20, x14;                  \
        mul     x14, x3, x8;                    \
        adcs    x21, x21, x14;                  \
        mul     x14, x3, x9;                    \
        adcs    x22, x22, x14;                  \
        mul     x14, x3, x10;                   \
        adcs    x23, x23, x14;                  \
        mul     x14, x3, x11;                   \
        adcs    x24, x24, x14;                  \
        mul     x14, x3, x12;                   \
        adcs    x1, x1, x14;                    \
        mul     x14, x3, x13;                   \
        adcs    x0, x0, x14;                    \
        cset    x15, hs;                        \
        umulh   x14, x3, x5;                    \
        adds    x19, x19, x14;                  \
        umulh   x14, x3, x6;                    \
        adcs    x20, x20, x14;                  \
        umulh   x14, x3, x7;                    \
        adcs    x21, x21, x14;                  \
        umulh   x14, x3, x8;                    \
        adcs    x22, x22, x14;                  \
        umulh   x14, x3, x9;                    \
        adcs    x23, x23, x14;                  \
        umulh   x14, x3, x10;                   \
        adcs    x24, x24, x14;                  \
        umulh   x14, x3, x11;                   \
        adcs    x1, x1, x14;                    \
        umulh   x14, x3, x12;                   \
        adcs    x0, x0, x14;                    \
        umulh   x14, x3, x13;                   \
        adc     x15, x15, x14;                  \
        mul     x14, x4, x5;                    \
        adds    x19, x19, x14;                  \
        mul     x14, x4, x6;                    \
        adcs    x20, x20, x14;                  \
        mul     x14, x4, x7;                    \
        adcs    x21, x21, x14;                  \
        mul     x14, x4, x8;                    \
        adcs    x22, x22, x14;                  \
        mul     x14, x4, x9;                    \
        adcs    x23, x23, x14;                  \
        mul     x14, x4, x10;                   \
        adcs    x24, x24, x14;                  \
        mul     x14, x4, x11;                   \
        adcs    x1, x1, x14;                    \
        mul     x14, x4, x12;                   \
        adcs    x0, x0, x14;                    \
        mul     x14, x4, x13;                   \
        adcs    x15, x15, x14;                  \
        cset    x16, hs;                        \
        umulh   x14, x4, x5;                    \
        adds    x20, x20, x14;                  \
        umulh   x14, x4, x6;                    \
        adcs    x21, x21, x14;                  \
        umulh   x14, x4, x7;                    \
        adcs    x22, x22, x14;                  \
        umulh   x14, x4, x8;                    \
        adcs    x23, x23, x14;                  \
        umulh   x14, x4, x9;                    \
        adcs    x24, x24, x14;                  \
        umulh   x14, x4, x10;                   \
        adcs    x1, x1, x14;                    \
        umulh   x14, x4, x11;                   \
        adcs    x0, x0, x14;                    \
        umulh   x14, x4, x12;                   \
        adcs    x15, x15, x14;                  \
        umulh   x14, x4, x13;                   \
        adc     x16, x16, x14;                  \
        stp     x17, x19, [P0+16];              \
        ldp     x3, x4, [P1+32];                \
        mul     x14, x3, x5;                    \
        adds    x20, x20, x14;                  \
        mul     x14, x3, x6;                    \
        adcs    x21, x21, x14;                  \
        mul     x14, x3, x7;                    \
        adcs    x22, x22, x14;                  \
        mul     x14, x3, x8;                    \
        adcs    x23, x23, x14;                  \
        mul     x14, x3, x9;                    \
        adcs    x24, x24, x14;                  \
        mul     x14, x3, x10;                   \
        adcs    x1, x1, x14;                    \
        mul     x14, x3, x11;                   \
        adcs    x0, x0, x14;                    \
        mul     x14, x3, x12;                   \
        adcs    x15, x15, x14;                  \
        mul     x14, x3, x13;                   \
        adcs    x16, x16, x14;                  \
        cset    x17, hs;                        \
        umulh   x14, x3, x5;                    \
        adds    x21, x21, x14;                  \
        umulh   x14, x3, x6;                    \
        adcs    x22, x22, x14;                  \
        umulh   x14, x3, x7;                    \
        adcs    x23, x23, x14;                  \
        umulh   x14, x3, x8;                    \
        adcs    x24, x24, x14;                  \
        umulh   x14, x3, x9;                    \
        adcs    x1, x1, x14;                    \
        umulh   x14, x3, x10;                   \
        adcs    x0, x0, x14;                    \
        umulh   x14, x3, x11;                   \
        adcs    x15, x15, x14;                  \
        umulh   x14, x3, x12;                   \
        adcs    x16, x16, x14;                  \
        umulh   x14, x3, x13;                   \
        adc     x17, x17, x14;                  \
        mul     x14, x4, x5;                    \
        adds    x21, x21, x14;                  \
        mul     x14, x4, x6;                    \
        adcs    x22, x22, x14;                  \
        mul     x14, x4, x7;                    \
        adcs    x23, x23, x14;                  \
        mul     x14, x4, x8;                    \
        adcs    x24, x24, x14;                  \
        mul     x14, x4, x9;                    \
        adcs    x1, x1, x14;                    \
        mul     x14, x4, x10;                   \
        adcs    x0, x0, x14;                    \
        mul     x14, x4, x11;                   \
        adcs    x15, x15, x14;                  \
        mul     x14, x4, x12;                   \
        adcs    x16, x16, x14;                  \
        mul     x14, x4, x13;                   \
        adcs    x17, x17, x14;                  \
        cset    x19, hs;                        \
        umulh   x14, x4, x5;                    \
        adds    x22, x22, x14;                  \
        umulh   x14, x4, x6;                    \
        adcs    x23, x23, x14;                  \
        umulh   x14, x4, x7;                    \
        adcs    x24, x24, x14;                  \
        umulh   x14, x4, x8;                    \
        adcs    x1, x1, x14;                    \
        umulh   x14, x4, x9;                    \
        adcs    x0, x0, x14;                    \
        umulh   x14, x4, x10;                   \
        adcs    x15, x15, x14;                  \
        umulh   x14, x4, x11;                   \
        adcs    x16, x16, x14;                  \
        umulh   x14, x4, x12;                   \
        adcs    x17, x17, x14;                  \
        umulh   x14, x4, x13;                   \
        adc     x19, x19, x14;                  \
        stp     x20, x21, [P0+32];              \
        ldp     x3, x4, [P1+48];                \
        mul     x14, x3, x5;                    \
        adds    x22, x22, x14;                  \
        mul     x14, x3, x6;                    \
        adcs    x23, x23, x14;                  \
        mul     x14, x3, x7;                    \
        adcs    x24, x24, x14;                  \
        mul     x14, x3, x8;                    \
        adcs    x1, x1, x14;                    \
        mul     x14, x3, x9;                    \
        adcs    x0, x0, x14;                    \
        mul     x14, x3, x10;                   \
        adcs    x15, x15, x14;                  \
        mul     x14, x3, x11;                   \
        adcs    x16, x16, x14;                  \
        mul     x14, x3, x12;                   \
        adcs    x17, x17, x14;                  \
        mul     x14, x3, x13;                   \
        adcs    x19, x19, x14;                  \
        cset    x20, hs;                        \
        umulh   x14, x3, x5;                    \
        adds    x23, x23, x14;                  \
        umulh   x14, x3, x6;                    \
        adcs    x24, x24, x14;                  \
        umulh   x14, x3, x7;                    \
        adcs    x1, x1, x14;                    \
        umulh   x14, x3, x8;                    \
        adcs    x0, x0, x14;                    \
        umulh   x14, x3, x9;                    \
        adcs    x15, x15, x14;                  \
        umulh   x14, x3, x10;                   \
        adcs    x16, x16, x14;                  \
        umulh   x14, x3, x11;                   \
        adcs    x17, x17, x14;                  \
        umulh   x14, x3, x12;                   \
        adcs    x19, x19, x14;                  \
        umulh   x14, x3, x13;                   \
        adc     x20, x20, x14;                  \
        mul     x14, x4, x5;                    \
        adds    x23, x23, x14;                  \
        mul     x14, x4, x6;                    \
        adcs    x24, x24, x14;                  \
        mul     x14, x4, x7;                    \
        adcs    x1, x1, x14;                    \
        mul     x14, x4, x8;                    \
        adcs    x0, x0, x14;                    \
        mul     x14, x4, x9;                    \
        adcs    x15, x15, x14;                  \
        mul     x14, x4, x10;                   \
        adcs    x16, x16, x14;                  \
        mul     x14, x4, x11;                   \
        adcs    x17, x17, x14;                  \
        mul     x14, x4, x12;                   \
        adcs    x19, x19, x14;                  \
        mul     x14, x4, x13;                   \
        adcs    x20, x20, x14;                  \
        cset    x21, hs;                        \
        umulh   x14, x4, x5;                    \
        adds    x24, x24, x14;                  \
        umulh   x14, x4, x6;                    \
        adcs    x1, x1, x14;                    \
        umulh   x14, x4, x7;                    \
        adcs    x0, x0, x14;                    \
        umulh   x14, x4, x8;                    \
        adcs    x15, x15, x14;                  \
        umulh   x14, x4, x9;                    \
        adcs    x16, x16, x14;                  \
        umulh   x14, x4, x10;                   \
        adcs    x17, x17, x14;                  \
        umulh   x14, x4, x11;                   \
        adcs    x19, x19, x14;                  \
        umulh   x14, x4, x12;                   \
        adcs    x20, x20, x14;                  \
        umulh   x14, x4, x13;                   \
        adc     x21, x21, x14;                  \
        stp     x22, x23, [P0+48];              \
        ldr     x3, [P1+64];                    \
        mul     x14, x3, x5;                    \
        adds    x24, x24, x14;                  \
        mul     x14, x3, x6;                    \
        adcs    x1, x1, x14;                    \
        mul     x14, x3, x7;                    \
        adcs    x0, x0, x14;                    \
        mul     x14, x3, x8;                    \
        adcs    x15, x15, x14;                  \
        mul     x14, x3, x9;                    \
        adcs    x16, x16, x14;                  \
        mul     x14, x3, x10;                   \
        adcs    x17, x17, x14;                  \
        mul     x14, x3, x11;                   \
        adcs    x19, x19, x14;                  \
        mul     x14, x3, x12;                   \
        adcs    x20, x20, x14;                  \
        mul     x14, x3, x13;                   \
        adc     x21, x21, x14;                  \
        umulh   x14, x3, x5;                    \
        adds    x1, x1, x14;                    \
        umulh   x14, x3, x6;                    \
        adcs    x0, x0, x14;                    \
        umulh   x14, x3, x7;                    \
        adcs    x15, x15, x14;                  \
        umulh   x14, x3, x8;                    \
        adcs    x16, x16, x14;                  \
        umulh   x14, x3, x9;                    \
        adcs    x17, x17, x14;                  \
        umulh   x14, x3, x10;                   \
        adcs    x19, x19, x14;                  \
        umulh   x14, x3, x11;                   \
        adcs    x20, x20, x14;                  \
        umulh   x14, x3, x12;                   \
        adc     x21, x21, x14;                  \
        cmp     xzr, xzr;                       \
        ldp     x5, x6, [P0];                   \
        extr    x14, x1, x24, #9;               \
        adcs    x5, x5, x14;                    \
        extr    x14, x0, x1, #9;                \
        adcs    x6, x6, x14;                    \
        ldp     x7, x8, [P0+16];                \
        extr    x14, x15, x0, #9;               \
        adcs    x7, x7, x14;                    \
        extr    x14, x16, x15, #9;              \
        adcs    x8, x8, x14;                    \
        ldp     x9, x10, [P0+32];               \
        extr    x14, x17, x16, #9;              \
        adcs    x9, x9, x14;                    \
        extr    x14, x19, x17, #9;              \
        adcs    x10, x10, x14;                  \
        ldp     x11, x12, [P0+48];              \
        extr    x14, x20, x19, #9;              \
        adcs    x11, x11, x14;                  \
        extr    x14, x21, x20, #9;              \
        adcs    x12, x12, x14;                  \
        orr     x13, x24, #0xfffffffffffffe00;  \
        lsr     x14, x21, #9;                   \
        adcs    x13, x13, x14;                  \
        sbcs    x5, x5, xzr;                    \
        sbcs    x6, x6, xzr;                    \
        sbcs    x7, x7, xzr;                    \
        sbcs    x8, x8, xzr;                    \
        sbcs    x9, x9, xzr;                    \
        sbcs    x10, x10, xzr;                  \
        sbcs    x11, x11, xzr;                  \
        sbcs    x12, x12, xzr;                  \
        sbc     x13, x13, xzr;                  \
        and     x13, x13, #0x1ff;               \
        stp     x5, x6, [P0];                   \
        stp     x7, x8, [P0+16];                \
        stp     x9, x10, [P0+32];               \
        stp     x11, x12, [P0+48];              \
        str     x13, [P0+64]

// Corresponds exactly to bignum_sqr_p521_alt

#define sqr_p521(P0,P1)                         \
        ldp     x2, x3, [P1];                   \
        mul     x11, x2, x3;                    \
        umulh   x12, x2, x3;                    \
        ldp     x4, x5, [P1+16];                \
        mul     x10, x2, x4;                    \
        umulh   x13, x2, x4;                    \
        adds    x12, x12, x10;                  \
        ldp     x6, x7, [P1+32];                \
        mul     x10, x2, x5;                    \
        umulh   x14, x2, x5;                    \
        adcs    x13, x13, x10;                  \
        ldp     x8, x9, [P1+48];                \
        mul     x10, x2, x6;                    \
        umulh   x15, x2, x6;                    \
        adcs    x14, x14, x10;                  \
        mul     x10, x2, x7;                    \
        umulh   x16, x2, x7;                    \
        adcs    x15, x15, x10;                  \
        mul     x10, x2, x8;                    \
        umulh   x17, x2, x8;                    \
        adcs    x16, x16, x10;                  \
        mul     x10, x2, x9;                    \
        umulh   x19, x2, x9;                    \
        adcs    x17, x17, x10;                  \
        adc     x19, x19, xzr;                  \
        mul     x10, x3, x4;                    \
        adds    x13, x13, x10;                  \
        mul     x10, x3, x5;                    \
        adcs    x14, x14, x10;                  \
        mul     x10, x3, x6;                    \
        adcs    x15, x15, x10;                  \
        mul     x10, x3, x7;                    \
        adcs    x16, x16, x10;                  \
        mul     x10, x3, x8;                    \
        adcs    x17, x17, x10;                  \
        mul     x10, x3, x9;                    \
        adcs    x19, x19, x10;                  \
        cset    x20, hs;                        \
        umulh   x10, x3, x4;                    \
        adds    x14, x14, x10;                  \
        umulh   x10, x3, x5;                    \
        adcs    x15, x15, x10;                  \
        umulh   x10, x3, x6;                    \
        adcs    x16, x16, x10;                  \
        umulh   x10, x3, x7;                    \
        adcs    x17, x17, x10;                  \
        umulh   x10, x3, x8;                    \
        adcs    x19, x19, x10;                  \
        umulh   x10, x3, x9;                    \
        adc     x20, x20, x10;                  \
        mul     x10, x6, x7;                    \
        umulh   x21, x6, x7;                    \
        adds    x20, x20, x10;                  \
        adc     x21, x21, xzr;                  \
        mul     x10, x4, x5;                    \
        adds    x15, x15, x10;                  \
        mul     x10, x4, x6;                    \
        adcs    x16, x16, x10;                  \
        mul     x10, x4, x7;                    \
        adcs    x17, x17, x10;                  \
        mul     x10, x4, x8;                    \
        adcs    x19, x19, x10;                  \
        mul     x10, x4, x9;                    \
        adcs    x20, x20, x10;                  \
        mul     x10, x6, x8;                    \
        adcs    x21, x21, x10;                  \
        cset    x22, hs;                        \
        umulh   x10, x4, x5;                    \
        adds    x16, x16, x10;                  \
        umulh   x10, x4, x6;                    \
        adcs    x17, x17, x10;                  \
        umulh   x10, x4, x7;                    \
        adcs    x19, x19, x10;                  \
        umulh   x10, x4, x8;                    \
        adcs    x20, x20, x10;                  \
        umulh   x10, x4, x9;                    \
        adcs    x21, x21, x10;                  \
        umulh   x10, x6, x8;                    \
        adc     x22, x22, x10;                  \
        mul     x10, x7, x8;                    \
        umulh   x23, x7, x8;                    \
        adds    x22, x22, x10;                  \
        adc     x23, x23, xzr;                  \
        mul     x10, x5, x6;                    \
        adds    x17, x17, x10;                  \
        mul     x10, x5, x7;                    \
        adcs    x19, x19, x10;                  \
        mul     x10, x5, x8;                    \
        adcs    x20, x20, x10;                  \
        mul     x10, x5, x9;                    \
        adcs    x21, x21, x10;                  \
        mul     x10, x6, x9;                    \
        adcs    x22, x22, x10;                  \
        mul     x10, x7, x9;                    \
        adcs    x23, x23, x10;                  \
        cset    x24, hs;                        \
        umulh   x10, x5, x6;                    \
        adds    x19, x19, x10;                  \
        umulh   x10, x5, x7;                    \
        adcs    x20, x20, x10;                  \
        umulh   x10, x5, x8;                    \
        adcs    x21, x21, x10;                  \
        umulh   x10, x5, x9;                    \
        adcs    x22, x22, x10;                  \
        umulh   x10, x6, x9;                    \
        adcs    x23, x23, x10;                  \
        umulh   x10, x7, x9;                    \
        adc     x24, x24, x10;                  \
        mul     x10, x8, x9;                    \
        umulh   x25, x8, x9;                    \
        adds    x24, x24, x10;                  \
        adc     x25, x25, xzr;                  \
        adds    x11, x11, x11;                  \
        adcs    x12, x12, x12;                  \
        adcs    x13, x13, x13;                  \
        adcs    x14, x14, x14;                  \
        adcs    x15, x15, x15;                  \
        adcs    x16, x16, x16;                  \
        adcs    x17, x17, x17;                  \
        adcs    x19, x19, x19;                  \
        adcs    x20, x20, x20;                  \
        adcs    x21, x21, x21;                  \
        adcs    x22, x22, x22;                  \
        adcs    x23, x23, x23;                  \
        adcs    x24, x24, x24;                  \
        adcs    x25, x25, x25;                  \
        cset    x0, hs;                         \
        umulh   x10, x2, x2;                    \
        adds    x11, x11, x10;                  \
        mul     x10, x3, x3;                    \
        adcs    x12, x12, x10;                  \
        umulh   x10, x3, x3;                    \
        adcs    x13, x13, x10;                  \
        mul     x10, x4, x4;                    \
        adcs    x14, x14, x10;                  \
        umulh   x10, x4, x4;                    \
        adcs    x15, x15, x10;                  \
        mul     x10, x5, x5;                    \
        adcs    x16, x16, x10;                  \
        umulh   x10, x5, x5;                    \
        adcs    x17, x17, x10;                  \
        mul     x10, x6, x6;                    \
        adcs    x19, x19, x10;                  \
        umulh   x10, x6, x6;                    \
        adcs    x20, x20, x10;                  \
        mul     x10, x7, x7;                    \
        adcs    x21, x21, x10;                  \
        umulh   x10, x7, x7;                    \
        adcs    x22, x22, x10;                  \
        mul     x10, x8, x8;                    \
        adcs    x23, x23, x10;                  \
        umulh   x10, x8, x8;                    \
        adcs    x24, x24, x10;                  \
        mul     x10, x9, x9;                    \
        adcs    x25, x25, x10;                  \
        umulh   x10, x9, x9;                    \
        adc     x0, x0, x10;                    \
        ldr     x1, [P1+64];                    \
        add     x1, x1, x1;                     \
        mul     x10, x1, x2;                    \
        adds    x19, x19, x10;                  \
        umulh   x10, x1, x2;                    \
        adcs    x20, x20, x10;                  \
        mul     x10, x1, x4;                    \
        adcs    x21, x21, x10;                  \
        umulh   x10, x1, x4;                    \
        adcs    x22, x22, x10;                  \
        mul     x10, x1, x6;                    \
        adcs    x23, x23, x10;                  \
        umulh   x10, x1, x6;                    \
        adcs    x24, x24, x10;                  \
        mul     x10, x1, x8;                    \
        adcs    x25, x25, x10;                  \
        umulh   x10, x1, x8;                    \
        adcs    x0, x0, x10;                    \
        lsr     x4, x1, #1;                     \
        mul     x4, x4, x4;                     \
        adc     x4, x4, xzr;                    \
        mul     x10, x1, x3;                    \
        adds    x20, x20, x10;                  \
        umulh   x10, x1, x3;                    \
        adcs    x21, x21, x10;                  \
        mul     x10, x1, x5;                    \
        adcs    x22, x22, x10;                  \
        umulh   x10, x1, x5;                    \
        adcs    x23, x23, x10;                  \
        mul     x10, x1, x7;                    \
        adcs    x24, x24, x10;                  \
        umulh   x10, x1, x7;                    \
        adcs    x25, x25, x10;                  \
        mul     x10, x1, x9;                    \
        adcs    x0, x0, x10;                    \
        umulh   x10, x1, x9;                    \
        adc     x4, x4, x10;                    \
        mul     x2, x2, x2;                     \
        cmp     xzr, xzr;                       \
        extr    x10, x20, x19, #9;              \
        adcs    x2, x2, x10;                    \
        extr    x10, x21, x20, #9;              \
        adcs    x11, x11, x10;                  \
        extr    x10, x22, x21, #9;              \
        adcs    x12, x12, x10;                  \
        extr    x10, x23, x22, #9;              \
        adcs    x13, x13, x10;                  \
        extr    x10, x24, x23, #9;              \
        adcs    x14, x14, x10;                  \
        extr    x10, x25, x24, #9;              \
        adcs    x15, x15, x10;                  \
        extr    x10, x0, x25, #9;               \
        adcs    x16, x16, x10;                  \
        extr    x10, x4, x0, #9;                \
        adcs    x17, x17, x10;                  \
        orr     x19, x19, #0xfffffffffffffe00;  \
        lsr     x10, x4, #9;                    \
        adcs    x19, x19, x10;                  \
        sbcs    x2, x2, xzr;                    \
        sbcs    x11, x11, xzr;                  \
        sbcs    x12, x12, xzr;                  \
        sbcs    x13, x13, xzr;                  \
        sbcs    x14, x14, xzr;                  \
        sbcs    x15, x15, xzr;                  \
        sbcs    x16, x16, xzr;                  \
        sbcs    x17, x17, xzr;                  \
        sbc     x19, x19, xzr;                  \
        and     x19, x19, #0x1ff;               \
        stp     x2, x11, [P0];                  \
        stp     x12, x13, [P0+16];              \
        stp     x14, x15, [P0+32];              \
        stp     x16, x17, [P0+48];              \
        str     x19, [P0+64]

// Corresponds exactly to bignum_add_p521

#define add_p521(P0,P1,P2)                      \
        cmp     xzr, xzr;                       \
        ldp     x5, x6, [P1];                   \
        ldp     x4, x3, [P2];                   \
        adcs    x5, x5, x4;                     \
        adcs    x6, x6, x3;                     \
        ldp     x7, x8, [P1+16];                \
        ldp     x4, x3, [P2+16];                \
        adcs    x7, x7, x4;                     \
        adcs    x8, x8, x3;                     \
        ldp     x9, x10, [P1+32];               \
        ldp     x4, x3, [P2+32];                \
        adcs    x9, x9, x4;                     \
        adcs    x10, x10, x3;                   \
        ldp     x11, x12, [P1+48];              \
        ldp     x4, x3, [P2+48];                \
        adcs    x11, x11, x4;                   \
        adcs    x12, x12, x3;                   \
        ldr     x13, [P1+64];                   \
        ldr     x4, [P2+64];                    \
        adc     x13, x13, x4;                   \
        subs    x4, x13, #512;                  \
        csetm   x4, hs;                         \
        sbcs    x5, x5, xzr;                    \
        and     x4, x4, #0x200;                 \
        sbcs    x6, x6, xzr;                    \
        sbcs    x7, x7, xzr;                    \
        sbcs    x8, x8, xzr;                    \
        sbcs    x9, x9, xzr;                    \
        sbcs    x10, x10, xzr;                  \
        sbcs    x11, x11, xzr;                  \
        sbcs    x12, x12, xzr;                  \
        sbc     x13, x13, x4;                   \
        stp     x5, x6, [P0];                   \
        stp     x7, x8, [P0+16];                \
        stp     x9, x10, [P0+32];               \
        stp     x11, x12, [P0+48];              \
        str     x13, [P0+64]

// Corresponds exactly to bignum_sub_p521

#define sub_p521(P0,P1,P2)                      \
        ldp     x5, x6, [P1];                   \
        ldp     x4, x3, [P2];                   \
        subs    x5, x5, x4;                     \
        sbcs    x6, x6, x3;                     \
        ldp     x7, x8, [P1+16];                \
        ldp     x4, x3, [P2+16];                \
        sbcs    x7, x7, x4;                     \
        sbcs    x8, x8, x3;                     \
        ldp     x9, x10, [P1+32];               \
        ldp     x4, x3, [P2+32];                \
        sbcs    x9, x9, x4;                     \
        sbcs    x10, x10, x3;                   \
        ldp     x11, x12, [P1+48];              \
        ldp     x4, x3, [P2+48];                \
        sbcs    x11, x11, x4;                   \
        sbcs    x12, x12, x3;                   \
        ldr     x13, [P1+64];                   \
        ldr     x4, [P2+64];                    \
        sbcs    x13, x13, x4;                   \
        sbcs    x5, x5, xzr;                    \
        sbcs    x6, x6, xzr;                    \
        sbcs    x7, x7, xzr;                    \
        sbcs    x8, x8, xzr;                    \
        sbcs    x9, x9, xzr;                    \
        sbcs    x10, x10, xzr;                  \
        sbcs    x11, x11, xzr;                  \
        sbcs    x12, x12, xzr;                  \
        sbcs    x13, x13, xzr;                  \
        and     x13, x13, #0x1ff;               \
        stp     x5, x6, [P0];                   \
        stp     x7, x8, [P0+16];                \
        stp     x9, x10, [P0+32];               \
        stp     x11, x12, [P0+48];              \
        str     x13, [P0+64]

// Weak multiplication not fully reducing

#define weakmul_p521(P0,P1,P2)                  \
        ldp     x3, x4, [P1];                   \
        ldp     x5, x6, [P2];                   \
        mul     x15, x3, x5;                    \
        umulh   x16, x3, x5;                    \
        mul     x14, x3, x6;                    \
        umulh   x17, x3, x6;                    \
        adds    x16, x16, x14;                  \
        ldp     x7, x8, [P2+16];                \
        mul     x14, x3, x7;                    \
        umulh   x19, x3, x7;                    \
        adcs    x17, x17, x14;                  \
        mul     x14, x3, x8;                    \
        umulh   x20, x3, x8;                    \
        adcs    x19, x19, x14;                  \
        ldp     x9, x10, [P2+32];               \
        mul     x14, x3, x9;                    \
        umulh   x21, x3, x9;                    \
        adcs    x20, x20, x14;                  \
        mul     x14, x3, x10;                   \
        umulh   x22, x3, x10;                   \
        adcs    x21, x21, x14;                  \
        ldp     x11, x12, [P2+48];              \
        mul     x14, x3, x11;                   \
        umulh   x23, x3, x11;                   \
        adcs    x22, x22, x14;                  \
        ldr     x13, [P2+64];                   \
        mul     x14, x3, x12;                   \
        umulh   x24, x3, x12;                   \
        adcs    x23, x23, x14;                  \
        mul     x14, x3, x13;                   \
        umulh   x1, x3, x13;                    \
        adcs    x24, x24, x14;                  \
        adc     x1, x1, xzr;                    \
        mul     x14, x4, x5;                    \
        adds    x16, x16, x14;                  \
        mul     x14, x4, x6;                    \
        adcs    x17, x17, x14;                  \
        mul     x14, x4, x7;                    \
        adcs    x19, x19, x14;                  \
        mul     x14, x4, x8;                    \
        adcs    x20, x20, x14;                  \
        mul     x14, x4, x9;                    \
        adcs    x21, x21, x14;                  \
        mul     x14, x4, x10;                   \
        adcs    x22, x22, x14;                  \
        mul     x14, x4, x11;                   \
        adcs    x23, x23, x14;                  \
        mul     x14, x4, x12;                   \
        adcs    x24, x24, x14;                  \
        mul     x14, x4, x13;                   \
        adcs    x1, x1, x14;                    \
        cset    x0, hs;                         \
        umulh   x14, x4, x5;                    \
        adds    x17, x17, x14;                  \
        umulh   x14, x4, x6;                    \
        adcs    x19, x19, x14;                  \
        umulh   x14, x4, x7;                    \
        adcs    x20, x20, x14;                  \
        umulh   x14, x4, x8;                    \
        adcs    x21, x21, x14;                  \
        umulh   x14, x4, x9;                    \
        adcs    x22, x22, x14;                  \
        umulh   x14, x4, x10;                   \
        adcs    x23, x23, x14;                  \
        umulh   x14, x4, x11;                   \
        adcs    x24, x24, x14;                  \
        umulh   x14, x4, x12;                   \
        adcs    x1, x1, x14;                    \
        umulh   x14, x4, x13;                   \
        adc     x0, x0, x14;                    \
        stp     x15, x16, [P0];                 \
        ldp     x3, x4, [P1+16];                \
        mul     x14, x3, x5;                    \
        adds    x17, x17, x14;                  \
        mul     x14, x3, x6;                    \
        adcs    x19, x19, x14;                  \
        mul     x14, x3, x7;                    \
        adcs    x20, x20, x14;                  \
        mul     x14, x3, x8;                    \
        adcs    x21, x21, x14;                  \
        mul     x14, x3, x9;                    \
        adcs    x22, x22, x14;                  \
        mul     x14, x3, x10;                   \
        adcs    x23, x23, x14;                  \
        mul     x14, x3, x11;                   \
        adcs    x24, x24, x14;                  \
        mul     x14, x3, x12;                   \
        adcs    x1, x1, x14;                    \
        mul     x14, x3, x13;                   \
        adcs    x0, x0, x14;                    \
        cset    x15, hs;                        \
        umulh   x14, x3, x5;                    \
        adds    x19, x19, x14;                  \
        umulh   x14, x3, x6;                    \
        adcs    x20, x20, x14;                  \
        umulh   x14, x3, x7;                    \
        adcs    x21, x21, x14;                  \
        umulh   x14, x3, x8;                    \
        adcs    x22, x22, x14;                  \
        umulh   x14, x3, x9;                    \
        adcs    x23, x23, x14;                  \
        umulh   x14, x3, x10;                   \
        adcs    x24, x24, x14;                  \
        umulh   x14, x3, x11;                   \
        adcs    x1, x1, x14;                    \
        umulh   x14, x3, x12;                   \
        adcs    x0, x0, x14;                    \
        umulh   x14, x3, x13;                   \
        adc     x15, x15, x14;                  \
        mul     x14, x4, x5;                    \
        adds    x19, x19, x14;                  \
        mul     x14, x4, x6;                    \
        adcs    x20, x20, x14;                  \
        mul     x14, x4, x7;                    \
        adcs    x21, x21, x14;                  \
        mul     x14, x4, x8;                    \
        adcs    x22, x22, x14;                  \
        mul     x14, x4, x9;                    \
        adcs    x23, x23, x14;                  \
        mul     x14, x4, x10;                   \
        adcs    x24, x24, x14;                  \
        mul     x14, x4, x11;                   \
        adcs    x1, x1, x14;                    \
        mul     x14, x4, x12;                   \
        adcs    x0, x0, x14;                    \
        mul     x14, x4, x13;                   \
        adcs    x15, x15, x14;                  \
        cset    x16, hs;                        \
        umulh   x14, x4, x5;                    \
        adds    x20, x20, x14;                  \
        umulh   x14, x4, x6;                    \
        adcs    x21, x21, x14;                  \
        umulh   x14, x4, x7;                    \
        adcs    x22, x22, x14;                  \
        umulh   x14, x4, x8;                    \
        adcs    x23, x23, x14;                  \
        umulh   x14, x4, x9;                    \
        adcs    x24, x24, x14;                  \
        umulh   x14, x4, x10;                   \
        adcs    x1, x1, x14;                    \
        umulh   x14, x4, x11;                   \
        adcs    x0, x0, x14;                    \
        umulh   x14, x4, x12;                   \
        adcs    x15, x15, x14;                  \
        umulh   x14, x4, x13;                   \
        adc     x16, x16, x14;                  \
        stp     x17, x19, [P0+16];              \
        ldp     x3, x4, [P1+32];                \
        mul     x14, x3, x5;                    \
        adds    x20, x20, x14;                  \
        mul     x14, x3, x6;                    \
        adcs    x21, x21, x14;                  \
        mul     x14, x3, x7;                    \
        adcs    x22, x22, x14;                  \
        mul     x14, x3, x8;                    \
        adcs    x23, x23, x14;                  \
        mul     x14, x3, x9;                    \
        adcs    x24, x24, x14;                  \
        mul     x14, x3, x10;                   \
        adcs    x1, x1, x14;                    \
        mul     x14, x3, x11;                   \
        adcs    x0, x0, x14;                    \
        mul     x14, x3, x12;                   \
        adcs    x15, x15, x14;                  \
        mul     x14, x3, x13;                   \
        adcs    x16, x16, x14;                  \
        cset    x17, hs;                        \
        umulh   x14, x3, x5;                    \
        adds    x21, x21, x14;                  \
        umulh   x14, x3, x6;                    \
        adcs    x22, x22, x14;                  \
        umulh   x14, x3, x7;                    \
        adcs    x23, x23, x14;                  \
        umulh   x14, x3, x8;                    \
        adcs    x24, x24, x14;                  \
        umulh   x14, x3, x9;                    \
        adcs    x1, x1, x14;                    \
        umulh   x14, x3, x10;                   \
        adcs    x0, x0, x14;                    \
        umulh   x14, x3, x11;                   \
        adcs    x15, x15, x14;                  \
        umulh   x14, x3, x12;                   \
        adcs    x16, x16, x14;                  \
        umulh   x14, x3, x13;                   \
        adc     x17, x17, x14;                  \
        mul     x14, x4, x5;                    \
        adds    x21, x21, x14;                  \
        mul     x14, x4, x6;                    \
        adcs    x22, x22, x14;                  \
        mul     x14, x4, x7;                    \
        adcs    x23, x23, x14;                  \
        mul     x14, x4, x8;                    \
        adcs    x24, x24, x14;                  \
        mul     x14, x4, x9;                    \
        adcs    x1, x1, x14;                    \
        mul     x14, x4, x10;                   \
        adcs    x0, x0, x14;                    \
        mul     x14, x4, x11;                   \
        adcs    x15, x15, x14;                  \
        mul     x14, x4, x12;                   \
        adcs    x16, x16, x14;                  \
        mul     x14, x4, x13;                   \
        adcs    x17, x17, x14;                  \
        cset    x19, hs;                        \
        umulh   x14, x4, x5;                    \
        adds    x22, x22, x14;                  \
        umulh   x14, x4, x6;                    \
        adcs    x23, x23, x14;                  \
        umulh   x14, x4, x7;                    \
        adcs    x24, x24, x14;                  \
        umulh   x14, x4, x8;                    \
        adcs    x1, x1, x14;                    \
        umulh   x14, x4, x9;                    \
        adcs    x0, x0, x14;                    \
        umulh   x14, x4, x10;                   \
        adcs    x15, x15, x14;                  \
        umulh   x14, x4, x11;                   \
        adcs    x16, x16, x14;                  \
        umulh   x14, x4, x12;                   \
        adcs    x17, x17, x14;                  \
        umulh   x14, x4, x13;                   \
        adc     x19, x19, x14;                  \
        stp     x20, x21, [P0+32];              \
        ldp     x3, x4, [P1+48];                \
        mul     x14, x3, x5;                    \
        adds    x22, x22, x14;                  \
        mul     x14, x3, x6;                    \
        adcs    x23, x23, x14;                  \
        mul     x14, x3, x7;                    \
        adcs    x24, x24, x14;                  \
        mul     x14, x3, x8;                    \
        adcs    x1, x1, x14;                    \
        mul     x14, x3, x9;                    \
        adcs    x0, x0, x14;                    \
        mul     x14, x3, x10;                   \
        adcs    x15, x15, x14;                  \
        mul     x14, x3, x11;                   \
        adcs    x16, x16, x14;                  \
        mul     x14, x3, x12;                   \
        adcs    x17, x17, x14;                  \
        mul     x14, x3, x13;                   \
        adcs    x19, x19, x14;                  \
        cset    x20, hs;                        \
        umulh   x14, x3, x5;                    \
        adds    x23, x23, x14;                  \
        umulh   x14, x3, x6;                    \
        adcs    x24, x24, x14;                  \
        umulh   x14, x3, x7;                    \
        adcs    x1, x1, x14;                    \
        umulh   x14, x3, x8;                    \
        adcs    x0, x0, x14;                    \
        umulh   x14, x3, x9;                    \
        adcs    x15, x15, x14;                  \
        umulh   x14, x3, x10;                   \
        adcs    x16, x16, x14;                  \
        umulh   x14, x3, x11;                   \
        adcs    x17, x17, x14;                  \
        umulh   x14, x3, x12;                   \
        adcs    x19, x19, x14;                  \
        umulh   x14, x3, x13;                   \
        adc     x20, x20, x14;                  \
        mul     x14, x4, x5;                    \
        adds    x23, x23, x14;                  \
        mul     x14, x4, x6;                    \
        adcs    x24, x24, x14;                  \
        mul     x14, x4, x7;                    \
        adcs    x1, x1, x14;                    \
        mul     x14, x4, x8;                    \
        adcs    x0, x0, x14;                    \
        mul     x14, x4, x9;                    \
        adcs    x15, x15, x14;                  \
        mul     x14, x4, x10;                   \
        adcs    x16, x16, x14;                  \
        mul     x14, x4, x11;                   \
        adcs    x17, x17, x14;                  \
        mul     x14, x4, x12;                   \
        adcs    x19, x19, x14;                  \
        mul     x14, x4, x13;                   \
        adcs    x20, x20, x14;                  \
        cset    x21, hs;                        \
        umulh   x14, x4, x5;                    \
        adds    x24, x24, x14;                  \
        umulh   x14, x4, x6;                    \
        adcs    x1, x1, x14;                    \
        umulh   x14, x4, x7;                    \
        adcs    x0, x0, x14;                    \
        umulh   x14, x4, x8;                    \
        adcs    x15, x15, x14;                  \
        umulh   x14, x4, x9;                    \
        adcs    x16, x16, x14;                  \
        umulh   x14, x4, x10;                   \
        adcs    x17, x17, x14;                  \
        umulh   x14, x4, x11;                   \
        adcs    x19, x19, x14;                  \
        umulh   x14, x4, x12;                   \
        adcs    x20, x20, x14;                  \
        umulh   x14, x4, x13;                   \
        adc     x21, x21, x14;                  \
        stp     x22, x23, [P0+48];              \
        ldr     x3, [P1+64];                    \
        mul     x14, x3, x5;                    \
        adds    x24, x24, x14;                  \
        mul     x14, x3, x6;                    \
        adcs    x1, x1, x14;                    \
        mul     x14, x3, x7;                    \
        adcs    x0, x0, x14;                    \
        mul     x14, x3, x8;                    \
        adcs    x15, x15, x14;                  \
        mul     x14, x3, x9;                    \
        adcs    x16, x16, x14;                  \
        mul     x14, x3, x10;                   \
        adcs    x17, x17, x14;                  \
        mul     x14, x3, x11;                   \
        adcs    x19, x19, x14;                  \
        mul     x14, x3, x12;                   \
        adcs    x20, x20, x14;                  \
        mul     x14, x3, x13;                   \
        adc     x21, x21, x14;                  \
        umulh   x14, x3, x5;                    \
        adds    x1, x1, x14;                    \
        umulh   x14, x3, x6;                    \
        adcs    x0, x0, x14;                    \
        umulh   x14, x3, x7;                    \
        adcs    x15, x15, x14;                  \
        umulh   x14, x3, x8;                    \
        adcs    x16, x16, x14;                  \
        umulh   x14, x3, x9;                    \
        adcs    x17, x17, x14;                  \
        umulh   x14, x3, x10;                   \
        adcs    x19, x19, x14;                  \
        umulh   x14, x3, x11;                   \
        adcs    x20, x20, x14;                  \
        umulh   x14, x3, x12;                   \
        adc     x21, x21, x14;                  \
        ldp     x5, x6, [P0];                   \
        extr    x14, x1, x24, #9;               \
        adds    x5, x5, x14;                    \
        extr    x14, x0, x1, #9;                \
        adcs    x6, x6, x14;                    \
        ldp     x7, x8, [P0+16];                \
        extr    x14, x15, x0, #9;               \
        adcs    x7, x7, x14;                    \
        extr    x14, x16, x15, #9;              \
        adcs    x8, x8, x14;                    \
        ldp     x9, x10, [P0+32];               \
        extr    x14, x17, x16, #9;              \
        adcs    x9, x9, x14;                    \
        extr    x14, x19, x17, #9;              \
        adcs    x10, x10, x14;                  \
        ldp     x11, x12, [P0+48];              \
        extr    x14, x20, x19, #9;              \
        adcs    x11, x11, x14;                  \
        extr    x14, x21, x20, #9;              \
        adcs    x12, x12, x14;                  \
        and     x13, x24, #0x1ff;               \
        lsr     x14, x21, #9;                   \
        adc     x13, x13, x14;                  \
        stp     x5, x6, [P0];                   \
        stp     x7, x8, [P0+16];                \
        stp     x9, x10, [P0+32];               \
        stp     x11, x12, [P0+48];              \
        str     x13, [P0+64]

// P0 = C * P1 - D * P2 == C * P1 + D * (p_521 - P2)

#define cmsub_p521(P0,C,P1,D,P2)                \
        ldp     x6, x7, [P1];                   \
        mov     x1, #(C);                       \
        mul     x3, x1, x6;                     \
        mul     x4, x1, x7;                     \
        umulh   x6, x1, x6;                     \
        adds    x4, x4, x6;                     \
        umulh   x7, x1, x7;                     \
        ldp     x8, x9, [P1+16];                \
        mul     x5, x1, x8;                     \
        mul     x6, x1, x9;                     \
        umulh   x8, x1, x8;                     \
        adcs    x5, x5, x7;                     \
        umulh   x9, x1, x9;                     \
        adcs    x6, x6, x8;                     \
        ldp     x10, x11, [P1+32];              \
        mul     x7, x1, x10;                    \
        mul     x8, x1, x11;                    \
        umulh   x10, x1, x10;                   \
        adcs    x7, x7, x9;                     \
        umulh   x11, x1, x11;                   \
        adcs    x8, x8, x10;                    \
        ldp     x12, x13, [P1+48];              \
        mul     x9, x1, x12;                    \
        mul     x10, x1, x13;                   \
        umulh   x12, x1, x12;                   \
        adcs    x9, x9, x11;                    \
        umulh   x13, x1, x13;                   \
        adcs    x10, x10, x12;                  \
        ldr     x14, [P1+64];                   \
        mul     x11, x1, x14;                   \
        adc     x11, x11, x13;                  \
        mov     x1, #(D);                       \
        ldp     x20, x21, [P2];                 \
        mvn     x20, x20;                       \
        mul     x0, x1, x20;                    \
        umulh   x20, x1, x20;                   \
        adds    x3, x3, x0;                     \
        mvn     x21, x21;                       \
        mul     x0, x1, x21;                    \
        umulh   x21, x1, x21;                   \
        adcs    x4, x4, x0;                     \
        ldp     x22, x23, [P2+16];              \
        mvn     x22, x22;                       \
        mul     x0, x1, x22;                    \
        umulh   x22, x1, x22;                   \
        adcs    x5, x5, x0;                     \
        mvn     x23, x23;                       \
        mul     x0, x1, x23;                    \
        umulh   x23, x1, x23;                   \
        adcs    x6, x6, x0;                     \
        ldp     x17, x19, [P2+32];              \
        mvn     x17, x17;                       \
        mul     x0, x1, x17;                    \
        umulh   x17, x1, x17;                   \
        adcs    x7, x7, x0;                     \
        mvn     x19, x19;                       \
        mul     x0, x1, x19;                    \
        umulh   x19, x1, x19;                   \
        adcs    x8, x8, x0;                     \
        ldp     x2, x16, [P2+48];               \
        mvn     x2, x2;                         \
        mul     x0, x1, x2;                     \
        umulh   x2, x1, x2;                     \
        adcs    x9, x9, x0;                     \
        mvn     x16, x16;                       \
        mul     x0, x1, x16;                    \
        umulh   x16, x1, x16;                   \
        adcs    x10, x10, x0;                   \
        ldr     x0, [P2+64];                    \
        eor     x0, x0, #0x1ff;                 \
        mul     x0, x1, x0;                     \
        adc     x11, x11, x0;                   \
        adds    x4, x4, x20;                    \
        adcs    x5, x5, x21;                    \
        and     x15, x4, x5;                    \
        adcs    x6, x6, x22;                    \
        and     x15, x15, x6;                   \
        adcs    x7, x7, x23;                    \
        and     x15, x15, x7;                   \
        adcs    x8, x8, x17;                    \
        and     x15, x15, x8;                   \
        adcs    x9, x9, x19;                    \
        and     x15, x15, x9;                   \
        adcs    x10, x10, x2;                   \
        and     x15, x15, x10;                  \
        adc     x11, x11, x16;                  \
        lsr     x12, x11, #9;                   \
        orr     x11, x11, #0xfffffffffffffe00;  \
        cmp     xzr, xzr;                       \
        adcs    xzr, x3, x12;                   \
        adcs    xzr, x15, xzr;                  \
        adcs    xzr, x11, xzr;                  \
        adcs    x3, x3, x12;                    \
        adcs    x4, x4, xzr;                    \
        adcs    x5, x5, xzr;                    \
        adcs    x6, x6, xzr;                    \
        adcs    x7, x7, xzr;                    \
        adcs    x8, x8, xzr;                    \
        adcs    x9, x9, xzr;                    \
        adcs    x10, x10, xzr;                  \
        adc     x11, x11, xzr;                  \
        and     x11, x11, #0x1ff;               \
        stp     x3, x4, [P0];                   \
        stp     x5, x6, [P0+16];                \
        stp     x7, x8, [P0+32];                \
        stp     x9, x10, [P0+48];               \
        str     x11, [P0+64]

// P0 = 3 * P1 - 8 * P2 == 3 * P1 + 8 * (p_521 - P2)

#define cmsub38_p521(P0,P1,P2)                  \
        ldp     x6, x7, [P1];                   \
        lsl     x3, x6, #1;                     \
        adds    x3, x3, x6;                     \
        extr    x4, x7, x6, #63;                \
        adcs    x4, x4, x7;                     \
        ldp     x8, x9, [P1+16];                \
        extr    x5, x8, x7, #63;                \
        adcs    x5, x5, x8;                     \
        extr    x6, x9, x8, #63;                \
        adcs    x6, x6, x9;                     \
        ldp     x10, x11, [P1+32];              \
        extr    x7, x10, x9, #63;               \
        adcs    x7, x7, x10;                    \
        extr    x8, x11, x10, #63;              \
        adcs    x8, x8, x11;                    \
        ldp     x12, x13, [P1+48];              \
        extr    x9, x12, x11, #63;              \
        adcs    x9, x9, x12;                    \
        extr    x10, x13, x12, #63;             \
        adcs    x10, x10, x13;                  \
        ldr     x14, [P1+64];                   \
        extr    x11, x14, x13, #63;             \
        adc     x11, x11, x14;                  \
        ldp     x20, x21, [P2];                 \
        mvn     x20, x20;                       \
        lsl     x0, x20, #3;                    \
        adds    x3, x3, x0;                     \
        mvn     x21, x21;                       \
        extr    x0, x21, x20, #61;              \
        adcs    x4, x4, x0;                     \
        ldp     x22, x23, [P2+16];              \
        mvn     x22, x22;                       \
        extr    x0, x22, x21, #61;              \
        adcs    x5, x5, x0;                     \
        and     x15, x4, x5;                    \
        mvn     x23, x23;                       \
        extr    x0, x23, x22, #61;              \
        adcs    x6, x6, x0;                     \
        and     x15, x15, x6;                   \
        ldp     x20, x21, [P2+32];              \
        mvn     x20, x20;                       \
        extr    x0, x20, x23, #61;              \
        adcs    x7, x7, x0;                     \
        and     x15, x15, x7;                   \
        mvn     x21, x21;                       \
        extr    x0, x21, x20, #61;              \
        adcs    x8, x8, x0;                     \
        and     x15, x15, x8;                   \
        ldp     x22, x23, [P2+48];              \
        mvn     x22, x22;                       \
        extr    x0, x22, x21, #61;              \
        adcs    x9, x9, x0;                     \
        and     x15, x15, x9;                   \
        mvn     x23, x23;                       \
        extr    x0, x23, x22, #61;              \
        adcs    x10, x10, x0;                   \
        and     x15, x15, x10;                  \
        ldr     x0, [P2+64];                    \
        eor     x0, x0, #0x1ff;                 \
        extr    x0, x0, x23, #61;               \
        adc     x11, x11, x0;                   \
        lsr     x12, x11, #9;                   \
        orr     x11, x11, #0xfffffffffffffe00;  \
        cmp     xzr, xzr;                       \
        adcs    xzr, x3, x12;                   \
        adcs    xzr, x15, xzr;                  \
        adcs    xzr, x11, xzr;                  \
        adcs    x3, x3, x12;                    \
        adcs    x4, x4, xzr;                    \
        adcs    x5, x5, xzr;                    \
        adcs    x6, x6, xzr;                    \
        adcs    x7, x7, xzr;                    \
        adcs    x8, x8, xzr;                    \
        adcs    x9, x9, xzr;                    \
        adcs    x10, x10, xzr;                  \
        adc     x11, x11, xzr;                  \
        and     x11, x11, #0x1ff;               \
        stp     x3, x4, [P0];                   \
        stp     x5, x6, [P0+16];                \
        stp     x7, x8, [P0+32];                \
        stp     x9, x10, [P0+48];               \
        str     x11, [P0+64]

// P0 = 4 * P1 - P2 = 4 * P1 + (p_521 - P2)

#define cmsub41_p521(P0,P1,P2)                  \
        ldp     x6, x7, [P1];                   \
        lsl     x3, x6, #2;                     \
        extr    x4, x7, x6, #62;                \
        ldp     x8, x9, [P1+16];                \
        extr    x5, x8, x7, #62;                \
        extr    x6, x9, x8, #62;                \
        ldp     x10, x11, [P1+32];              \
        extr    x7, x10, x9, #62;               \
        extr    x8, x11, x10, #62;              \
        ldp     x12, x13, [P1+48];              \
        extr    x9, x12, x11, #62;              \
        extr    x10, x13, x12, #62;             \
        ldr     x14, [P1+64];                   \
        extr    x11, x14, x13, #62;             \
        ldp     x0, x1, [P2];                   \
        mvn     x0, x0;                         \
        adds    x3, x3, x0;                     \
        sbcs    x4, x4, x1;                     \
        ldp     x0, x1, [P2+16];                \
        sbcs    x5, x5, x0;                     \
        and     x15, x4, x5;                    \
        sbcs    x6, x6, x1;                     \
        and     x15, x15, x6;                   \
        ldp     x0, x1, [P2+32];                \
        sbcs    x7, x7, x0;                     \
        and     x15, x15, x7;                   \
        sbcs    x8, x8, x1;                     \
        and     x15, x15, x8;                   \
        ldp     x0, x1, [P2+48];                \
        sbcs    x9, x9, x0;                     \
        and     x15, x15, x9;                   \
        sbcs    x10, x10, x1;                   \
        and     x15, x15, x10;                  \
        ldr     x0, [P2+64];                    \
        eor     x0, x0, #0x1ff;                 \
        adc     x11, x11, x0;                   \
        lsr     x12, x11, #9;                   \
        orr     x11, x11, #0xfffffffffffffe00;  \
        cmp     xzr, xzr;                       \
        adcs    xzr, x3, x12;                   \
        adcs    xzr, x15, xzr;                  \
        adcs    xzr, x11, xzr;                  \
        adcs    x3, x3, x12;                    \
        adcs    x4, x4, xzr;                    \
        adcs    x5, x5, xzr;                    \
        adcs    x6, x6, xzr;                    \
        adcs    x7, x7, xzr;                    \
        adcs    x8, x8, xzr;                    \
        adcs    x9, x9, xzr;                    \
        adcs    x10, x10, xzr;                  \
        adc     x11, x11, xzr;                  \
        and     x11, x11, #0x1ff;               \
        stp     x3, x4, [P0];                   \
        stp     x5, x6, [P0+16];                \
        stp     x7, x8, [P0+32];                \
        stp     x9, x10, [P0+48];               \
        str     x11, [P0+64]

S2N_BN_SYMBOL(p521_jdouble):

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
