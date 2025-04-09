// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point addition on NIST curve P-521 in Jacobian coordinates
//
//    extern void p521_jadd_alt
//      (uint64_t p3[static 27],uint64_t p1[static 27],uint64_t p2[static 27]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples.
// A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3).
// It is assumed that all coordinates of the input points p1 and p2 are
// fully reduced mod p_521, that both z coordinates are nonzero and
// that neither p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents
// the same affine point as".
//
// Standard ARM ABI: X0 = p3, X1 = p1, X2 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p521_jadd_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p521_jadd_alt)

        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 72

// Stable homes for input arguments during main code sequence

#define input_z x26
#define input_x x27
#define input_y x28

// Pointer-offset pairs for inputs and outputs

#define x_1 input_x, #0
#define y_1 input_x, #NUMSIZE
#define z_1 input_x, #(2*NUMSIZE)

#define x_2 input_y, #0
#define y_2 input_y, #NUMSIZE
#define z_2 input_y, #(2*NUMSIZE)

#define x_3 input_z, #0
#define y_3 input_z, #NUMSIZE
#define z_3 input_z, #(2*NUMSIZE)

// Pointer-offset pairs for temporaries, with some aliasing
// NSPACE is the total stack needed for these temporaries

#define z1sq sp, #(NUMSIZE*0)
#define ww sp, #(NUMSIZE*0)
#define resx sp, #(NUMSIZE*0)

#define yd sp, #(NUMSIZE*1)
#define y2a sp, #(NUMSIZE*1)

#define x2a sp, #(NUMSIZE*2)
#define zzx2 sp, #(NUMSIZE*2)

#define zz sp, #(NUMSIZE*3)
#define t1 sp, #(NUMSIZE*3)

#define t2 sp, #(NUMSIZE*4)
#define x1a sp, #(NUMSIZE*4)
#define zzx1 sp, #(NUMSIZE*4)
#define resy sp, #(NUMSIZE*4)

#define xd sp, #(NUMSIZE*5)
#define z2sq sp, #(NUMSIZE*5)
#define resz sp, #(NUMSIZE*5)

#define y1a sp, #(NUMSIZE*6)

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

S2N_BN_SYMBOL(p521_jadd_alt):

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
        mov     input_y, x2

// Main code, just a sequence of basic field operations

        sqr_p521(z1sq,z_1)
        sqr_p521(z2sq,z_2)

        mul_p521(y1a,z_2,y_1)
        mul_p521(y2a,z_1,y_2)

        mul_p521(x2a,z1sq,x_2)
        mul_p521(x1a,z2sq,x_1)
        mul_p521(y2a,z1sq,y2a)
        mul_p521(y1a,z2sq,y1a)

        sub_p521(xd,x2a,x1a)
        sub_p521(yd,y2a,y1a)

        sqr_p521(zz,xd)
        sqr_p521(ww,yd)

        mul_p521(zzx1,zz,x1a)
        mul_p521(zzx2,zz,x2a)

        sub_p521(resx,ww,zzx1)
        sub_p521(t1,zzx2,zzx1)

        mul_p521(xd,xd,z_1)

        sub_p521(resx,resx,zzx2)

        sub_p521(t2,zzx1,resx)

        mul_p521(t1,t1,y1a)
        mul_p521(resz,xd,z_2)
        mul_p521(t2,yd,t2)

        sub_p521(resy,t2,t1)

// Load in the z coordinates of the inputs to check for P1 = 0 and P2 = 0
// The condition codes get set by a comparison (P2 != 0) - (P1 != 0)
// So  "HI" <=> CF /\ ~ZF <=> P1 = 0 /\ ~(P2 = 0)
// and "LO" <=> ~CF       <=> ~(P1 = 0) /\ P2 = 0
// Multiplex the z outputs accordingly and re-store in resz

        ldp     x0, x1, [z_1]
        ldp     x2, x3, [z_1+16]
        ldp     x4, x5, [z_1+32]
        ldp     x6, x7, [z_1+48]
        ldr     x8, [z_1+64]

        orr     x20, x0, x1
        orr     x21, x2, x3
        orr     x22, x4, x5
        orr     x23, x6, x7
        orr     x20, x20, x21
        orr     x22, x22, x23
        orr     x20, x20, x8
        orr     x20, x20, x22
        cmp     x20, xzr
        cset    x20, ne

        ldp     x10, x11, [z_2]
        ldp     x12, x13, [z_2+16]
        ldp     x14, x15, [z_2+32]
        ldp     x16, x17, [z_2+48]
        ldr     x19, [z_2+64]

        orr     x21, x10, x11
        orr     x22, x12, x13
        orr     x23, x14, x15
        orr     x24, x16, x17
        orr     x21, x21, x22
        orr     x23, x23, x24
        orr     x21, x21, x19
        orr     x21, x21, x23

        csel    x0, x0, x10, ne
        csel    x1, x1, x11, ne
        csel    x2, x2, x12, ne
        csel    x3, x3, x13, ne
        csel    x4, x4, x14, ne
        csel    x5, x5, x15, ne
        csel    x6, x6, x16, ne
        csel    x7, x7, x17, ne
        csel    x8, x8, x19, ne

        cmp     x21, xzr
        cset    x21, ne

        cmp     x21, x20

        ldp     x10, x11, [resz]
        ldp     x12, x13, [resz+16]
        ldp     x14, x15, [resz+32]
        ldp     x16, x17, [resz+48]
        ldr     x19, [resz+64]

        csel    x0, x0, x10, ne
        csel    x1, x1, x11, ne
        csel    x2, x2, x12, ne
        csel    x3, x3, x13, ne
        csel    x4, x4, x14, ne
        csel    x5, x5, x15, ne
        csel    x6, x6, x16, ne
        csel    x7, x7, x17, ne
        csel    x8, x8, x19, ne

        stp     x0, x1, [resz]
        stp     x2, x3, [resz+16]
        stp     x4, x5, [resz+32]
        stp     x6, x7, [resz+48]
        str     x8, [resz+64]

// Multiplex the x and y outputs too, keeping the results in registers

        ldp     x20, x21, [x_1]
        ldp     x0, x1, [resx]
        csel    x0, x20, x0, lo
        csel    x1, x21, x1, lo
        ldp     x20, x21, [x_2]
        csel    x0, x20, x0, hi
        csel    x1, x21, x1, hi

        ldp     x20, x21, [x_1+16]
        ldp     x2, x3, [resx+16]
        csel    x2, x20, x2, lo
        csel    x3, x21, x3, lo
        ldp     x20, x21, [x_2+16]
        csel    x2, x20, x2, hi
        csel    x3, x21, x3, hi

        ldp     x20, x21, [x_1+32]
        ldp     x4, x5, [resx+32]
        csel    x4, x20, x4, lo
        csel    x5, x21, x5, lo
        ldp     x20, x21, [x_2+32]
        csel    x4, x20, x4, hi
        csel    x5, x21, x5, hi

        ldp     x20, x21, [x_1+48]
        ldp     x6, x7, [resx+48]
        csel    x6, x20, x6, lo
        csel    x7, x21, x7, lo
        ldp     x20, x21, [x_2+48]
        csel    x6, x20, x6, hi
        csel    x7, x21, x7, hi

        ldr     x20, [x_1+64]
        ldr     x8, [resx+64]
        csel    x8, x20, x8, lo
        ldr     x21, [x_2+64]
        csel    x8, x21, x8, hi


        ldp     x20, x21, [y_1]
        ldp     x10, x11, [resy]
        csel    x10, x20, x10, lo
        csel    x11, x21, x11, lo
        ldp     x20, x21, [y_2]
        csel    x10, x20, x10, hi
        csel    x11, x21, x11, hi

        ldp     x20, x21, [y_1+16]
        ldp     x12, x13, [resy+16]
        csel    x12, x20, x12, lo
        csel    x13, x21, x13, lo
        ldp     x20, x21, [y_2+16]
        csel    x12, x20, x12, hi
        csel    x13, x21, x13, hi

        ldp     x20, x21, [y_1+32]
        ldp     x14, x15, [resy+32]
        csel    x14, x20, x14, lo
        csel    x15, x21, x15, lo
        ldp     x20, x21, [y_2+32]
        csel    x14, x20, x14, hi
        csel    x15, x21, x15, hi

        ldp     x20, x21, [y_1+48]
        ldp     x16, x17, [resy+48]
        csel    x16, x20, x16, lo
        csel    x17, x21, x17, lo
        ldp     x20, x21, [y_2+48]
        csel    x16, x20, x16, hi
        csel    x17, x21, x17, hi

        ldr     x20, [y_1+64]
        ldr     x19, [resy+64]
        csel    x19, x20, x19, lo
        ldr     x21, [y_2+64]
        csel    x19, x21, x19, hi

// Finally store back the multiplexed values

        stp     x0, x1, [x_3]
        stp     x2, x3, [x_3+16]
        stp     x4, x5, [x_3+32]
        stp     x6, x7, [x_3+48]
        str     x8, [x_3+64]

        ldp     x0, x1, [resz]
        ldp     x2, x3, [resz+16]
        ldp     x4, x5, [resz+32]
        ldp     x6, x7, [resz+48]
        ldr     x8, [resz+64]

        stp     x10, x11, [y_3]
        stp     x12, x13, [y_3+16]
        stp     x14, x15, [y_3+32]
        stp     x16, x17, [y_3+48]
        str     x19, [y_3+64]

        stp     x0, x1, [z_3]
        stp     x2, x3, [z_3+16]
        stp     x4, x5, [z_3+32]
        stp     x6, x7, [z_3+48]
        str     x8, [z_3+64]

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
