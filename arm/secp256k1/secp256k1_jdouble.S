// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point doubling on SECG curve secp256k1 in Jacobian coordinates
//
//    extern void secp256k1_jdouble
//      (uint64_t p3[static 12],uint64_t p1[static 12]);
//
// Does p3 := 2 * p1 where all points are regarded as Jacobian triples.
// A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3).
// It is assumed that all coordinates of the input point are fully
// reduced mod p_256k1 and that the z coordinate is not zero.
//
// Standard ARM ABI: X0 = p3, X1 = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(secp256k1_jdouble)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(secp256k1_jdouble)

        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 32

// Stable homes for input arguments during main code sequence

#define input_z x15
#define input_x x16

// The magic constant 2^256 - p_256k1

#define pconst x17

// Pointer-offset pairs for inputs and outputs

#define x_1 input_x, #0
#define y_1 input_x, #NUMSIZE
#define z_1 input_x, #(2*NUMSIZE)

#define x_3 input_z, #0
#define y_3 input_z, #NUMSIZE
#define z_3 input_z, #(2*NUMSIZE)

// Pointer-offset pairs for temporaries

#define x_2 sp, #(NUMSIZE*0)
#define y_2 sp, #(NUMSIZE*1)
#define d sp, #(NUMSIZE*2)
#define tmp sp, #(NUMSIZE*3)
#define x_4 sp, #(NUMSIZE*4)
#define y_4 sp, #(NUMSIZE*6)
#define dx2 sp, #(NUMSIZE*8)
#define xy2 sp, #(NUMSIZE*10)

#define NSPACE #(NUMSIZE*12)

// Corresponds exactly to bignum_mul_p256k1_alt except for
// re-use of the pconst register for the constant 4294968273

#define mul_p256k1(P0,P1,P2)                    \
        ldp     x3, x4, [P1];                   \
        ldp     x7, x8, [P2];                   \
        mul     x12, x3, x7;                    \
        umulh   x13, x3, x7;                    \
        mul     x11, x3, x8;                    \
        umulh   x14, x3, x8;                    \
        adds    x13, x13, x11;                  \
        ldp     x9, x10, [P2+16];               \
        mul     x11, x3, x9;                    \
        umulh   x0, x3, x9;                     \
        adcs    x14, x14, x11;                  \
        mul     x11, x3, x10;                   \
        umulh   x1, x3, x10;                    \
        adcs    x0, x0, x11;                    \
        adc     x1, x1, xzr;                    \
        ldp     x5, x6, [P1+16];                \
        mul     x11, x4, x7;                    \
        adds    x13, x13, x11;                  \
        mul     x11, x4, x8;                    \
        adcs    x14, x14, x11;                  \
        mul     x11, x4, x9;                    \
        adcs    x0, x0, x11;                    \
        mul     x11, x4, x10;                   \
        adcs    x1, x1, x11;                    \
        umulh   x3, x4, x10;                    \
        adc     x3, x3, xzr;                    \
        umulh   x11, x4, x7;                    \
        adds    x14, x14, x11;                  \
        umulh   x11, x4, x8;                    \
        adcs    x0, x0, x11;                    \
        umulh   x11, x4, x9;                    \
        adcs    x1, x1, x11;                    \
        adc     x3, x3, xzr;                    \
        mul     x11, x5, x7;                    \
        adds    x14, x14, x11;                  \
        mul     x11, x5, x8;                    \
        adcs    x0, x0, x11;                    \
        mul     x11, x5, x9;                    \
        adcs    x1, x1, x11;                    \
        mul     x11, x5, x10;                   \
        adcs    x3, x3, x11;                    \
        umulh   x4, x5, x10;                    \
        adc     x4, x4, xzr;                    \
        umulh   x11, x5, x7;                    \
        adds    x0, x0, x11;                    \
        umulh   x11, x5, x8;                    \
        adcs    x1, x1, x11;                    \
        umulh   x11, x5, x9;                    \
        adcs    x3, x3, x11;                    \
        adc     x4, x4, xzr;                    \
        mul     x11, x6, x7;                    \
        adds    x0, x0, x11;                    \
        mul     x11, x6, x8;                    \
        adcs    x1, x1, x11;                    \
        mul     x11, x6, x9;                    \
        adcs    x3, x3, x11;                    \
        mul     x11, x6, x10;                   \
        adcs    x4, x4, x11;                    \
        umulh   x5, x6, x10;                    \
        adc     x5, x5, xzr;                    \
        umulh   x11, x6, x7;                    \
        adds    x1, x1, x11;                    \
        umulh   x11, x6, x8;                    \
        adcs    x3, x3, x11;                    \
        umulh   x11, x6, x9;                    \
        adcs    x4, x4, x11;                    \
        adc     x5, x5, xzr;                    \
        mul     x11, pconst, x1;                \
        umulh   x9, pconst, x1;                 \
        adds    x12, x12, x11;                  \
        mul     x11, pconst, x3;                \
        umulh   x3, pconst, x3;                 \
        adcs    x13, x13, x11;                  \
        mul     x11, pconst, x4;                \
        umulh   x4, pconst, x4;                 \
        adcs    x14, x14, x11;                  \
        mul     x11, pconst, x5;                \
        umulh   x5, pconst, x5;                 \
        adcs    x0, x0, x11;                    \
        cset    x1, cs;                         \
        adds    x13, x13, x9;                   \
        adcs    x14, x14, x3;                   \
        adcs    x0, x0, x4;                     \
        adc     x1, x1, x5;                     \
        add     x8, x1, #0x1;                   \
        mul     x11, pconst, x8;                \
        umulh   x9, pconst, x8;                 \
        adds    x12, x12, x11;                  \
        adcs    x13, x13, x9;                   \
        adcs    x14, x14, xzr;                  \
        adcs    x0, x0, xzr;                    \
        csel    x7, pconst, xzr, cc;            \
        subs    x12, x12, x7;                   \
        sbcs    x13, x13, xzr;                  \
        sbcs    x14, x14, xzr;                  \
        sbc     x0, x0, xzr;                    \
        stp     x12, x13, [P0];                 \
        stp     x14, x0, [P0+16]

// Corresponds exactly to bignum_sqr_p256k1_alt except for
// re-use of the pconst register for the constant 4294968273

#define sqr_p256k1(P0,P1)                       \
        ldp     x2, x3, [P1];                   \
        mul     x9, x2, x3;                     \
        umulh   x10, x2, x3;                    \
        ldp     x4, x5, [P1+16];                \
        mul     x11, x2, x5;                    \
        umulh   x12, x2, x5;                    \
        mul     x7, x2, x4;                     \
        umulh   x6, x2, x4;                     \
        adds    x10, x10, x7;                   \
        adcs    x11, x11, x6;                   \
        mul     x7, x3, x4;                     \
        umulh   x6, x3, x4;                     \
        adc     x6, x6, xzr;                    \
        adds    x11, x11, x7;                   \
        mul     x13, x4, x5;                    \
        umulh   x14, x4, x5;                    \
        adcs    x12, x12, x6;                   \
        mul     x7, x3, x5;                     \
        umulh   x6, x3, x5;                     \
        adc     x6, x6, xzr;                    \
        adds    x12, x12, x7;                   \
        adcs    x13, x13, x6;                   \
        adc     x14, x14, xzr;                  \
        adds    x9, x9, x9;                     \
        adcs    x10, x10, x10;                  \
        adcs    x11, x11, x11;                  \
        adcs    x12, x12, x12;                  \
        adcs    x13, x13, x13;                  \
        adcs    x14, x14, x14;                  \
        cset    x6, cs;                         \
        umulh   x7, x2, x2;                     \
        mul     x8, x2, x2;                     \
        adds    x9, x9, x7;                     \
        mul     x7, x3, x3;                     \
        adcs    x10, x10, x7;                   \
        umulh   x7, x3, x3;                     \
        adcs    x11, x11, x7;                   \
        mul     x7, x4, x4;                     \
        adcs    x12, x12, x7;                   \
        umulh   x7, x4, x4;                     \
        adcs    x13, x13, x7;                   \
        mul     x7, x5, x5;                     \
        adcs    x14, x14, x7;                   \
        umulh   x7, x5, x5;                     \
        adc     x6, x6, x7;                     \
        mul     x7, pconst, x12;                \
        umulh   x4, pconst, x12;                \
        adds    x8, x8, x7;                     \
        mul     x7, pconst, x13;                \
        umulh   x13, pconst, x13;               \
        adcs    x9, x9, x7;                     \
        mul     x7, pconst, x14;                \
        umulh   x14, pconst, x14;               \
        adcs    x10, x10, x7;                   \
        mul     x7, pconst, x6;                 \
        umulh   x6, pconst, x6;                 \
        adcs    x11, x11, x7;                   \
        cset    x12, cs;                        \
        adds    x9, x9, x4;                     \
        adcs    x10, x10, x13;                  \
        adcs    x11, x11, x14;                  \
        adc     x12, x12, x6;                   \
        add     x2, x12, #0x1;                  \
        mul     x7, pconst, x2;                 \
        umulh   x6, pconst, x2;                 \
        adds    x8, x8, x7;                     \
        adcs    x9, x9, x6;                     \
        adcs    x10, x10, xzr;                  \
        adcs    x11, x11, xzr;                  \
        csel    x3, pconst, xzr, cc;            \
        subs    x8, x8, x3;                     \
        sbcs    x9, x9, xzr;                    \
        sbcs    x10, x10, xzr;                  \
        sbc     x11, x11, xzr;                  \
        stp     x8, x9, [P0];                   \
        stp     x10, x11, [P0+16]

// Rough versions producing 5-word results

#define roughmul_p256k1(P0,P1,P2)               \
        ldp     x3, x4, [P1];                   \
        ldp     x7, x8, [P2];                   \
        mul     x12, x3, x7;                    \
        umulh   x13, x3, x7;                    \
        mul     x11, x3, x8;                    \
        umulh   x14, x3, x8;                    \
        adds    x13, x13, x11;                  \
        ldp     x9, x10, [P2+16];               \
        mul     x11, x3, x9;                    \
        umulh   x0, x3, x9;                     \
        adcs    x14, x14, x11;                  \
        mul     x11, x3, x10;                   \
        umulh   x1, x3, x10;                    \
        adcs    x0, x0, x11;                    \
        adc     x1, x1, xzr;                    \
        ldp     x5, x6, [P1+16];                \
        mul     x11, x4, x7;                    \
        adds    x13, x13, x11;                  \
        mul     x11, x4, x8;                    \
        adcs    x14, x14, x11;                  \
        mul     x11, x4, x9;                    \
        adcs    x0, x0, x11;                    \
        mul     x11, x4, x10;                   \
        adcs    x1, x1, x11;                    \
        umulh   x3, x4, x10;                    \
        adc     x3, x3, xzr;                    \
        umulh   x11, x4, x7;                    \
        adds    x14, x14, x11;                  \
        umulh   x11, x4, x8;                    \
        adcs    x0, x0, x11;                    \
        umulh   x11, x4, x9;                    \
        adcs    x1, x1, x11;                    \
        adc     x3, x3, xzr;                    \
        mul     x11, x5, x7;                    \
        adds    x14, x14, x11;                  \
        mul     x11, x5, x8;                    \
        adcs    x0, x0, x11;                    \
        mul     x11, x5, x9;                    \
        adcs    x1, x1, x11;                    \
        mul     x11, x5, x10;                   \
        adcs    x3, x3, x11;                    \
        umulh   x4, x5, x10;                    \
        adc     x4, x4, xzr;                    \
        umulh   x11, x5, x7;                    \
        adds    x0, x0, x11;                    \
        umulh   x11, x5, x8;                    \
        adcs    x1, x1, x11;                    \
        umulh   x11, x5, x9;                    \
        adcs    x3, x3, x11;                    \
        adc     x4, x4, xzr;                    \
        mul     x11, x6, x7;                    \
        adds    x0, x0, x11;                    \
        mul     x11, x6, x8;                    \
        adcs    x1, x1, x11;                    \
        mul     x11, x6, x9;                    \
        adcs    x3, x3, x11;                    \
        mul     x11, x6, x10;                   \
        adcs    x4, x4, x11;                    \
        umulh   x5, x6, x10;                    \
        adc     x5, x5, xzr;                    \
        umulh   x11, x6, x7;                    \
        adds    x1, x1, x11;                    \
        umulh   x11, x6, x8;                    \
        adcs    x3, x3, x11;                    \
        umulh   x11, x6, x9;                    \
        adcs    x4, x4, x11;                    \
        adc     x5, x5, xzr;                    \
        mul     x11, pconst, x1;                \
        umulh   x9, pconst, x1;                 \
        adds    x12, x12, x11;                  \
        mul     x11, pconst, x3;                \
        umulh   x3, pconst, x3;                 \
        adcs    x13, x13, x11;                  \
        mul     x11, pconst, x4;                \
        umulh   x4, pconst, x4;                 \
        adcs    x14, x14, x11;                  \
        mul     x11, pconst, x5;                \
        umulh   x5, pconst, x5;                 \
        adcs    x0, x0, x11;                    \
        cset    x1, cs;                         \
        adds    x13, x13, x9;                   \
        adcs    x14, x14, x3;                   \
        adcs    x0, x0, x4;                     \
        adc     x1, x1, x5;                     \
        stp     x12, x13, [P0];                 \
        stp     x14, x0, [P0+16];               \
        str     x1, [P0+32]

#define roughsqr_p256k1(P0,P1)                  \
        ldp     x2, x3, [P1];                   \
        mul     x9, x2, x3;                     \
        umulh   x10, x2, x3;                    \
        ldp     x4, x5, [P1+16];                \
        mul     x11, x2, x5;                    \
        umulh   x12, x2, x5;                    \
        mul     x7, x2, x4;                     \
        umulh   x6, x2, x4;                     \
        adds    x10, x10, x7;                   \
        adcs    x11, x11, x6;                   \
        mul     x7, x3, x4;                     \
        umulh   x6, x3, x4;                     \
        adc     x6, x6, xzr;                    \
        adds    x11, x11, x7;                   \
        mul     x13, x4, x5;                    \
        umulh   x14, x4, x5;                    \
        adcs    x12, x12, x6;                   \
        mul     x7, x3, x5;                     \
        umulh   x6, x3, x5;                     \
        adc     x6, x6, xzr;                    \
        adds    x12, x12, x7;                   \
        adcs    x13, x13, x6;                   \
        adc     x14, x14, xzr;                  \
        adds    x9, x9, x9;                     \
        adcs    x10, x10, x10;                  \
        adcs    x11, x11, x11;                  \
        adcs    x12, x12, x12;                  \
        adcs    x13, x13, x13;                  \
        adcs    x14, x14, x14;                  \
        cset    x6, cs;                         \
        umulh   x7, x2, x2;                     \
        mul     x8, x2, x2;                     \
        adds    x9, x9, x7;                     \
        mul     x7, x3, x3;                     \
        adcs    x10, x10, x7;                   \
        umulh   x7, x3, x3;                     \
        adcs    x11, x11, x7;                   \
        mul     x7, x4, x4;                     \
        adcs    x12, x12, x7;                   \
        umulh   x7, x4, x4;                     \
        adcs    x13, x13, x7;                   \
        mul     x7, x5, x5;                     \
        adcs    x14, x14, x7;                   \
        umulh   x7, x5, x5;                     \
        adc     x6, x6, x7;                     \
        mul     x7, pconst, x12;                \
        umulh   x4, pconst, x12;                \
        adds    x8, x8, x7;                     \
        mul     x7, pconst, x13;                \
        umulh   x13, pconst, x13;               \
        adcs    x9, x9, x7;                     \
        mul     x7, pconst, x14;                \
        umulh   x14, pconst, x14;               \
        adcs    x10, x10, x7;                   \
        mul     x7, pconst, x6;                 \
        umulh   x6, pconst, x6;                 \
        adcs    x11, x11, x7;                   \
        cset    x12, cs;                        \
        adds    x9, x9, x4;                     \
        adcs    x10, x10, x13;                  \
        adcs    x11, x11, x14;                  \
        adc     x12, x12, x6;                   \
        stp     x8, x9, [P0];                   \
        stp     x10, x11, [P0+16];              \
        str     x12, [P0+32]

// Weak doubling operation, staying in 4 digits but not in general
// fully normalizing modulo p_256k1

#define weakdouble_p256k1(P0,P1)                \
        ldp     x1, x2, [P1];                   \
        lsl     x0, x1, #1;                     \
        ldp     x3, x4, [P1+16];                \
        ands    xzr, x4, #0x8000000000000000;   \
        csel    x5, pconst, xzr, ne;            \
        extr    x1, x2, x1, #63;                \
        adds    x0, x0, x5;                     \
        extr    x2, x3, x2, #63;                \
        adcs    x1, x1, xzr;                    \
        extr    x3, x4, x3, #63;                \
        adcs    x2, x2, xzr;                    \
        stp     x0, x1, [P0];                   \
        adc     x3, x3, xzr;                    \
        stp     x2, x3, [P0+16]

// P0 = C * P1 - D * P2 with 5-word inputs P1 and P2
// Only used here with C = 12, D = 9, but could be used more generally.
// We start with (2^40 * 2^256 + C * P1) - (D * P2 + 2^40 * k)
// where p_256k1 = 2^256 - k (so k = 4294968273)

#define cmsub_p256k1(P0,C,P1,D,P2)              \
        mov     x10, C;                         \
        ldp     x4, x5, [P1];                   \
        mul     x0, x4, x10;                    \
        mul     x1, x5, x10;                    \
        ldp     x6, x7, [P1+16];                \
        mul     x2, x6, x10;                    \
        mul     x3, x7, x10;                    \
        ldr     x13, [P1+32];                   \
        umulh   x4, x4, x10;                    \
        adds    x1, x1, x4;                     \
        umulh   x5, x5, x10;                    \
        adcs    x2, x2, x5;                     \
        umulh   x6, x6, x10;                    \
        adcs    x3, x3, x6;                     \
        umulh   x4, x7, x10;                    \
        mul     x13, x13, x10;                  \
        adc     x9, x4, x13;                    \
        orr     x9, x9, #0x10000000000;         \
        /* [x9; x3;x2;x1;x0] = 2^40 * 2^256 + C * P1 */ \
        mov     x10, D;                         \
        ldp     x13, x14, [P2];                 \
        mul     x5, x14, x10;                   \
        umulh   x6, x14, x10;                   \
        adds    x5, x5, pconst, lsr #24;        \
        adc     x6, x6, xzr;                    \
        mul     x4, x13, x10;                   \
        adds    x4, x4, pconst, lsl #40;        \
        umulh   x13, x13, x10;                  \
        adcs    x5, x5, x13;                    \
        ldp     x13, x14, [P2+16];              \
        mul     x12, x13, x10;                  \
        umulh   x7, x13, x10;                   \
        ldr     x13, [P2+32];                   \
        adcs    x6, x6, x12;                    \
        mul     x12, x14, x10;                  \
        umulh   x8, x14, x10;                   \
        mul     x13, x13, x10;                  \
        adcs    x7, x7, x12;                    \
        adc     x8, x8, x13;                    \
        /* [x8; x7;x6;x5;x4] = D * P2 + 2^40 * k */ \
        subs    x0, x0, x4;                     \
        sbcs    x1, x1, x5;                     \
        sbcs    x2, x2, x6;                     \
        sbcs    x3, x3, x7;                     \
        sbc     x4, x9, x8;                     \
        /* [x4; x3;x2;x1;x0] = 2^40*p_256k1+result */ \
        add     x10, x4, #1;                    \
        /* (h + 1) is quotient estimate */      \
        mul     x4, pconst, x10;                \
        umulh   x5, pconst, x10;                \
        adds    x0, x0, x4;                     \
        adcs    x1, x1, x5;                     \
        adcs    x2, x2, xzr;                    \
        adcs    x3, x3, xzr;                    \
        csel    x11, pconst, xzr, cc;           \
        /* If un-correction needed */           \
        subs    x0, x0, x11;                    \
        sbcs    x1, x1, xzr;                    \
        stp     x0, x1, [P0];                   \
        sbcs    x2, x2, xzr;                    \
        sbc     x3, x3, xzr;                    \
        stp     x2, x3, [P0+16]

// P0 = 3 * P1 - 8 * P2 with 5-digit P1 and P2
// We start with (2^40 * 2^256 + 3 * P1) - (8 * P2 + 2^40 * k)
// where p_256k1 = 2^256 - k (so k = 4294968273)

#define cmsub38_p256k1(P0,P1,P2)                \
        mov     x10, #3;                        \
        ldp     x4, x5, [P1];                   \
        mul     x0, x4, x10;                    \
        mul     x1, x5, x10;                    \
        ldp     x6, x7, [P1+16];                \
        mul     x2, x6, x10;                    \
        mul     x3, x7, x10;                    \
        ldr     x13, [P1+32];                   \
        umulh   x4, x4, x10;                    \
        adds    x1, x1, x4;                     \
        umulh   x5, x5, x10;                    \
        adcs    x2, x2, x5;                     \
        umulh   x6, x6, x10;                    \
        adcs    x3, x3, x6;                     \
        umulh   x4, x7, x10;                    \
        mul     x13, x13, x10;                  \
        adc     x9, x4, x13;                    \
        orr     x9, x9, #0x10000000000;         \
        /*  [x9; x3;x2;x1;x0] = 2^40 * 2^256 + 3 * P1 */ \
        lsl     x12, pconst, #40;               \
        ldp     x13, x14, [P2];                 \
        lsl     x4, x13, #3;                    \
        adds    x4, x4, x12;                    \
        extr    x5, x14, x13, #61;              \
        lsr     x12, pconst, #24;               \
        adcs    x5, x5, x12;                    \
        ldp     x11, x12, [P2+16];              \
        extr    x6, x11, x14, #61;              \
        adcs    x6, x6, xzr;                    \
        ldr     x13, [P2+32];                   \
        extr    x7, x12, x11, #61;              \
        adcs    x7, x7, xzr;                    \
        extr    x8, x13, x12, #61;              \
        adc     x8, x8, xzr;                    \
        /* [x8; x7;x6;x5;x4] = 8 * P2 + 2^40 * k */ \
        subs    x0, x0, x4;                     \
        sbcs    x1, x1, x5;                     \
        sbcs    x2, x2, x6;                     \
        sbcs    x3, x3, x7;                     \
        sbc     x4, x9, x8;                     \
        /* [x4; x3;x2;x1;x0] = 2^40*p_256k1+result */ \
        add     x10, x4, #1;                    \
        /* (h + 1) is quotient estimate */      \
        mul     x4, pconst, x10;                \
        umulh   x5, pconst, x10;                \
        adds    x0, x0, x4;                     \
        adcs    x1, x1, x5;                     \
        adcs    x2, x2, xzr;                    \
        adcs    x3, x3, xzr;                    \
        csel    x11, pconst, xzr, cc;           \
        /*  If un-correction needed */          \
        subs    x0, x0, x11;                    \
        sbcs    x1, x1, xzr;                    \
        stp     x0, x1, [P0];                   \
        sbcs    x2, x2, xzr;                    \
        sbc     x3, x3, xzr;                    \
        stp     x2, x3, [P0+16]

// P0 = 4 * P1 - P2 with 5-digit P1, 4-digit P2 and result.
// This is done by direct subtraction of P2 since the method
// in bignum_cmul_p256k1 etc. for quotient estimation still
// works when the value to be reduced is negative, as
// long as it is  > -p_256k1, which is the case here.

#define cmsub41_p256k1(P0,P1,P2)                \
        ldp     x1, x2, [P1];                   \
        lsl     x0, x1, #2;                     \
        ldp     x6, x7, [P2];                   \
        subs    x0, x0, x6;                     \
        extr    x1, x2, x1, #62;                \
        sbcs    x1, x1, x7;                     \
        ldp     x3, x4, [P1+16];                \
        extr    x2, x3, x2, #62;                \
        ldp     x6, x7, [P2+16];                \
        sbcs    x2, x2, x6;                     \
        extr    x3, x4, x3, #62;                \
        sbcs    x3, x3, x7;                     \
        ldr     x5, [P1+32];                    \
        extr    x4, x5, x4, #62;                \
        sbc     x4, x4, xzr;                    \
        add     x5, x4, #1;                     \
        /* (h + 1) is quotient estimate */      \
        mul     x4, pconst, x5;                 \
        adds    x0, x0, x4;                     \
        umulh   x5, pconst, x5;                 \
        adcs    x1, x1, x5;                     \
        adcs    x2, x2, xzr;                    \
        adcs    x3, x3, xzr;                    \
        csel    x4, pconst, xzr, cc;            \
        /*  If un-correction needed */          \
        subs    x0, x0, x4;                     \
        sbcs    x1, x1, xzr;                    \
        stp     x0, x1, [P0];                   \
        sbcs    x2, x2, xzr;                    \
        sbc     x3, x3, xzr;                    \
        stp     x2, x3, [P0+16]

S2N_BN_SYMBOL(secp256k1_jdouble):

// Make room on stack for temp registers

        sub     sp, sp, NSPACE

// Move the input arguments to stable place

        mov     input_z, x0
        mov     input_x, x1

// Set up pconst =  4294968273, so p_256k1 = 2^256 - pconst

        mov     pconst, #977
        orr     pconst, pconst, #0x100000000

// Main sequence of operations

        // y_2 = y^2

        sqr_p256k1(y_2,y_1)

        // x_2 = x^2

        sqr_p256k1(x_2,x_1)

        // tmp = 2 * y_1 (in 4 words but not fully normalized)

        weakdouble_p256k1(tmp,y_1)

        // xy2 = x * y^2 (5-digit partially reduced)
        // x_4 = x^4 (5-digit partially reduced)

        roughmul_p256k1(xy2,x_1,y_2)
        roughsqr_p256k1(x_4,x_2)

        // z_3 = 2 * y_1 * z_1

        mul_p256k1(z_3,z_1,tmp)

        // d = 12 * xy2 - 9 * x_4

        cmsub_p256k1(d,12,xy2,9,x_4)

        // y4 = y2^2 (5-digit partially reduced)

        roughsqr_p256k1(y_4,y_2)

        // dx2 = d * x_2 (5-digit partially reduced)

        roughmul_p256k1(dx2,x_2,d)

        // x_3 = 4 * xy2 - d

        cmsub41_p256k1(x_3,xy2,d)

        // y_3 = 3 * dx2 - 8 * y_4

        cmsub38_p256k1(y_3,dx2,y_4)

// Restore stack and return

        add     sp, sp, NSPACE
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
