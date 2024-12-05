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

#define input_z x19
#define input_x x20

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

// Corresponds exactly to bignum_mul_p256k1 except for registers and
// re-use of the pconst register for the constant 4294968273

#define mul_p256k1(P0,P1,P2)                    \
        ldp     x3, x4, [P1];                   \
        ldp     x5, x6, [P2];                   \
        mul     x7, x3, x5;                     \
        umulh   x8, x3, x5;                     \
        mul     x9, x4, x6;                     \
        umulh   x10, x4, x6;                    \
        subs    x4, x4, x3;                     \
        cneg    x4, x4, lo;                     \
        csetm   x16, lo;                        \
        adds    x9, x9, x8;                     \
        adc     x10, x10, xzr;                  \
        subs    x3, x5, x6;                     \
        cneg    x3, x3, lo;                     \
        cinv    x16, x16, lo;                   \
        mul     x15, x4, x3;                    \
        umulh   x3, x4, x3;                     \
        adds    x8, x7, x9;                     \
        adcs    x9, x9, x10;                    \
        adc     x10, x10, xzr;                  \
        cmn     x16, #1;                        \
        eor     x15, x15, x16;                  \
        adcs    x8, x15, x8;                    \
        eor     x3, x3, x16;                    \
        adcs    x9, x3, x9;                     \
        adc     x10, x10, x16;                  \
        ldp     x3, x4, [P1+16];                \
        ldp     x5, x6, [P2+16];                \
        mul     x11, x3, x5;                    \
        umulh   x12, x3, x5;                    \
        mul     x13, x4, x6;                    \
        umulh   x14, x4, x6;                    \
        subs    x4, x4, x3;                     \
        cneg    x4, x4, lo;                     \
        csetm   x16, lo;                        \
        adds    x13, x13, x12;                  \
        adc     x14, x14, xzr;                  \
        subs    x3, x5, x6;                     \
        cneg    x3, x3, lo;                     \
        cinv    x16, x16, lo;                   \
        mul     x15, x4, x3;                    \
        umulh   x3, x4, x3;                     \
        adds    x12, x11, x13;                  \
        adcs    x13, x13, x14;                  \
        adc     x14, x14, xzr;                  \
        cmn     x16, #1;                        \
        eor     x15, x15, x16;                  \
        adcs    x12, x15, x12;                  \
        eor     x3, x3, x16;                    \
        adcs    x13, x3, x13;                   \
        adc     x14, x14, x16;                  \
        ldp     x3, x4, [P1+16];                \
        ldp     x15, x16, [P1];                 \
        subs    x3, x3, x15;                    \
        sbcs    x4, x4, x16;                    \
        csetm   x16, lo;                        \
        ldp     x15, x0, [P2];                  \
        subs    x5, x15, x5;                    \
        sbcs    x6, x0, x6;                     \
        csetm   x0, lo;                         \
        eor     x3, x3, x16;                    \
        subs    x3, x3, x16;                    \
        eor     x4, x4, x16;                    \
        sbc     x4, x4, x16;                    \
        eor     x5, x5, x0;                     \
        subs    x5, x5, x0;                     \
        eor     x6, x6, x0;                     \
        sbc     x6, x6, x0;                     \
        eor     x16, x0, x16;                   \
        adds    x11, x11, x9;                   \
        adcs    x12, x12, x10;                  \
        adcs    x13, x13, xzr;                  \
        adc     x14, x14, xzr;                  \
        mul     x2, x3, x5;                     \
        umulh   x0, x3, x5;                     \
        mul     x15, x4, x6;                    \
        umulh   x1, x4, x6;                     \
        subs    x4, x4, x3;                     \
        cneg    x4, x4, lo;                     \
        csetm   x9, lo;                         \
        adds    x15, x15, x0;                   \
        adc     x1, x1, xzr;                    \
        subs    x6, x5, x6;                     \
        cneg    x6, x6, lo;                     \
        cinv    x9, x9, lo;                     \
        mul     x5, x4, x6;                     \
        umulh   x6, x4, x6;                     \
        adds    x0, x2, x15;                    \
        adcs    x15, x15, x1;                   \
        adc     x1, x1, xzr;                    \
        cmn     x9, #1;                         \
        eor     x5, x5, x9;                     \
        adcs    x0, x5, x0;                     \
        eor     x6, x6, x9;                     \
        adcs    x15, x6, x15;                   \
        adc     x1, x1, x9;                     \
        adds    x9, x11, x7;                    \
        adcs    x10, x12, x8;                   \
        adcs    x11, x13, x11;                  \
        adcs    x12, x14, x12;                  \
        adcs    x13, x13, xzr;                  \
        adc     x14, x14, xzr;                  \
        cmn     x16, #1;                        \
        eor     x2, x2, x16;                    \
        adcs    x9, x2, x9;                     \
        eor     x0, x0, x16;                    \
        adcs    x10, x0, x10;                   \
        eor     x15, x15, x16;                  \
        adcs    x11, x15, x11;                  \
        eor     x1, x1, x16;                    \
        adcs    x12, x1, x12;                   \
        adcs    x13, x13, x16;                  \
        adc     x14, x14, x16;                  \
        mov     x16, #977;                      \
        mul     x3, pconst, x11;                \
        umulh   x5, pconst, x11;                \
        and     x15, x12, #0xffffffff;          \
        lsr     x2, x12, #32;                   \
        mul     x4, x16, x15;                   \
        madd    x15, x16, x2, x15;              \
        adds    x4, x4, x15, lsl #32;           \
        lsr     x15, x15, #32;                  \
        adc     x6, x2, x15;                    \
        mul     x11, pconst, x13;               \
        umulh   x13, pconst, x13;               \
        and     x15, x14, #0xffffffff;          \
        lsr     x2, x14, #32;                   \
        mul     x12, x16, x15;                  \
        madd    x15, x16, x2, x15;              \
        adds    x12, x12, x15, lsl #32;         \
        lsr     x15, x15, #32;                  \
        adc     x14, x2, x15;                   \
        adds    x7, x7, x3;                     \
        adcs    x8, x8, x4;                     \
        adcs    x9, x9, x11;                    \
        adcs    x10, x10, x12;                  \
        cset    x11, hs;                        \
        adds    x8, x8, x5;                     \
        adcs    x9, x9, x6;                     \
        adcs    x10, x10, x13;                  \
        adc     x11, x11, x14;                  \
        add     x0, x11, #1;                    \
        mul     x3, x16, x0;                    \
        lsr     x4, x0, #32;                    \
        adds    x3, x3, x0, lsl #32;            \
        adc     x4, xzr, x4;                    \
        adds    x7, x7, x3;                     \
        adcs    x8, x8, x4;                     \
        adcs    x9, x9, xzr;                    \
        adcs    x10, x10, xzr;                  \
        csel    x1, pconst, xzr, lo;            \
        subs    x7, x7, x1;                     \
        sbcs    x8, x8, xzr;                    \
        sbcs    x9, x9, xzr;                    \
        sbc     x10, x10, xzr;                  \
        stp     x7, x8, [P0];                   \
        stp     x9, x10, [P0+16]

// Corresponds exactly to bignum_sqr_p256k1 except for
// re-use of the pconst register for the constant 4294968273

#define sqr_p256k1(P0,P1)                       \
        ldp     x10, x11, [P1];                 \
        ldp     x12, x13, [P1+16];              \
        umull   x2, w10, w10;                   \
        lsr     x14, x10, #32;                  \
        umull   x3, w14, w14;                   \
        umull   x14, w10, w14;                  \
        adds    x2, x2, x14, lsl #33;           \
        lsr     x14, x14, #31;                  \
        adc     x3, x3, x14;                    \
        umull   x4, w11, w11;                   \
        lsr     x14, x11, #32;                  \
        umull   x5, w14, w14;                   \
        umull   x14, w11, w14;                  \
        mul     x15, x10, x11;                  \
        umulh   x16, x10, x11;                  \
        adds    x4, x4, x14, lsl #33;           \
        lsr     x14, x14, #31;                  \
        adc     x5, x5, x14;                    \
        adds    x15, x15, x15;                  \
        adcs    x16, x16, x16;                  \
        adc     x5, x5, xzr;                    \
        adds    x3, x3, x15;                    \
        adcs    x4, x4, x16;                    \
        adc     x5, x5, xzr;                    \
        umull   x6, w12, w12;                   \
        lsr     x14, x12, #32;                  \
        umull   x7, w14, w14;                   \
        umull   x14, w12, w14;                  \
        adds    x6, x6, x14, lsl #33;           \
        lsr     x14, x14, #31;                  \
        adc     x7, x7, x14;                    \
        umull   x8, w13, w13;                   \
        lsr     x14, x13, #32;                  \
        umull   x9, w14, w14;                   \
        umull   x14, w13, w14;                  \
        mul     x15, x12, x13;                  \
        umulh   x16, x12, x13;                  \
        adds    x8, x8, x14, lsl #33;           \
        lsr     x14, x14, #31;                  \
        adc     x9, x9, x14;                    \
        adds    x15, x15, x15;                  \
        adcs    x16, x16, x16;                  \
        adc     x9, x9, xzr;                    \
        adds    x7, x7, x15;                    \
        adcs    x8, x8, x16;                    \
        adc     x9, x9, xzr;                    \
        subs    x10, x10, x12;                  \
        sbcs    x11, x11, x13;                  \
        csetm   x16, lo;                        \
        eor     x10, x10, x16;                  \
        subs    x10, x10, x16;                  \
        eor     x11, x11, x16;                  \
        sbc     x11, x11, x16;                  \
        adds    x6, x6, x4;                     \
        adcs    x7, x7, x5;                     \
        adcs    x8, x8, xzr;                    \
        adc     x9, x9, xzr;                    \
        umull   x12, w10, w10;                  \
        lsr     x5, x10, #32;                   \
        umull   x13, w5, w5;                    \
        umull   x5, w10, w5;                    \
        adds    x12, x12, x5, lsl #33;          \
        lsr     x5, x5, #31;                    \
        adc     x13, x13, x5;                   \
        umull   x15, w11, w11;                  \
        lsr     x5, x11, #32;                   \
        umull   x14, w5, w5;                    \
        umull   x5, w11, w5;                    \
        mul     x4, x10, x11;                   \
        umulh   x16, x10, x11;                  \
        adds    x15, x15, x5, lsl #33;          \
        lsr     x5, x5, #31;                    \
        adc     x14, x14, x5;                   \
        adds    x4, x4, x4;                     \
        adcs    x16, x16, x16;                  \
        adc     x14, x14, xzr;                  \
        adds    x13, x13, x4;                   \
        adcs    x15, x15, x16;                  \
        adc     x14, x14, xzr;                  \
        adds    x4, x2, x6;                     \
        adcs    x5, x3, x7;                     \
        adcs    x6, x6, x8;                     \
        adcs    x7, x7, x9;                     \
        csetm   x16, lo;                        \
        subs    x4, x4, x12;                    \
        sbcs    x5, x5, x13;                    \
        sbcs    x6, x6, x15;                    \
        sbcs    x7, x7, x14;                    \
        adcs    x8, x8, x16;                    \
        adc     x9, x9, x16;                    \
        mov     x16, #977;                      \
        mul     x10, pconst, x6;                \
        umulh   x13, pconst, x6;                \
        and     x6, x7, #0xffffffff;            \
        lsr     x7, x7, #32;                    \
        mul     x11, x16, x6;                   \
        madd    x6, x16, x7, x6;                \
        adds    x11, x11, x6, lsl #32;          \
        lsr     x6, x6, #32;                    \
        adc     x14, x7, x6;                    \
        mul     x12, pconst, x8;                \
        umulh   x8, pconst, x8;                 \
        and     x6, x9, #0xffffffff;            \
        lsr     x7, x9, #32;                    \
        mul     x9, x16, x6;                    \
        madd    x6, x16, x7, x6;                \
        adds    x9, x9, x6, lsl #32;            \
        lsr     x6, x6, #32;                    \
        adc     x15, x7, x6;                    \
        adds    x2, x2, x10;                    \
        adcs    x3, x3, x11;                    \
        adcs    x4, x4, x12;                    \
        adcs    x5, x5, x9;                     \
        cset    x6, hs;                         \
        adds    x3, x3, x13;                    \
        adcs    x4, x4, x14;                    \
        adcs    x5, x5, x8;                     \
        adc     x6, x6, x15;                    \
        add     x6, x6, #1;                     \
        mul     x10, x16, x6;                   \
        lsr     x11, x6, #32;                   \
        adds    x10, x10, x6, lsl #32;          \
        adc     x11, xzr, x11;                  \
        adds    x2, x2, x10;                    \
        adcs    x3, x3, x11;                    \
        adcs    x4, x4, xzr;                    \
        adcs    x5, x5, xzr;                    \
        csel    x16, pconst, xzr, lo;           \
        subs    x2, x2, x16;                    \
        sbcs    x3, x3, xzr;                    \
        sbcs    x4, x4, xzr;                    \
        sbc     x5, x5, xzr;                    \
        stp     x2, x3, [P0];                   \
        stp     x4, x5, [P0+16]

// Rough versions producing 5-word results

#define roughmul_p256k1(P0,P1,P2)               \
        ldp     x3, x4, [P1];                   \
        ldp     x5, x6, [P2];                   \
        mul     x7, x3, x5;                     \
        umulh   x8, x3, x5;                     \
        mul     x9, x4, x6;                     \
        umulh   x10, x4, x6;                    \
        subs    x4, x4, x3;                     \
        cneg    x4, x4, lo;                     \
        csetm   x16, lo;                        \
        adds    x9, x9, x8;                     \
        adc     x10, x10, xzr;                  \
        subs    x3, x5, x6;                     \
        cneg    x3, x3, lo;                     \
        cinv    x16, x16, lo;                   \
        mul     x15, x4, x3;                    \
        umulh   x3, x4, x3;                     \
        adds    x8, x7, x9;                     \
        adcs    x9, x9, x10;                    \
        adc     x10, x10, xzr;                  \
        cmn     x16, #1;                        \
        eor     x15, x15, x16;                  \
        adcs    x8, x15, x8;                    \
        eor     x3, x3, x16;                    \
        adcs    x9, x3, x9;                     \
        adc     x10, x10, x16;                  \
        ldp     x3, x4, [P1+16];                \
        ldp     x5, x6, [P2+16];                \
        mul     x11, x3, x5;                    \
        umulh   x12, x3, x5;                    \
        mul     x13, x4, x6;                    \
        umulh   x14, x4, x6;                    \
        subs    x4, x4, x3;                     \
        cneg    x4, x4, lo;                     \
        csetm   x16, lo;                        \
        adds    x13, x13, x12;                  \
        adc     x14, x14, xzr;                  \
        subs    x3, x5, x6;                     \
        cneg    x3, x3, lo;                     \
        cinv    x16, x16, lo;                   \
        mul     x15, x4, x3;                    \
        umulh   x3, x4, x3;                     \
        adds    x12, x11, x13;                  \
        adcs    x13, x13, x14;                  \
        adc     x14, x14, xzr;                  \
        cmn     x16, #1;                        \
        eor     x15, x15, x16;                  \
        adcs    x12, x15, x12;                  \
        eor     x3, x3, x16;                    \
        adcs    x13, x3, x13;                   \
        adc     x14, x14, x16;                  \
        ldp     x3, x4, [P1+16];                \
        ldp     x15, x16, [P1];                 \
        subs    x3, x3, x15;                    \
        sbcs    x4, x4, x16;                    \
        csetm   x16, lo;                        \
        ldp     x15, x0, [P2];                  \
        subs    x5, x15, x5;                    \
        sbcs    x6, x0, x6;                     \
        csetm   x0, lo;                         \
        eor     x3, x3, x16;                    \
        subs    x3, x3, x16;                    \
        eor     x4, x4, x16;                    \
        sbc     x4, x4, x16;                    \
        eor     x5, x5, x0;                     \
        subs    x5, x5, x0;                     \
        eor     x6, x6, x0;                     \
        sbc     x6, x6, x0;                     \
        eor     x16, x0, x16;                   \
        adds    x11, x11, x9;                   \
        adcs    x12, x12, x10;                  \
        adcs    x13, x13, xzr;                  \
        adc     x14, x14, xzr;                  \
        mul     x2, x3, x5;                     \
        umulh   x0, x3, x5;                     \
        mul     x15, x4, x6;                    \
        umulh   x1, x4, x6;                     \
        subs    x4, x4, x3;                     \
        cneg    x4, x4, lo;                     \
        csetm   x9, lo;                         \
        adds    x15, x15, x0;                   \
        adc     x1, x1, xzr;                    \
        subs    x6, x5, x6;                     \
        cneg    x6, x6, lo;                     \
        cinv    x9, x9, lo;                     \
        mul     x5, x4, x6;                     \
        umulh   x6, x4, x6;                     \
        adds    x0, x2, x15;                    \
        adcs    x15, x15, x1;                   \
        adc     x1, x1, xzr;                    \
        cmn     x9, #1;                         \
        eor     x5, x5, x9;                     \
        adcs    x0, x5, x0;                     \
        eor     x6, x6, x9;                     \
        adcs    x15, x6, x15;                   \
        adc     x1, x1, x9;                     \
        adds    x9, x11, x7;                    \
        adcs    x10, x12, x8;                   \
        adcs    x11, x13, x11;                  \
        adcs    x12, x14, x12;                  \
        adcs    x13, x13, xzr;                  \
        adc     x14, x14, xzr;                  \
        cmn     x16, #1;                        \
        eor     x2, x2, x16;                    \
        adcs    x9, x2, x9;                     \
        eor     x0, x0, x16;                    \
        adcs    x10, x0, x10;                   \
        eor     x15, x15, x16;                  \
        adcs    x11, x15, x11;                  \
        eor     x1, x1, x16;                    \
        adcs    x12, x1, x12;                   \
        adcs    x13, x13, x16;                  \
        adc     x14, x14, x16;                  \
        mov     x16, #977;                      \
        mul     x3, pconst, x11;                \
        umulh   x5, pconst, x11;                \
        and     x15, x12, #0xffffffff;          \
        lsr     x2, x12, #32;                   \
        mul     x4, x16, x15;                   \
        madd    x15, x16, x2, x15;              \
        adds    x4, x4, x15, lsl #32;           \
        lsr     x15, x15, #32;                  \
        adc     x6, x2, x15;                    \
        mul     x11, pconst, x13;               \
        umulh   x13, pconst, x13;               \
        and     x15, x14, #0xffffffff;          \
        lsr     x2, x14, #32;                   \
        mul     x12, x16, x15;                  \
        madd    x15, x16, x2, x15;              \
        adds    x12, x12, x15, lsl #32;         \
        lsr     x15, x15, #32;                  \
        adc     x14, x2, x15;                   \
        adds    x7, x7, x3;                     \
        adcs    x8, x8, x4;                     \
        adcs    x9, x9, x11;                    \
        adcs    x10, x10, x12;                  \
        cset    x11, hs;                        \
        adds    x8, x8, x5;                     \
        adcs    x9, x9, x6;                     \
        adcs    x10, x10, x13;                  \
        adc     x11, x11, x14;                  \
        stp     x7, x8, [P0];                   \
        stp     x9, x10, [P0+16];               \
        str     x11, [P0+32]

#define roughsqr_p256k1(P0,P1)                  \
        ldp     x10, x11, [P1];                 \
        ldp     x12, x13, [P1+16];              \
        umull   x2, w10, w10;                   \
        lsr     x14, x10, #32;                  \
        umull   x3, w14, w14;                   \
        umull   x14, w10, w14;                  \
        adds    x2, x2, x14, lsl #33;           \
        lsr     x14, x14, #31;                  \
        adc     x3, x3, x14;                    \
        umull   x4, w11, w11;                   \
        lsr     x14, x11, #32;                  \
        umull   x5, w14, w14;                   \
        umull   x14, w11, w14;                  \
        mul     x15, x10, x11;                  \
        umulh   x16, x10, x11;                  \
        adds    x4, x4, x14, lsl #33;           \
        lsr     x14, x14, #31;                  \
        adc     x5, x5, x14;                    \
        adds    x15, x15, x15;                  \
        adcs    x16, x16, x16;                  \
        adc     x5, x5, xzr;                    \
        adds    x3, x3, x15;                    \
        adcs    x4, x4, x16;                    \
        adc     x5, x5, xzr;                    \
        umull   x6, w12, w12;                   \
        lsr     x14, x12, #32;                  \
        umull   x7, w14, w14;                   \
        umull   x14, w12, w14;                  \
        adds    x6, x6, x14, lsl #33;           \
        lsr     x14, x14, #31;                  \
        adc     x7, x7, x14;                    \
        umull   x8, w13, w13;                   \
        lsr     x14, x13, #32;                  \
        umull   x9, w14, w14;                   \
        umull   x14, w13, w14;                  \
        mul     x15, x12, x13;                  \
        umulh   x16, x12, x13;                  \
        adds    x8, x8, x14, lsl #33;           \
        lsr     x14, x14, #31;                  \
        adc     x9, x9, x14;                    \
        adds    x15, x15, x15;                  \
        adcs    x16, x16, x16;                  \
        adc     x9, x9, xzr;                    \
        adds    x7, x7, x15;                    \
        adcs    x8, x8, x16;                    \
        adc     x9, x9, xzr;                    \
        subs    x10, x10, x12;                  \
        sbcs    x11, x11, x13;                  \
        csetm   x16, lo;                        \
        eor     x10, x10, x16;                  \
        subs    x10, x10, x16;                  \
        eor     x11, x11, x16;                  \
        sbc     x11, x11, x16;                  \
        adds    x6, x6, x4;                     \
        adcs    x7, x7, x5;                     \
        adcs    x8, x8, xzr;                    \
        adc     x9, x9, xzr;                    \
        umull   x12, w10, w10;                  \
        lsr     x5, x10, #32;                   \
        umull   x13, w5, w5;                    \
        umull   x5, w10, w5;                    \
        adds    x12, x12, x5, lsl #33;          \
        lsr     x5, x5, #31;                    \
        adc     x13, x13, x5;                   \
        umull   x15, w11, w11;                  \
        lsr     x5, x11, #32;                   \
        umull   x14, w5, w5;                    \
        umull   x5, w11, w5;                    \
        mul     x4, x10, x11;                   \
        umulh   x16, x10, x11;                  \
        adds    x15, x15, x5, lsl #33;          \
        lsr     x5, x5, #31;                    \
        adc     x14, x14, x5;                   \
        adds    x4, x4, x4;                     \
        adcs    x16, x16, x16;                  \
        adc     x14, x14, xzr;                  \
        adds    x13, x13, x4;                   \
        adcs    x15, x15, x16;                  \
        adc     x14, x14, xzr;                  \
        adds    x4, x2, x6;                     \
        adcs    x5, x3, x7;                     \
        adcs    x6, x6, x8;                     \
        adcs    x7, x7, x9;                     \
        csetm   x16, lo;                        \
        subs    x4, x4, x12;                    \
        sbcs    x5, x5, x13;                    \
        sbcs    x6, x6, x15;                    \
        sbcs    x7, x7, x14;                    \
        adcs    x8, x8, x16;                    \
        adc     x9, x9, x16;                    \
        mov     x16, #977;                      \
        mul     x10, pconst, x6;                \
        umulh   x13, pconst, x6;                \
        and     x6, x7, #0xffffffff;            \
        lsr     x7, x7, #32;                    \
        mul     x11, x16, x6;                   \
        madd    x6, x16, x7, x6;                \
        adds    x11, x11, x6, lsl #32;          \
        lsr     x6, x6, #32;                    \
        adc     x14, x7, x6;                    \
        mul     x12, pconst, x8;                \
        umulh   x8, pconst, x8;                 \
        and     x6, x9, #0xffffffff;            \
        lsr     x7, x9, #32;                    \
        mul     x9, x16, x6;                    \
        madd    x6, x16, x7, x6;                \
        adds    x9, x9, x6, lsl #32;            \
        lsr     x6, x6, #32;                    \
        adc     x15, x7, x6;                    \
        adds    x2, x2, x10;                    \
        adcs    x3, x3, x11;                    \
        adcs    x4, x4, x12;                    \
        adcs    x5, x5, x9;                     \
        cset    x6, hs;                         \
        adds    x3, x3, x13;                    \
        adcs    x4, x4, x14;                    \
        adcs    x5, x5, x8;                     \
        adc     x6, x6, x15;                    \
        stp     x2, x3, [P0];                   \
        stp     x4, x5, [P0+16];                \
        str     x6, [P0+32]

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

// Save registers and make room on stack for temporary variables

        sub     sp, sp, NSPACE+16
        stp     x19, x20, [sp, NSPACE]

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

        ldp     x19, x20, [sp, NSPACE]
        add     sp, sp, NSPACE+16
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
