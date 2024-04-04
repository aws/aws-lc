// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point doubling on NIST curve P-384 in Montgomery-Jacobian coordinates
//
//    extern void p384_montjdouble
//      (uint64_t p3[static 18],uint64_t p1[static 18]);
//
// Does p3 := 2 * p1 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^384 * x) mod p_384.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
//
// Standard ARM ABI: X0 = p3, X1 = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p384_montjdouble)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p384_montjdouble)
        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 48

// Stable homes for input arguments during main code sequence

#define input_z x25
#define input_x x26

// Pointer-offset pairs for inputs and outputs

#define x_1 input_x, #0
#define y_1 input_x, #NUMSIZE
#define z_1 input_x, #(2*NUMSIZE)

#define x_3 input_z, #0
#define y_3 input_z, #NUMSIZE
#define z_3 input_z, #(2*NUMSIZE)

// Pointer-offset pairs for temporaries, with some aliasing
// NSPACE is the total stack needed for these temporaries

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

#define NSPACE #(NUMSIZE*7)

// Corresponds exactly to bignum_montmul_p384

#define montmul_p384(P0,P1,P2)                  \
        ldp     x3, x4, [P1];                   \
        ldp     x5, x6, [P1+16];                \
        ldp     x7, x8, [P1+32];                \
        ldp     x9, x10, [P2];                  \
        ldp     x11, x12, [P2+16];              \
        ldp     x13, x14, [P2+32];              \
        mul     x15, x3, x9;                    \
        mul     x21, x4, x10;                   \
        mul     x22, x5, x11;                   \
        umulh   x23, x3, x9;                    \
        umulh   x24, x4, x10;                   \
        umulh   x1, x5, x11;                    \
        adds    x23, x23, x21;                  \
        adcs    x24, x24, x22;                  \
        adc     x1, x1, xzr;                    \
        adds    x16, x23, x15;                  \
        adcs    x17, x24, x23;                  \
        adcs    x19, x1, x24;                   \
        adc     x20, x1, xzr;                   \
        adds    x17, x17, x15;                  \
        adcs    x19, x19, x23;                  \
        adcs    x20, x20, x24;                  \
        adc     x1, x1, xzr;                    \
        subs    x24, x3, x4;                    \
        cneg    x24, x24, lo;                   \
        csetm   x23, lo;                        \
        subs    x22, x10, x9;                   \
        cneg    x22, x22, lo;                   \
        mul     x21, x24, x22;                  \
        umulh   x22, x24, x22;                  \
        cinv    x23, x23, lo;                   \
        eor     x21, x21, x23;                  \
        eor     x22, x22, x23;                  \
        cmn     x23, #1;                        \
        adcs    x16, x16, x21;                  \
        adcs    x17, x17, x22;                  \
        adcs    x19, x19, x23;                  \
        adcs    x20, x20, x23;                  \
        adc     x1, x1, x23;                    \
        subs    x24, x3, x5;                    \
        cneg    x24, x24, lo;                   \
        csetm   x23, lo;                        \
        subs    x22, x11, x9;                   \
        cneg    x22, x22, lo;                   \
        mul     x21, x24, x22;                  \
        umulh   x22, x24, x22;                  \
        cinv    x23, x23, lo;                   \
        eor     x21, x21, x23;                  \
        eor     x22, x22, x23;                  \
        cmn     x23, #1;                        \
        adcs    x17, x17, x21;                  \
        adcs    x19, x19, x22;                  \
        adcs    x20, x20, x23;                  \
        adc     x1, x1, x23;                    \
        subs    x24, x4, x5;                    \
        cneg    x24, x24, lo;                   \
        csetm   x23, lo;                        \
        subs    x22, x11, x10;                  \
        cneg    x22, x22, lo;                   \
        mul     x21, x24, x22;                  \
        umulh   x22, x24, x22;                  \
        cinv    x23, x23, lo;                   \
        eor     x21, x21, x23;                  \
        eor     x22, x22, x23;                  \
        cmn     x23, #1;                        \
        adcs    x19, x19, x21;                  \
        adcs    x20, x20, x22;                  \
        adc     x1, x1, x23;                    \
        lsl     x23, x15, #32;                  \
        add     x15, x23, x15;                  \
        lsr     x23, x15, #32;                  \
        subs    x23, x23, x15;                  \
        sbc     x22, x15, xzr;                  \
        extr    x23, x22, x23, #32;             \
        lsr     x22, x22, #32;                  \
        adds    x22, x22, x15;                  \
        adc     x21, xzr, xzr;                  \
        subs    x16, x16, x23;                  \
        sbcs    x17, x17, x22;                  \
        sbcs    x19, x19, x21;                  \
        sbcs    x20, x20, xzr;                  \
        sbcs    x1, x1, xzr;                    \
        sbc     x15, x15, xzr;                  \
        lsl     x23, x16, #32;                  \
        add     x16, x23, x16;                  \
        lsr     x23, x16, #32;                  \
        subs    x23, x23, x16;                  \
        sbc     x22, x16, xzr;                  \
        extr    x23, x22, x23, #32;             \
        lsr     x22, x22, #32;                  \
        adds    x22, x22, x16;                  \
        adc     x21, xzr, xzr;                  \
        subs    x17, x17, x23;                  \
        sbcs    x19, x19, x22;                  \
        sbcs    x20, x20, x21;                  \
        sbcs    x1, x1, xzr;                    \
        sbcs    x15, x15, xzr;                  \
        sbc     x16, x16, xzr;                  \
        lsl     x23, x17, #32;                  \
        add     x17, x23, x17;                  \
        lsr     x23, x17, #32;                  \
        subs    x23, x23, x17;                  \
        sbc     x22, x17, xzr;                  \
        extr    x23, x22, x23, #32;             \
        lsr     x22, x22, #32;                  \
        adds    x22, x22, x17;                  \
        adc     x21, xzr, xzr;                  \
        subs    x19, x19, x23;                  \
        sbcs    x20, x20, x22;                  \
        sbcs    x1, x1, x21;                    \
        sbcs    x15, x15, xzr;                  \
        sbcs    x16, x16, xzr;                  \
        sbc     x17, x17, xzr;                  \
        stp     x19, x20, [P0];                 \
        stp     x1, x15, [P0+16];               \
        stp     x16, x17, [P0+32];              \
        mul     x15, x6, x12;                   \
        mul     x21, x7, x13;                   \
        mul     x22, x8, x14;                   \
        umulh   x23, x6, x12;                   \
        umulh   x24, x7, x13;                   \
        umulh   x1, x8, x14;                    \
        adds    x23, x23, x21;                  \
        adcs    x24, x24, x22;                  \
        adc     x1, x1, xzr;                    \
        adds    x16, x23, x15;                  \
        adcs    x17, x24, x23;                  \
        adcs    x19, x1, x24;                   \
        adc     x20, x1, xzr;                   \
        adds    x17, x17, x15;                  \
        adcs    x19, x19, x23;                  \
        adcs    x20, x20, x24;                  \
        adc     x1, x1, xzr;                    \
        subs    x24, x6, x7;                    \
        cneg    x24, x24, lo;                   \
        csetm   x23, lo;                        \
        subs    x22, x13, x12;                  \
        cneg    x22, x22, lo;                   \
        mul     x21, x24, x22;                  \
        umulh   x22, x24, x22;                  \
        cinv    x23, x23, lo;                   \
        eor     x21, x21, x23;                  \
        eor     x22, x22, x23;                  \
        cmn     x23, #1;                        \
        adcs    x16, x16, x21;                  \
        adcs    x17, x17, x22;                  \
        adcs    x19, x19, x23;                  \
        adcs    x20, x20, x23;                  \
        adc     x1, x1, x23;                    \
        subs    x24, x6, x8;                    \
        cneg    x24, x24, lo;                   \
        csetm   x23, lo;                        \
        subs    x22, x14, x12;                  \
        cneg    x22, x22, lo;                   \
        mul     x21, x24, x22;                  \
        umulh   x22, x24, x22;                  \
        cinv    x23, x23, lo;                   \
        eor     x21, x21, x23;                  \
        eor     x22, x22, x23;                  \
        cmn     x23, #1;                        \
        adcs    x17, x17, x21;                  \
        adcs    x19, x19, x22;                  \
        adcs    x20, x20, x23;                  \
        adc     x1, x1, x23;                    \
        subs    x24, x7, x8;                    \
        cneg    x24, x24, lo;                   \
        csetm   x23, lo;                        \
        subs    x22, x14, x13;                  \
        cneg    x22, x22, lo;                   \
        mul     x21, x24, x22;                  \
        umulh   x22, x24, x22;                  \
        cinv    x23, x23, lo;                   \
        eor     x21, x21, x23;                  \
        eor     x22, x22, x23;                  \
        cmn     x23, #1;                        \
        adcs    x19, x19, x21;                  \
        adcs    x20, x20, x22;                  \
        adc     x1, x1, x23;                    \
        subs    x6, x6, x3;                     \
        sbcs    x7, x7, x4;                     \
        sbcs    x8, x8, x5;                     \
        ngc     x3, xzr;                        \
        cmn     x3, #1;                         \
        eor     x6, x6, x3;                     \
        adcs    x6, x6, xzr;                    \
        eor     x7, x7, x3;                     \
        adcs    x7, x7, xzr;                    \
        eor     x8, x8, x3;                     \
        adc     x8, x8, xzr;                    \
        subs    x9, x9, x12;                    \
        sbcs    x10, x10, x13;                  \
        sbcs    x11, x11, x14;                  \
        ngc     x14, xzr;                       \
        cmn     x14, #1;                        \
        eor     x9, x9, x14;                    \
        adcs    x9, x9, xzr;                    \
        eor     x10, x10, x14;                  \
        adcs    x10, x10, xzr;                  \
        eor     x11, x11, x14;                  \
        adc     x11, x11, xzr;                  \
        eor     x14, x3, x14;                   \
        ldp     x21, x22, [P0];                 \
        adds    x15, x15, x21;                  \
        adcs    x16, x16, x22;                  \
        ldp     x21, x22, [P0+16];              \
        adcs    x17, x17, x21;                  \
        adcs    x19, x19, x22;                  \
        ldp     x21, x22, [P0+32];              \
        adcs    x20, x20, x21;                  \
        adcs    x1, x1, x22;                    \
        adc     x2, xzr, xzr;                   \
        stp     x15, x16, [P0];                 \
        stp     x17, x19, [P0+16];              \
        stp     x20, x1, [P0+32];               \
        mul     x15, x6, x9;                    \
        mul     x21, x7, x10;                   \
        mul     x22, x8, x11;                   \
        umulh   x23, x6, x9;                    \
        umulh   x24, x7, x10;                   \
        umulh   x1, x8, x11;                    \
        adds    x23, x23, x21;                  \
        adcs    x24, x24, x22;                  \
        adc     x1, x1, xzr;                    \
        adds    x16, x23, x15;                  \
        adcs    x17, x24, x23;                  \
        adcs    x19, x1, x24;                   \
        adc     x20, x1, xzr;                   \
        adds    x17, x17, x15;                  \
        adcs    x19, x19, x23;                  \
        adcs    x20, x20, x24;                  \
        adc     x1, x1, xzr;                    \
        subs    x24, x6, x7;                    \
        cneg    x24, x24, lo;                   \
        csetm   x23, lo;                        \
        subs    x22, x10, x9;                   \
        cneg    x22, x22, lo;                   \
        mul     x21, x24, x22;                  \
        umulh   x22, x24, x22;                  \
        cinv    x23, x23, lo;                   \
        eor     x21, x21, x23;                  \
        eor     x22, x22, x23;                  \
        cmn     x23, #1;                        \
        adcs    x16, x16, x21;                  \
        adcs    x17, x17, x22;                  \
        adcs    x19, x19, x23;                  \
        adcs    x20, x20, x23;                  \
        adc     x1, x1, x23;                    \
        subs    x24, x6, x8;                    \
        cneg    x24, x24, lo;                   \
        csetm   x23, lo;                        \
        subs    x22, x11, x9;                   \
        cneg    x22, x22, lo;                   \
        mul     x21, x24, x22;                  \
        umulh   x22, x24, x22;                  \
        cinv    x23, x23, lo;                   \
        eor     x21, x21, x23;                  \
        eor     x22, x22, x23;                  \
        cmn     x23, #1;                        \
        adcs    x17, x17, x21;                  \
        adcs    x19, x19, x22;                  \
        adcs    x20, x20, x23;                  \
        adc     x1, x1, x23;                    \
        subs    x24, x7, x8;                    \
        cneg    x24, x24, lo;                   \
        csetm   x23, lo;                        \
        subs    x22, x11, x10;                  \
        cneg    x22, x22, lo;                   \
        mul     x21, x24, x22;                  \
        umulh   x22, x24, x22;                  \
        cinv    x23, x23, lo;                   \
        eor     x21, x21, x23;                  \
        eor     x22, x22, x23;                  \
        cmn     x23, #1;                        \
        adcs    x19, x19, x21;                  \
        adcs    x20, x20, x22;                  \
        adc     x1, x1, x23;                    \
        ldp     x3, x4, [P0];                   \
        ldp     x5, x6, [P0+16];                \
        ldp     x7, x8, [P0+32];                \
        cmn     x14, #1;                        \
        eor     x15, x15, x14;                  \
        adcs    x15, x15, x3;                   \
        eor     x16, x16, x14;                  \
        adcs    x16, x16, x4;                   \
        eor     x17, x17, x14;                  \
        adcs    x17, x17, x5;                   \
        eor     x19, x19, x14;                  \
        adcs    x19, x19, x6;                   \
        eor     x20, x20, x14;                  \
        adcs    x20, x20, x7;                   \
        eor     x1, x1, x14;                    \
        adcs    x1, x1, x8;                     \
        adcs    x9, x14, x2;                    \
        adcs    x10, x14, xzr;                  \
        adcs    x11, x14, xzr;                  \
        adc     x12, x14, xzr;                  \
        adds    x19, x19, x3;                   \
        adcs    x20, x20, x4;                   \
        adcs    x1, x1, x5;                     \
        adcs    x9, x9, x6;                     \
        adcs    x10, x10, x7;                   \
        adcs    x11, x11, x8;                   \
        adc     x12, x12, x2;                   \
        lsl     x23, x15, #32;                  \
        add     x15, x23, x15;                  \
        lsr     x23, x15, #32;                  \
        subs    x23, x23, x15;                  \
        sbc     x22, x15, xzr;                  \
        extr    x23, x22, x23, #32;             \
        lsr     x22, x22, #32;                  \
        adds    x22, x22, x15;                  \
        adc     x21, xzr, xzr;                  \
        subs    x16, x16, x23;                  \
        sbcs    x17, x17, x22;                  \
        sbcs    x19, x19, x21;                  \
        sbcs    x20, x20, xzr;                  \
        sbcs    x1, x1, xzr;                    \
        sbc     x15, x15, xzr;                  \
        lsl     x23, x16, #32;                  \
        add     x16, x23, x16;                  \
        lsr     x23, x16, #32;                  \
        subs    x23, x23, x16;                  \
        sbc     x22, x16, xzr;                  \
        extr    x23, x22, x23, #32;             \
        lsr     x22, x22, #32;                  \
        adds    x22, x22, x16;                  \
        adc     x21, xzr, xzr;                  \
        subs    x17, x17, x23;                  \
        sbcs    x19, x19, x22;                  \
        sbcs    x20, x20, x21;                  \
        sbcs    x1, x1, xzr;                    \
        sbcs    x15, x15, xzr;                  \
        sbc     x16, x16, xzr;                  \
        lsl     x23, x17, #32;                  \
        add     x17, x23, x17;                  \
        lsr     x23, x17, #32;                  \
        subs    x23, x23, x17;                  \
        sbc     x22, x17, xzr;                  \
        extr    x23, x22, x23, #32;             \
        lsr     x22, x22, #32;                  \
        adds    x22, x22, x17;                  \
        adc     x21, xzr, xzr;                  \
        subs    x19, x19, x23;                  \
        sbcs    x20, x20, x22;                  \
        sbcs    x1, x1, x21;                    \
        sbcs    x15, x15, xzr;                  \
        sbcs    x16, x16, xzr;                  \
        sbc     x17, x17, xzr;                  \
        adds    x9, x9, x15;                    \
        adcs    x10, x10, x16;                  \
        adcs    x11, x11, x17;                  \
        adc     x12, x12, xzr;                  \
        add     x22, x12, #1;                   \
        lsl     x21, x22, #32;                  \
        subs    x24, x22, x21;                  \
        sbc     x21, x21, xzr;                  \
        adds    x19, x19, x24;                  \
        adcs    x20, x20, x21;                  \
        adcs    x1, x1, x22;                    \
        adcs    x9, x9, xzr;                    \
        adcs    x10, x10, xzr;                  \
        adcs    x11, x11, xzr;                  \
        csetm   x22, lo;                        \
        mov     x23, #4294967295;               \
        and     x23, x23, x22;                  \
        adds    x19, x19, x23;                  \
        eor     x23, x23, x22;                  \
        adcs    x20, x20, x23;                  \
        mov     x23, #-2;                       \
        and     x23, x23, x22;                  \
        adcs    x1, x1, x23;                    \
        adcs    x9, x9, x22;                    \
        adcs    x10, x10, x22;                  \
        adc     x11, x11, x22;                  \
        stp     x19, x20, [P0];                 \
        stp     x1, x9, [P0+16];                \
        stp     x10, x11, [P0+32]

// Corresponds exactly to bignum_montsqr_p384

#define montsqr_p384(P0,P1)                     \
        ldp     x2, x3, [P1];                   \
        ldp     x4, x5, [P1+16];                \
        ldp     x6, x7, [P1+32];                \
        mul     x14, x2, x3;                    \
        mul     x15, x2, x4;                    \
        mul     x16, x3, x4;                    \
        mul     x8, x2, x2;                     \
        mul     x10, x3, x3;                    \
        mul     x12, x4, x4;                    \
        umulh   x17, x2, x3;                    \
        adds    x15, x15, x17;                  \
        umulh   x17, x2, x4;                    \
        adcs    x16, x16, x17;                  \
        umulh   x17, x3, x4;                    \
        adcs    x17, x17, xzr;                  \
        umulh   x9, x2, x2;                     \
        umulh   x11, x3, x3;                    \
        umulh   x13, x4, x4;                    \
        adds    x14, x14, x14;                  \
        adcs    x15, x15, x15;                  \
        adcs    x16, x16, x16;                  \
        adcs    x17, x17, x17;                  \
        adc     x13, x13, xzr;                  \
        adds    x9, x9, x14;                    \
        adcs    x10, x10, x15;                  \
        adcs    x11, x11, x16;                  \
        adcs    x12, x12, x17;                  \
        adc     x13, x13, xzr;                  \
        lsl     x16, x8, #32;                   \
        add     x8, x16, x8;                    \
        lsr     x16, x8, #32;                   \
        subs    x16, x16, x8;                   \
        sbc     x15, x8, xzr;                   \
        extr    x16, x15, x16, #32;             \
        lsr     x15, x15, #32;                  \
        adds    x15, x15, x8;                   \
        adc     x14, xzr, xzr;                  \
        subs    x9, x9, x16;                    \
        sbcs    x10, x10, x15;                  \
        sbcs    x11, x11, x14;                  \
        sbcs    x12, x12, xzr;                  \
        sbcs    x13, x13, xzr;                  \
        sbc     x8, x8, xzr;                    \
        lsl     x16, x9, #32;                   \
        add     x9, x16, x9;                    \
        lsr     x16, x9, #32;                   \
        subs    x16, x16, x9;                   \
        sbc     x15, x9, xzr;                   \
        extr    x16, x15, x16, #32;             \
        lsr     x15, x15, #32;                  \
        adds    x15, x15, x9;                   \
        adc     x14, xzr, xzr;                  \
        subs    x10, x10, x16;                  \
        sbcs    x11, x11, x15;                  \
        sbcs    x12, x12, x14;                  \
        sbcs    x13, x13, xzr;                  \
        sbcs    x8, x8, xzr;                    \
        sbc     x9, x9, xzr;                    \
        lsl     x16, x10, #32;                  \
        add     x10, x16, x10;                  \
        lsr     x16, x10, #32;                  \
        subs    x16, x16, x10;                  \
        sbc     x15, x10, xzr;                  \
        extr    x16, x15, x16, #32;             \
        lsr     x15, x15, #32;                  \
        adds    x15, x15, x10;                  \
        adc     x14, xzr, xzr;                  \
        subs    x11, x11, x16;                  \
        sbcs    x12, x12, x15;                  \
        sbcs    x13, x13, x14;                  \
        sbcs    x8, x8, xzr;                    \
        sbcs    x9, x9, xzr;                    \
        sbc     x10, x10, xzr;                  \
        stp     x11, x12, [P0];                 \
        stp     x13, x8, [P0+16];               \
        stp     x9, x10, [P0+32];               \
        mul     x8, x2, x5;                     \
        mul     x14, x3, x6;                    \
        mul     x15, x4, x7;                    \
        umulh   x16, x2, x5;                    \
        umulh   x17, x3, x6;                    \
        umulh   x1, x4, x7;                     \
        adds    x16, x16, x14;                  \
        adcs    x17, x17, x15;                  \
        adc     x1, x1, xzr;                    \
        adds    x9, x16, x8;                    \
        adcs    x10, x17, x16;                  \
        adcs    x11, x1, x17;                   \
        adc     x12, x1, xzr;                   \
        adds    x10, x10, x8;                   \
        adcs    x11, x11, x16;                  \
        adcs    x12, x12, x17;                  \
        adc     x13, x1, xzr;                   \
        subs    x17, x2, x3;                    \
        cneg    x17, x17, lo;                   \
        csetm   x14, lo;                        \
        subs    x15, x6, x5;                    \
        cneg    x15, x15, lo;                   \
        mul     x16, x17, x15;                  \
        umulh   x15, x17, x15;                  \
        cinv    x14, x14, lo;                   \
        eor     x16, x16, x14;                  \
        eor     x15, x15, x14;                  \
        cmn     x14, #1;                        \
        adcs    x9, x9, x16;                    \
        adcs    x10, x10, x15;                  \
        adcs    x11, x11, x14;                  \
        adcs    x12, x12, x14;                  \
        adc     x13, x13, x14;                  \
        subs    x17, x2, x4;                    \
        cneg    x17, x17, lo;                   \
        csetm   x14, lo;                        \
        subs    x15, x7, x5;                    \
        cneg    x15, x15, lo;                   \
        mul     x16, x17, x15;                  \
        umulh   x15, x17, x15;                  \
        cinv    x14, x14, lo;                   \
        eor     x16, x16, x14;                  \
        eor     x15, x15, x14;                  \
        cmn     x14, #1;                        \
        adcs    x10, x10, x16;                  \
        adcs    x11, x11, x15;                  \
        adcs    x12, x12, x14;                  \
        adc     x13, x13, x14;                  \
        subs    x17, x3, x4;                    \
        cneg    x17, x17, lo;                   \
        csetm   x14, lo;                        \
        subs    x15, x7, x6;                    \
        cneg    x15, x15, lo;                   \
        mul     x16, x17, x15;                  \
        umulh   x15, x17, x15;                  \
        cinv    x14, x14, lo;                   \
        eor     x16, x16, x14;                  \
        eor     x15, x15, x14;                  \
        cmn     x14, #1;                        \
        adcs    x11, x11, x16;                  \
        adcs    x12, x12, x15;                  \
        adc     x13, x13, x14;                  \
        adds    x8, x8, x8;                     \
        adcs    x9, x9, x9;                     \
        adcs    x10, x10, x10;                  \
        adcs    x11, x11, x11;                  \
        adcs    x12, x12, x12;                  \
        adcs    x13, x13, x13;                  \
        adc     x17, xzr, xzr;                  \
        ldp     x2, x3, [P0];                   \
        adds    x8, x8, x2;                     \
        adcs    x9, x9, x3;                     \
        ldp     x2, x3, [P0+16];                \
        adcs    x10, x10, x2;                   \
        adcs    x11, x11, x3;                   \
        ldp     x2, x3, [P0+32];                \
        adcs    x12, x12, x2;                   \
        adcs    x13, x13, x3;                   \
        adc     x17, x17, xzr;                  \
        lsl     x4, x8, #32;                    \
        add     x8, x4, x8;                     \
        lsr     x4, x8, #32;                    \
        subs    x4, x4, x8;                     \
        sbc     x3, x8, xzr;                    \
        extr    x4, x3, x4, #32;                \
        lsr     x3, x3, #32;                    \
        adds    x3, x3, x8;                     \
        adc     x2, xzr, xzr;                   \
        subs    x9, x9, x4;                     \
        sbcs    x10, x10, x3;                   \
        sbcs    x11, x11, x2;                   \
        sbcs    x12, x12, xzr;                  \
        sbcs    x13, x13, xzr;                  \
        sbc     x8, x8, xzr;                    \
        lsl     x4, x9, #32;                    \
        add     x9, x4, x9;                     \
        lsr     x4, x9, #32;                    \
        subs    x4, x4, x9;                     \
        sbc     x3, x9, xzr;                    \
        extr    x4, x3, x4, #32;                \
        lsr     x3, x3, #32;                    \
        adds    x3, x3, x9;                     \
        adc     x2, xzr, xzr;                   \
        subs    x10, x10, x4;                   \
        sbcs    x11, x11, x3;                   \
        sbcs    x12, x12, x2;                   \
        sbcs    x13, x13, xzr;                  \
        sbcs    x8, x8, xzr;                    \
        sbc     x9, x9, xzr;                    \
        lsl     x4, x10, #32;                   \
        add     x10, x4, x10;                   \
        lsr     x4, x10, #32;                   \
        subs    x4, x4, x10;                    \
        sbc     x3, x10, xzr;                   \
        extr    x4, x3, x4, #32;                \
        lsr     x3, x3, #32;                    \
        adds    x3, x3, x10;                    \
        adc     x2, xzr, xzr;                   \
        subs    x11, x11, x4;                   \
        sbcs    x12, x12, x3;                   \
        sbcs    x13, x13, x2;                   \
        sbcs    x8, x8, xzr;                    \
        sbcs    x9, x9, xzr;                    \
        sbc     x10, x10, xzr;                  \
        adds    x17, x17, x8;                   \
        adcs    x8, x9, xzr;                    \
        adcs    x9, x10, xzr;                   \
        adcs    x10, xzr, xzr;                  \
        mul     x1, x5, x5;                     \
        adds    x11, x11, x1;                   \
        mul     x14, x6, x6;                    \
        mul     x15, x7, x7;                    \
        umulh   x1, x5, x5;                     \
        adcs    x12, x12, x1;                   \
        umulh   x1, x6, x6;                     \
        adcs    x13, x13, x14;                  \
        adcs    x17, x17, x1;                   \
        umulh   x1, x7, x7;                     \
        adcs    x8, x8, x15;                    \
        adcs    x9, x9, x1;                     \
        adc     x10, x10, xzr;                  \
        mul     x1, x5, x6;                     \
        mul     x14, x5, x7;                    \
        mul     x15, x6, x7;                    \
        umulh   x16, x5, x6;                    \
        adds    x14, x14, x16;                  \
        umulh   x16, x5, x7;                    \
        adcs    x15, x15, x16;                  \
        umulh   x16, x6, x7;                    \
        adc     x16, x16, xzr;                  \
        adds    x1, x1, x1;                     \
        adcs    x14, x14, x14;                  \
        adcs    x15, x15, x15;                  \
        adcs    x16, x16, x16;                  \
        adc     x5, xzr, xzr;                   \
        adds    x12, x12, x1;                   \
        adcs    x13, x13, x14;                  \
        adcs    x17, x17, x15;                  \
        adcs    x8, x8, x16;                    \
        adcs    x9, x9, x5;                     \
        adc     x10, x10, xzr;                  \
        mov     x1, #-4294967295;               \
        mov     x14, #4294967295;               \
        mov     x15, #1;                        \
        cmn     x11, x1;                        \
        adcs    xzr, x12, x14;                  \
        adcs    xzr, x13, x15;                  \
        adcs    xzr, x17, xzr;                  \
        adcs    xzr, x8, xzr;                   \
        adcs    xzr, x9, xzr;                   \
        adc     x10, x10, xzr;                  \
        neg     x10, x10;                       \
        and     x1, x1, x10;                    \
        adds    x11, x11, x1;                   \
        and     x14, x14, x10;                  \
        adcs    x12, x12, x14;                  \
        and     x15, x15, x10;                  \
        adcs    x13, x13, x15;                  \
        adcs    x17, x17, xzr;                  \
        adcs    x8, x8, xzr;                    \
        adc     x9, x9, xzr;                    \
        stp     x11, x12, [P0];                 \
        stp     x13, x17, [P0+16];              \
        stp     x8, x9, [P0+32]

// Corresponds exactly to bignum_sub_p384

#define sub_p384(P0,P1,P2)                      \
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
        csetm   x3, lo;                         \
        mov     x4, #4294967295;                \
        and     x4, x4, x3;                     \
        adds    x5, x5, x4;                     \
        eor     x4, x4, x3;                     \
        adcs    x6, x6, x4;                     \
        mov     x4, #-2;                        \
        and     x4, x4, x3;                     \
        adcs    x7, x7, x4;                     \
        adcs    x8, x8, x3;                     \
        adcs    x9, x9, x3;                     \
        adc     x10, x10, x3;                   \
        stp     x5, x6, [P0];                   \
        stp     x7, x8, [P0+16];                \
        stp     x9, x10, [P0+32]

// Corresponds exactly to bignum_add_p384

#define add_p384(P0,P1,P2)                      \
        ldp     x5, x6, [P1];                   \
        ldp     x4, x3, [P2];                   \
        adds    x5, x5, x4;                     \
        adcs    x6, x6, x3;                     \
        ldp     x7, x8, [P1+16];                \
        ldp     x4, x3, [P2+16];                \
        adcs    x7, x7, x4;                     \
        adcs    x8, x8, x3;                     \
        ldp     x9, x10, [P1+32];               \
        ldp     x4, x3, [P2+32];                \
        adcs    x9, x9, x4;                     \
        adcs    x10, x10, x3;                   \
        adc     x3, xzr, xzr;                   \
        mov     x4, #0xffffffff;                \
        cmp     x5, x4;                         \
        mov     x4, #0xffffffff00000000;        \
        sbcs    xzr, x6, x4;                    \
        mov     x4, #0xfffffffffffffffe;        \
        sbcs    xzr, x7, x4;                    \
        adcs    xzr, x8, xzr;                   \
        adcs    xzr, x9, xzr;                   \
        adcs    xzr, x10, xzr;                  \
        adcs    x3, x3, xzr;                    \
        csetm   x3, ne;                         \
        mov     x4, #0xffffffff;                \
        and     x4, x4, x3;                     \
        subs    x5, x5, x4;                     \
        eor     x4, x4, x3;                     \
        sbcs    x6, x6, x4;                     \
        mov     x4, #0xfffffffffffffffe;        \
        and     x4, x4, x3;                     \
        sbcs    x7, x7, x4;                     \
        sbcs    x8, x8, x3;                     \
        sbcs    x9, x9, x3;                     \
        sbc     x10, x10, x3;                   \
        stp     x5, x6, [P0];                   \
        stp     x7, x8, [P0+16];                \
        stp     x9, x10, [P0+32]

// P0 = 4 * P1 - P2

#define cmsub41_p384(P0,P1,P2)                  \
        ldp     x1, x2, [P1];                   \
        ldp     x3, x4, [P1+16];                \
        ldp     x5, x6, [P1+32];                \
        lsl     x0, x1, #2;                     \
        ldp     x7, x8, [P2];                   \
        subs    x0, x0, x7;                     \
        extr    x1, x2, x1, #62;                \
        sbcs    x1, x1, x8;                     \
        ldp     x7, x8, [P2+16];                \
        extr    x2, x3, x2, #62;                \
        sbcs    x2, x2, x7;                     \
        extr    x3, x4, x3, #62;                \
        sbcs    x3, x3, x8;                     \
        extr    x4, x5, x4, #62;                \
        ldp     x7, x8, [P2+32];                \
        sbcs    x4, x4, x7;                     \
        extr    x5, x6, x5, #62;                \
        sbcs    x5, x5, x8;                     \
        lsr     x6, x6, #62;                    \
        adc     x6, x6, xzr;                    \
        lsl     x7, x6, #32;                    \
        subs    x8, x6, x7;                     \
        sbc     x7, x7, xzr;                    \
        adds    x0, x0, x8;                     \
        adcs    x1, x1, x7;                     \
        adcs    x2, x2, x6;                     \
        adcs    x3, x3, xzr;                    \
        adcs    x4, x4, xzr;                    \
        adcs    x5, x5, xzr;                    \
        csetm   x8, cc;                         \
        mov     x9, #0xffffffff;                \
        and     x9, x9, x8;                     \
        adds    x0, x0, x9;                     \
        eor     x9, x9, x8;                     \
        adcs    x1, x1, x9;                     \
        mov     x9, #0xfffffffffffffffe;        \
        and     x9, x9, x8;                     \
        adcs    x2, x2, x9;                     \
        adcs    x3, x3, x8;                     \
        adcs    x4, x4, x8;                     \
        adc     x5, x5, x8;                     \
        stp     x0, x1, [P0];                   \
        stp     x2, x3, [P0+16];                \
        stp     x4, x5, [P0+32]

// P0 = C * P1 - D * P2

#define cmsub_p384(P0,C,P1,D,P2)                \
        ldp     x0, x1, [P2];                   \
        mov     x6, #0x00000000ffffffff;        \
        subs    x6, x6, x0;                     \
        mov     x7, #0xffffffff00000000;        \
        sbcs    x7, x7, x1;                     \
        ldp     x0, x1, [P2+16];                \
        mov     x8, #0xfffffffffffffffe;        \
        sbcs    x8, x8, x0;                     \
        mov     x13, #0xffffffffffffffff;       \
        sbcs    x9, x13, x1;                    \
        ldp     x0, x1, [P2+32];                \
        sbcs    x10, x13, x0;                   \
        sbc     x11, x13, x1;                   \
        mov     x12, D;                         \
        mul     x0, x12, x6;                    \
        mul     x1, x12, x7;                    \
        mul     x2, x12, x8;                    \
        mul     x3, x12, x9;                    \
        mul     x4, x12, x10;                   \
        mul     x5, x12, x11;                   \
        umulh   x6, x12, x6;                    \
        umulh   x7, x12, x7;                    \
        umulh   x8, x12, x8;                    \
        umulh   x9, x12, x9;                    \
        umulh   x10, x12, x10;                  \
        umulh   x12, x12, x11;                  \
        adds    x1, x1, x6;                     \
        adcs    x2, x2, x7;                     \
        adcs    x3, x3, x8;                     \
        adcs    x4, x4, x9;                     \
        adcs    x5, x5, x10;                    \
        mov     x6, #1;                         \
        adc     x6, x12, x6;                    \
        ldp     x8, x9, [P1];                   \
        ldp     x10, x11, [P1+16];              \
        ldp     x12, x13, [P1+32];              \
        mov     x14, C;                         \
        mul     x15, x14, x8;                   \
        umulh   x8, x14, x8;                    \
        adds    x0, x0, x15;                    \
        mul     x15, x14, x9;                   \
        umulh   x9, x14, x9;                    \
        adcs    x1, x1, x15;                    \
        mul     x15, x14, x10;                  \
        umulh   x10, x14, x10;                  \
        adcs    x2, x2, x15;                    \
        mul     x15, x14, x11;                  \
        umulh   x11, x14, x11;                  \
        adcs    x3, x3, x15;                    \
        mul     x15, x14, x12;                  \
        umulh   x12, x14, x12;                  \
        adcs    x4, x4, x15;                    \
        mul     x15, x14, x13;                  \
        umulh   x13, x14, x13;                  \
        adcs    x5, x5, x15;                    \
        adc     x6, x6, xzr;                    \
        adds    x1, x1, x8;                     \
        adcs    x2, x2, x9;                     \
        adcs    x3, x3, x10;                    \
        adcs    x4, x4, x11;                    \
        adcs    x5, x5, x12;                    \
        adcs    x6, x6, x13;                    \
        lsl     x7, x6, #32;                    \
        subs    x8, x6, x7;                     \
        sbc     x7, x7, xzr;                    \
        adds    x0, x0, x8;                     \
        adcs    x1, x1, x7;                     \
        adcs    x2, x2, x6;                     \
        adcs    x3, x3, xzr;                    \
        adcs    x4, x4, xzr;                    \
        adcs    x5, x5, xzr;                    \
        csetm   x6, cc;                         \
        mov     x7, #0xffffffff;                \
        and     x7, x7, x6;                     \
        adds    x0, x0, x7;                     \
        eor     x7, x7, x6;                     \
        adcs    x1, x1, x7;                     \
        mov     x7, #0xfffffffffffffffe;        \
        and     x7, x7, x6;                     \
        adcs    x2, x2, x7;                     \
        adcs    x3, x3, x6;                     \
        adcs    x4, x4, x6;                     \
        adc     x5, x5, x6;                     \
        stp     x0, x1, [P0];                   \
        stp     x2, x3, [P0+16];                \
        stp     x4, x5, [P0+32]

// A weak version of add that only guarantees sum in 6 digits

#define weakadd_p384(P0,P1,P2)                  \
        ldp     x5, x6, [P1];                   \
        ldp     x4, x3, [P2];                   \
        adds    x5, x5, x4;                     \
        adcs    x6, x6, x3;                     \
        ldp     x7, x8, [P1+16];                \
        ldp     x4, x3, [P2+16];                \
        adcs    x7, x7, x4;                     \
        adcs    x8, x8, x3;                     \
        ldp     x9, x10, [P1+32];               \
        ldp     x4, x3, [P2+32];                \
        adcs    x9, x9, x4;                     \
        adcs    x10, x10, x3;                   \
        csetm   x3, cs;                         \
        mov     x4, #0xffffffff;                \
        and     x4, x4, x3;                     \
        subs    x5, x5, x4;                     \
        eor     x4, x4, x3;                     \
        sbcs    x6, x6, x4;                     \
        mov     x4, #0xfffffffffffffffe;        \
        and     x4, x4, x3;                     \
        sbcs    x7, x7, x4;                     \
        sbcs    x8, x8, x3;                     \
        sbcs    x9, x9, x3;                     \
        sbc     x10, x10, x3;                   \
        stp     x5, x6, [P0];                   \
        stp     x7, x8, [P0+16];                \
        stp     x9, x10, [P0+32]

// P0 = 3 * P1 - 8 * P2

#define cmsub38_p384(P0,P1,P2)                  \
        ldp     x0, x1, [P2];                   \
        mov     x6, #0x00000000ffffffff;        \
        subs    x6, x6, x0;                     \
        mov     x7, #0xffffffff00000000;        \
        sbcs    x7, x7, x1;                     \
        ldp     x0, x1, [P2+16];                \
        mov     x8, #0xfffffffffffffffe;        \
        sbcs    x8, x8, x0;                     \
        mov     x13, #0xffffffffffffffff;       \
        sbcs    x9, x13, x1;                    \
        ldp     x0, x1, [P2+32];                \
        sbcs    x10, x13, x0;                   \
        sbc     x11, x13, x1;                   \
        lsl     x0, x6, #3;                     \
        extr    x1, x7, x6, #61;                \
        extr    x2, x8, x7, #61;                \
        extr    x3, x9, x8, #61;                \
        extr    x4, x10, x9, #61;               \
        extr    x5, x11, x10, #61;              \
        lsr     x6, x11, #61;                   \
        add     x6, x6, #1;                     \
        ldp     x8, x9, [P1];                   \
        ldp     x10, x11, [P1+16];              \
        ldp     x12, x13, [P1+32];              \
        mov     x14, 3;                         \
        mul     x15, x14, x8;                   \
        umulh   x8, x14, x8;                    \
        adds    x0, x0, x15;                    \
        mul     x15, x14, x9;                   \
        umulh   x9, x14, x9;                    \
        adcs    x1, x1, x15;                    \
        mul     x15, x14, x10;                  \
        umulh   x10, x14, x10;                  \
        adcs    x2, x2, x15;                    \
        mul     x15, x14, x11;                  \
        umulh   x11, x14, x11;                  \
        adcs    x3, x3, x15;                    \
        mul     x15, x14, x12;                  \
        umulh   x12, x14, x12;                  \
        adcs    x4, x4, x15;                    \
        mul     x15, x14, x13;                  \
        umulh   x13, x14, x13;                  \
        adcs    x5, x5, x15;                    \
        adc     x6, x6, xzr;                    \
        adds    x1, x1, x8;                     \
        adcs    x2, x2, x9;                     \
        adcs    x3, x3, x10;                    \
        adcs    x4, x4, x11;                    \
        adcs    x5, x5, x12;                    \
        adcs    x6, x6, x13;                    \
        lsl     x7, x6, #32;                    \
        subs    x8, x6, x7;                     \
        sbc     x7, x7, xzr;                    \
        adds    x0, x0, x8;                     \
        adcs    x1, x1, x7;                     \
        adcs    x2, x2, x6;                     \
        adcs    x3, x3, xzr;                    \
        adcs    x4, x4, xzr;                    \
        adcs    x5, x5, xzr;                    \
        csetm   x6, cc;                         \
        mov     x7, #0xffffffff;                \
        and     x7, x7, x6;                     \
        adds    x0, x0, x7;                     \
        eor     x7, x7, x6;                     \
        adcs    x1, x1, x7;                     \
        mov     x7, #0xfffffffffffffffe;        \
        and     x7, x7, x6;                     \
        adcs    x2, x2, x7;                     \
        adcs    x3, x3, x6;                     \
        adcs    x4, x4, x6;                     \
        adc     x5, x5, x6;                     \
        stp     x0, x1, [P0];                   \
        stp     x2, x3, [P0+16];                \
        stp     x4, x5, [P0+32]

S2N_BN_SYMBOL(p384_montjdouble):

// Save regs and make room on stack for temporary variables

        sub     sp, sp, NSPACE+64
        stp     x19, x20, [sp, NSPACE]
        stp     x21, x22, [sp, NSPACE+16]
        stp     x23, x24, [sp, NSPACE+32]
        stp     x25, x26, [sp, NSPACE+48]

// Move the input arguments to stable places

        mov     input_z, x0
        mov     input_x, x1

// Main code, just a sequence of basic field operations

// z2 = z^2
// y2 = y^2

        montsqr_p384(z2,z_1)
        montsqr_p384(y2,y_1)

// x2p = x^2 - z^4 = (x + z^2) * (x - z^2)

        weakadd_p384(t1,x_1,z2)
        sub_p384(t2,x_1,z2)
        montmul_p384(x2p,t1,t2)

// t1 = y + z
// x4p = x2p^2
// xy2 = x * y^2

        add_p384(t1,y_1,z_1)
        montsqr_p384(x4p,x2p)
        montmul_p384(xy2,x_1,y2)

// t2 = (y + z)^2

        montsqr_p384(t2,t1)

// d = 12 * xy2 - 9 * x4p
// t1 = y^2 + 2 * y * z

        cmsub_p384(d,12,xy2,9,x4p)
        sub_p384(t1,t2,z2)

// y4 = y^4

        montsqr_p384(y4,y2)

// z_3' = 2 * y * z
// dx2 = d * x2p

        sub_p384(z_3,t1,y2)
        montmul_p384(dx2,d,x2p)

// x' = 4 * xy2 - d

        cmsub41_p384(x_3,xy2,d)

// y' = 3 * dx2 - 8 * y4

        cmsub38_p384(y_3,dx2,y4)

// Restore stack and registers

        ldp     x19, x20, [sp, NSPACE]
        ldp     x21, x22, [sp, NSPACE+16]
        ldp     x23, x24, [sp, NSPACE+32]
        ldp     x25, x26, [sp, NSPACE+48]
        add     sp, sp, NSPACE+64
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
