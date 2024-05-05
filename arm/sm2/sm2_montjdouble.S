// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point doubling on GM/T 0003-2012 curve SM2 in Montgomery-Jacobian coordinates
//
//    extern void sm2_montjdouble
//      (uint64_t p3[static 12],uint64_t p1[static 12]);
//
// Does p3 := 2 * p1 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_sm2.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
//
// Standard ARM ABI: X0 = p3, X1 = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sm2_montjdouble)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sm2_montjdouble)
        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 32

// Stable homes for input arguments during main code sequence

#define input_z x19
#define input_x x20

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

#define NSPACE (NUMSIZE*7)

// Corresponds to bignum_montmul_sm2 exactly

#define montmul_sm2(P0,P1,P2)                   \
        ldp     x3, x4, [P1];                   \
        ldp     x5, x6, [P1+16];                \
        ldp     x7, x8, [P2];                   \
        ldp     x9, x10, [P2+16];               \
        mul     x11, x3, x7;                    \
        mul     x13, x4, x8;                    \
        umulh   x12, x3, x7;                    \
        adds    x16, x11, x13;                  \
        umulh   x14, x4, x8;                    \
        adcs    x17, x12, x14;                  \
        adcs    x14, x14, xzr;                  \
        adds    x12, x12, x16;                  \
        adcs    x13, x13, x17;                  \
        adcs    x14, x14, xzr;                  \
        subs    x15, x3, x4;                    \
        cneg    x15, x15, lo;                   \
        csetm   x1, lo;                         \
        subs    x17, x8, x7;                    \
        cneg    x17, x17, lo;                   \
        mul     x16, x15, x17;                  \
        umulh   x17, x15, x17;                  \
        cinv    x1, x1, lo;                     \
        eor     x16, x16, x1;                   \
        eor     x17, x17, x1;                   \
        cmn     x1, #1;                         \
        adcs    x12, x12, x16;                  \
        adcs    x13, x13, x17;                  \
        adc     x14, x14, x1;                   \
        lsl     x16, x11, #32;                  \
        lsr     x15, x11, #32;                  \
        subs    x1, x16, x11;                   \
        sbc     x17, x15, xzr;                  \
        subs    x12, x12, x1;                   \
        sbcs    x13, x13, x17;                  \
        sbcs    x14, x14, x16;                  \
        sbc     x11, x11, x15;                  \
        lsl     x16, x12, #32;                  \
        lsr     x15, x12, #32;                  \
        subs    x1, x16, x12;                   \
        sbc     x17, x15, xzr;                  \
        subs    x13, x13, x1;                   \
        sbcs    x14, x14, x17;                  \
        sbcs    x11, x11, x16;                  \
        sbc     x12, x12, x15;                  \
        stp     x13, x14, [P0];                 \
        stp     x11, x12, [P0+16];              \
        mul     x11, x5, x9;                    \
        mul     x13, x6, x10;                   \
        umulh   x12, x5, x9;                    \
        adds    x16, x11, x13;                  \
        umulh   x14, x6, x10;                   \
        adcs    x17, x12, x14;                  \
        adcs    x14, x14, xzr;                  \
        adds    x12, x12, x16;                  \
        adcs    x13, x13, x17;                  \
        adcs    x14, x14, xzr;                  \
        subs    x15, x5, x6;                    \
        cneg    x15, x15, lo;                   \
        csetm   x1, lo;                         \
        subs    x17, x10, x9;                   \
        cneg    x17, x17, lo;                   \
        mul     x16, x15, x17;                  \
        umulh   x17, x15, x17;                  \
        cinv    x1, x1, lo;                     \
        eor     x16, x16, x1;                   \
        eor     x17, x17, x1;                   \
        cmn     x1, #1;                         \
        adcs    x12, x12, x16;                  \
        adcs    x13, x13, x17;                  \
        adc     x14, x14, x1;                   \
        subs    x3, x5, x3;                     \
        sbcs    x4, x6, x4;                     \
        ngc     x5, xzr;                        \
        cmn     x5, #1;                         \
        eor     x3, x3, x5;                     \
        adcs    x3, x3, xzr;                    \
        eor     x4, x4, x5;                     \
        adcs    x4, x4, xzr;                    \
        subs    x7, x7, x9;                     \
        sbcs    x8, x8, x10;                    \
        ngc     x9, xzr;                        \
        cmn     x9, #1;                         \
        eor     x7, x7, x9;                     \
        adcs    x7, x7, xzr;                    \
        eor     x8, x8, x9;                     \
        adcs    x8, x8, xzr;                    \
        eor     x10, x5, x9;                    \
        ldp     x15, x1, [P0];                  \
        adds    x15, x11, x15;                  \
        adcs    x1, x12, x1;                    \
        ldp     x5, x9, [P0+16];                \
        adcs    x5, x13, x5;                    \
        adcs    x9, x14, x9;                    \
        adc     x2, xzr, xzr;                   \
        mul     x11, x3, x7;                    \
        mul     x13, x4, x8;                    \
        umulh   x12, x3, x7;                    \
        adds    x16, x11, x13;                  \
        umulh   x14, x4, x8;                    \
        adcs    x17, x12, x14;                  \
        adcs    x14, x14, xzr;                  \
        adds    x12, x12, x16;                  \
        adcs    x13, x13, x17;                  \
        adcs    x14, x14, xzr;                  \
        subs    x3, x3, x4;                     \
        cneg    x3, x3, lo;                     \
        csetm   x4, lo;                         \
        subs    x17, x8, x7;                    \
        cneg    x17, x17, lo;                   \
        mul     x16, x3, x17;                   \
        umulh   x17, x3, x17;                   \
        cinv    x4, x4, lo;                     \
        eor     x16, x16, x4;                   \
        eor     x17, x17, x4;                   \
        cmn     x4, #1;                         \
        adcs    x12, x12, x16;                  \
        adcs    x13, x13, x17;                  \
        adc     x14, x14, x4;                   \
        cmn     x10, #1;                        \
        eor     x11, x11, x10;                  \
        adcs    x11, x11, x15;                  \
        eor     x12, x12, x10;                  \
        adcs    x12, x12, x1;                   \
        eor     x13, x13, x10;                  \
        adcs    x13, x13, x5;                   \
        eor     x14, x14, x10;                  \
        adcs    x14, x14, x9;                   \
        adcs    x3, x2, x10;                    \
        adcs    x4, x10, xzr;                   \
        adc     x10, x10, xzr;                  \
        adds    x13, x13, x15;                  \
        adcs    x14, x14, x1;                   \
        adcs    x3, x3, x5;                     \
        adcs    x4, x4, x9;                     \
        adc     x10, x10, x2;                   \
        lsl     x16, x11, #32;                  \
        lsr     x15, x11, #32;                  \
        subs    x1, x16, x11;                   \
        sbc     x17, x15, xzr;                  \
        subs    x12, x12, x1;                   \
        sbcs    x13, x13, x17;                  \
        sbcs    x14, x14, x16;                  \
        sbc     x11, x11, x15;                  \
        lsl     x16, x12, #32;                  \
        lsr     x15, x12, #32;                  \
        subs    x1, x16, x12;                   \
        sbc     x17, x15, xzr;                  \
        subs    x13, x13, x1;                   \
        sbcs    x14, x14, x17;                  \
        sbcs    x11, x11, x16;                  \
        sbc     x12, x12, x15;                  \
        adds    x3, x3, x11;                    \
        adcs    x4, x4, x12;                    \
        adc     x10, x10, xzr;                  \
        add     x2, x10, #1;                    \
        lsl     x15, x2, #32;                   \
        sub     x16, x15, x2;                   \
        adds    x13, x13, x2;                   \
        adcs    x14, x14, x16;                  \
        adcs    x3, x3, xzr;                    \
        adcs    x4, x4, x15;                    \
        csetm   x7, lo;                         \
        adds    x13, x13, x7;                   \
        and     x16, x7, #0xffffffff00000000;   \
        adcs    x14, x14, x16;                  \
        adcs    x3, x3, x7;                     \
        and     x15, x7, #0xfffffffeffffffff;   \
        adc     x4, x4, x15;                    \
        stp     x13, x14, [P0];                 \
        stp     x3, x4, [P0+16]

// Corresponds to bignum_montsqr_sm2 exactly

#define montsqr_sm2(P0,P1)                      \
        ldp     x2, x3, [P1];                   \
        ldp     x4, x5, [P1+16];                \
        umull   x15, w2, w2;                    \
        lsr     x11, x2, #32;                   \
        umull   x16, w11, w11;                  \
        umull   x11, w2, w11;                   \
        adds    x15, x15, x11, lsl #33;         \
        lsr     x11, x11, #31;                  \
        adc     x16, x16, x11;                  \
        umull   x17, w3, w3;                    \
        lsr     x11, x3, #32;                   \
        umull   x1, w11, w11;                   \
        umull   x11, w3, w11;                   \
        mul     x12, x2, x3;                    \
        umulh   x13, x2, x3;                    \
        adds    x17, x17, x11, lsl #33;         \
        lsr     x11, x11, #31;                  \
        adc     x1, x1, x11;                    \
        adds    x12, x12, x12;                  \
        adcs    x13, x13, x13;                  \
        adc     x1, x1, xzr;                    \
        adds    x16, x16, x12;                  \
        adcs    x17, x17, x13;                  \
        adc     x1, x1, xzr;                    \
        lsl     x12, x15, #32;                  \
        lsr     x11, x15, #32;                  \
        subs    x14, x12, x15;                  \
        sbc     x13, x11, xzr;                  \
        subs    x16, x16, x14;                  \
        sbcs    x17, x17, x13;                  \
        sbcs    x1, x1, x12;                    \
        sbc     x15, x15, x11;                  \
        lsl     x12, x16, #32;                  \
        lsr     x11, x16, #32;                  \
        subs    x14, x12, x16;                  \
        sbc     x13, x11, xzr;                  \
        subs    x17, x17, x14;                  \
        sbcs    x1, x1, x13;                    \
        sbcs    x15, x15, x12;                  \
        sbc     x16, x16, x11;                  \
        mul     x6, x2, x4;                     \
        mul     x14, x3, x5;                    \
        umulh   x8, x2, x4;                     \
        subs    x10, x2, x3;                    \
        cneg    x10, x10, lo;                   \
        csetm   x13, lo;                        \
        subs    x12, x5, x4;                    \
        cneg    x12, x12, lo;                   \
        mul     x11, x10, x12;                  \
        umulh   x12, x10, x12;                  \
        cinv    x13, x13, lo;                   \
        eor     x11, x11, x13;                  \
        eor     x12, x12, x13;                  \
        adds    x7, x6, x8;                     \
        adc     x8, x8, xzr;                    \
        umulh   x9, x3, x5;                     \
        adds    x7, x7, x14;                    \
        adcs    x8, x8, x9;                     \
        adc     x9, x9, xzr;                    \
        adds    x8, x8, x14;                    \
        adc     x9, x9, xzr;                    \
        cmn     x13, #1;                        \
        adcs    x7, x7, x11;                    \
        adcs    x8, x8, x12;                    \
        adc     x9, x9, x13;                    \
        adds    x6, x6, x6;                     \
        adcs    x7, x7, x7;                     \
        adcs    x8, x8, x8;                     \
        adcs    x9, x9, x9;                     \
        adc     x10, xzr, xzr;                  \
        adds    x6, x6, x17;                    \
        adcs    x7, x7, x1;                     \
        adcs    x8, x8, x15;                    \
        adcs    x9, x9, x16;                    \
        adc     x10, x10, xzr;                  \
        lsl     x12, x6, #32;                   \
        lsr     x11, x6, #32;                   \
        subs    x14, x12, x6;                   \
        sbc     x13, x11, xzr;                  \
        subs    x7, x7, x14;                    \
        sbcs    x8, x8, x13;                    \
        sbcs    x9, x9, x12;                    \
        sbc     x14, x6, x11;                   \
        adds    x10, x10, x14;                  \
        adc     x6, xzr, xzr;                   \
        lsl     x12, x7, #32;                   \
        lsr     x11, x7, #32;                   \
        subs    x14, x12, x7;                   \
        sbc     x13, x11, xzr;                  \
        subs    x8, x8, x14;                    \
        sbcs    x9, x9, x13;                    \
        sbcs    x10, x10, x12;                  \
        sbc     x14, x7, x11;                   \
        adds    x6, x6, x14;                    \
        adc     x7, xzr, xzr;                   \
        mul     x11, x4, x4;                    \
        adds    x8, x8, x11;                    \
        mul     x12, x5, x5;                    \
        umulh   x11, x4, x4;                    \
        adcs    x9, x9, x11;                    \
        adcs    x10, x10, x12;                  \
        umulh   x12, x5, x5;                    \
        adcs    x6, x6, x12;                    \
        adc     x7, x7, xzr;                    \
        mul     x11, x4, x5;                    \
        umulh   x12, x4, x5;                    \
        adds    x11, x11, x11;                  \
        adcs    x12, x12, x12;                  \
        adc     x13, xzr, xzr;                  \
        adds    x9, x9, x11;                    \
        adcs    x10, x10, x12;                  \
        adcs    x6, x6, x13;                    \
        adcs    x7, x7, xzr;                    \
        mov     x11, #-4294967296;              \
        adds    x5, x8, #1;                     \
        sbcs    x11, x9, x11;                   \
        mov     x13, #-4294967297;              \
        adcs    x12, x10, xzr;                  \
        sbcs    x13, x6, x13;                   \
        sbcs    xzr, x7, xzr;                   \
        csel    x8, x5, x8, hs;                 \
        csel    x9, x11, x9, hs;                \
        csel    x10, x12, x10, hs;              \
        csel    x6, x13, x6, hs;                \
        stp     x8, x9, [P0];                   \
        stp     x10, x6, [P0+16]

// Corresponds exactly to bignum_sub_sm2

#define sub_sm2(P0,P1,P2)                       \
        ldp     x5, x6, [P1];                   \
        ldp     x4, x3, [P2];                   \
        subs    x5, x5, x4;                     \
        sbcs    x6, x6, x3;                     \
        ldp     x7, x8, [P1+16];                \
        ldp     x4, x3, [P2+16];                \
        sbcs    x7, x7, x4;                     \
        sbcs    x8, x8, x3;                     \
        csetm   x3, cc;                         \
        adds    x5, x5, x3;                     \
        and     x4, x3, #0xffffffff00000000;    \
        adcs    x6, x6, x4;                     \
        adcs    x7, x7, x3;                     \
        and     x4, x3, #0xfffffffeffffffff;    \
        adc     x8, x8, x4;                     \
        stp     x5, x6, [P0];                   \
        stp     x7, x8, [P0+16]

// Corresponds exactly to bignum_add_sm2

#define add_sm2(P0,P1,P2)                       \
        ldp     x4, x5, [P1];                   \
        ldp     x8, x9, [P2];                   \
        adds    x4, x4, x8;                     \
        adcs    x5, x5, x9;                     \
        ldp     x6, x7, [P1+16];                \
        ldp     x10, x11, [P2+16];              \
        adcs    x6, x6, x10;                    \
        adcs    x7, x7, x11;                    \
        adc     x3, xzr, xzr;                   \
        adds    x8, x4, #0x1;                   \
        mov     x9, #0xffffffff00000000;        \
        sbcs    x9, x5, x9;                     \
        adcs    x10, x6, xzr;                   \
        mov     x11, #0xfffffffeffffffff;       \
        sbcs    x11, x7, x11;                   \
        sbcs    x3, x3, xzr;                    \
        csel    x4, x4, x8, cc;                 \
        csel    x5, x5, x9, cc;                 \
        csel    x6, x6, x10, cc;                \
        csel    x7, x7, x11, cc;                \
        stp     x4, x5, [P0];                   \
        stp     x6, x7, [P0+16]

// A weak version of add that only guarantees sum in 4 digits

#define weakadd_sm2(P0,P1,P2)                   \
        ldp     x4, x5, [P1];                   \
        ldp     x8, x9, [P2];                   \
        adds    x4, x4, x8;                     \
        adcs    x5, x5, x9;                     \
        ldp     x6, x7, [P1+16];                \
        ldp     x10, x11, [P2+16];              \
        adcs    x6, x6, x10;                    \
        adcs    x7, x7, x11;                    \
        csetm   x2, cs;                         \
        subs    x4, x4, x2;                     \
        and     x3, x2, #0xffffffff00000000;    \
        sbcs    x5, x5, x3;                     \
        and     x1, x2, #0xfffffffeffffffff;    \
        sbcs    x6, x6, x2;                     \
        sbc     x7, x7, x1;                     \
        stp     x4, x5, [P0];                   \
        stp     x6, x7, [P0+16]

// P0 = C * P1 - D * P2 computed as D * (p_sm2 - P2) + C * P1
// Quotient estimation is done just as q = h + 1 as in bignum_triple_sm2
// This also applies to the other functions following.

#define cmsub_sm2(P0,C,P1,D,P2)                 \
        mov     x1, D;                          \
        mov     x2, #-1;                        \
        ldp     x9, x10, [P2];                  \
        subs    x9, x2, x9;                     \
        mov     x3, #0xffffffff00000000;        \
        sbcs    x10, x3, x10;                   \
        ldp     x11, x12, [P2+16];              \
        sbcs    x11, x2, x11;                   \
        mov     x4, #0xfffffffeffffffff;        \
        sbc     x12, x4, x12;                   \
        mul     x3, x1, x9;                     \
        mul     x4, x1, x10;                    \
        mul     x5, x1, x11;                    \
        mul     x6, x1, x12;                    \
        umulh   x9, x1, x9;                     \
        umulh   x10, x1, x10;                   \
        umulh   x11, x1, x11;                   \
        umulh   x7, x1, x12;                    \
        adds    x4, x4, x9;                     \
        adcs    x5, x5, x10;                    \
        adcs    x6, x6, x11;                    \
        adc     x7, x7, xzr;                    \
        mov     x1, C;                          \
        ldp     x9, x10, [P1];                  \
        mul     x8, x9, x1;                     \
        umulh   x9, x9, x1;                     \
        adds    x3, x3, x8;                     \
        mul     x8, x10, x1;                    \
        umulh   x10, x10, x1;                   \
        adcs    x4, x4, x8;                     \
        ldp     x11, x12, [P1+16];              \
        mul     x8, x11, x1;                    \
        umulh   x11, x11, x1;                   \
        adcs    x5, x5, x8;                     \
        mul     x8, x12, x1;                    \
        umulh   x12, x12, x1;                   \
        adcs    x6, x6, x8;                     \
        adc     x7, x7, xzr;                    \
        adds    x4, x4, x9;                     \
        adcs    x5, x5, x10;                    \
        adcs    x6, x6, x11;                    \
        adc     x7, x7, x12;                    \
        add     x7, x7, #0x1;                   \
        lsl     x8, x7, #32;                    \
        sub     x9, x8, x7;                     \
        adds    x3, x3, x7;                     \
        adcs    x4, x4, x9;                     \
        adcs    x5, x5, xzr;                    \
        adcs    x6, x6, x8;                     \
        csetm   x7, cc;                         \
        adds    x3, x3, x7;                     \
        and     x9, x7, #0xffffffff00000000;    \
        adcs    x4, x4, x9;                     \
        adcs    x5, x5, x7;                     \
        and     x8, x7, #0xfffffffeffffffff;    \
        adc     x6, x6, x8;                     \
        stp     x3, x4, [P0];                   \
        stp     x5, x6, [P0+16]

// P0 = 4 * P1 - P2, by direct subtraction of P2; the method
// in bignum_cmul_sm2 etc. for quotient estimation still
// works when the value to be reduced is negative, as
// long as it is > -p_sm2, which is the case here.

#define cmsub41_sm2(P0,P1,P2)                   \
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
        lsr     x4, x4, #62;                    \
        sbc     x4, x4, xzr;                    \
        add     x4, x4, #0x1;                   \
        lsl     x5, x4, #32;                    \
        sub     x6, x5, x4;                     \
        adds    x0, x0, x4;                     \
        adcs    x1, x1, x6;                     \
        adcs    x2, x2, xzr;                    \
        adcs    x3, x3, x5;                     \
        csetm   x4, cc;                         \
        adds    x0, x0, x4;                     \
        and     x6, x4, #0xffffffff00000000;    \
        adcs    x1, x1, x6;                     \
        adcs    x2, x2, x4;                     \
        and     x5, x4, #0xfffffffeffffffff;    \
        adc     x3, x3, x5;                     \
        stp     x0, x1, [P0];                   \
        stp     x2, x3, [P0+16]

// P0 = 3 * P1 - 8 * P2, computed as (p_sm2 - P2) << 3 + 3 * P1

#define cmsub38_sm2(P0,P1,P2)                   \
        mov     x1, 8;                          \
        mov     x2, #-1;                        \
        ldp     x9, x10, [P2];                  \
        subs    x9, x2, x9;                     \
        mov     x3, #0xffffffff00000000;        \
        sbcs    x10, x3, x10;                   \
        ldp     x11, x12, [P2+16];              \
        sbcs    x11, x2, x11;                   \
        mov     x4, #0xfffffffeffffffff;        \
        sbc     x12, x4, x12;                   \
        lsl     x3, x9, #3;                     \
        extr    x4, x10, x9, #61;               \
        extr    x5, x11, x10, #61;              \
        extr    x6, x12, x11, #61;              \
        lsr     x7, x12, #61;                   \
        mov     x1, 3;                          \
        ldp     x9, x10, [P1];                  \
        mul     x8, x9, x1;                     \
        umulh   x9, x9, x1;                     \
        adds    x3, x3, x8;                     \
        mul     x8, x10, x1;                    \
        umulh   x10, x10, x1;                   \
        adcs    x4, x4, x8;                     \
        ldp     x11, x12, [P1+16];              \
        mul     x8, x11, x1;                    \
        umulh   x11, x11, x1;                   \
        adcs    x5, x5, x8;                     \
        mul     x8, x12, x1;                    \
        umulh   x12, x12, x1;                   \
        adcs    x6, x6, x8;                     \
        adc     x7, x7, xzr;                    \
        adds    x4, x4, x9;                     \
        adcs    x5, x5, x10;                    \
        adcs    x6, x6, x11;                    \
        adc     x7, x7, x12;                    \
        add     x7, x7, #0x1;                   \
        lsl     x8, x7, #32;                    \
        sub     x9, x8, x7;                     \
        adds    x3, x3, x7;                     \
        adcs    x4, x4, x9;                     \
        adcs    x5, x5, xzr;                    \
        adcs    x6, x6, x8;                     \
        csetm   x7, cc;                         \
        adds    x3, x3, x7;                     \
        and     x9, x7, #0xffffffff00000000;    \
        adcs    x4, x4, x9;                     \
        adcs    x5, x5, x7;                     \
        and     x8, x7, #0xfffffffeffffffff;    \
        adc     x6, x6, x8;                     \
        stp     x3, x4, [P0];                   \
        stp     x5, x6, [P0+16]

S2N_BN_SYMBOL(sm2_montjdouble):

// Save registers and make room on stack for temporary variables

        sub     sp, sp, NSPACE+16
        stp     x19, x20, [sp, NSPACE]

// Move the input arguments to stable places

        mov     input_z, x0
        mov     input_x, x1

// Main code, just a sequence of basic field operations

// z2 = z^2
// y2 = y^2

        montsqr_sm2(z2,z_1)
        montsqr_sm2(y2,y_1)

// x2p = x^2 - z^4 = (x + z^2) * (x - z^2)

        weakadd_sm2(t1,x_1,z2)
        sub_sm2(t2,x_1,z2)
        montmul_sm2(x2p,t1,t2)

// t1 = y + z
// x4p = x2p^2
// xy2 = x * y^2

        add_sm2(t1,y_1,z_1)
        montsqr_sm2(x4p,x2p)
        montmul_sm2(xy2,x_1,y2)

// t2 = (y + z)^2

        montsqr_sm2(t2,t1)

// d = 12 * xy2 - 9 * x4p
// t1 = y^2 + 2 * y * z

        cmsub_sm2(d,12,xy2,9,x4p)
        sub_sm2(t1,t2,z2)

// y4 = y^4

        montsqr_sm2(y4,y2)

// z_3' = 2 * y * z
// dx2 = d * x2p

        sub_sm2(z_3,t1,y2)
        montmul_sm2(dx2,d,x2p)

// x' = 4 * xy2 - d

        cmsub41_sm2(x_3,xy2,d)

// y' = 3 * dx2 - 8 * y4

        cmsub38_sm2(y_3,dx2,y4);

// Restore registers and stack and return

        ldp     x19, x20, [sp, NSPACE]
        add     sp, sp, NSPACE+16
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
