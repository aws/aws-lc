// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point addition on NIST curve P-384 in Montgomery-Jacobian coordinates
//
//    extern void p384_montjadd
//      (uint64_t p3[static 18],uint64_t p1[static 18],uint64_t p2[static 18]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^384 * x) mod p_384.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
//
// Standard ARM ABI: X0 = p3, X1 = p1, X2 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p384_montjadd)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p384_montjadd)
        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 48

// Stable homes for input arguments during main code sequence

#define input_z x24
#define input_x x25
#define input_y x26

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

#define yd sp, #(NUMSIZE*1)
#define y2a sp, #(NUMSIZE*1)

#define x2a sp, #(NUMSIZE*2)
#define zzx2 sp, #(NUMSIZE*2)

#define zz sp, #(NUMSIZE*3)
#define t1 sp, #(NUMSIZE*3)

#define t2 sp, #(NUMSIZE*4)
#define x1a sp, #(NUMSIZE*4)
#define zzx1 sp, #(NUMSIZE*4)

#define xd sp, #(NUMSIZE*5)
#define z2sq sp, #(NUMSIZE*5)

#define y1a sp, #(NUMSIZE*6)

#define NSPACE (NUMSIZE*7)

// Corresponds exactly to bignum_montmul_p384_alt

#define montmul_p384(P0,P1,P2)                  \
        ldp     x3, x4, [P1];                   \
        ldp     x5, x6, [P2];                   \
        mul     x12, x3, x5;                    \
        umulh   x13, x3, x5;                    \
        mul     x11, x3, x6;                    \
        umulh   x14, x3, x6;                    \
        adds    x13, x13, x11;                  \
        ldp     x7, x8, [P2+16];                \
        mul     x11, x3, x7;                    \
        umulh   x15, x3, x7;                    \
        adcs    x14, x14, x11;                  \
        mul     x11, x3, x8;                    \
        umulh   x16, x3, x8;                    \
        adcs    x15, x15, x11;                  \
        ldp     x9, x10, [P2+32];               \
        mul     x11, x3, x9;                    \
        umulh   x17, x3, x9;                    \
        adcs    x16, x16, x11;                  \
        mul     x11, x3, x10;                   \
        umulh   x19, x3, x10;                   \
        adcs    x17, x17, x11;                  \
        adc     x19, x19, xzr;                  \
        mul     x11, x4, x5;                    \
        adds    x13, x13, x11;                  \
        mul     x11, x4, x6;                    \
        adcs    x14, x14, x11;                  \
        mul     x11, x4, x7;                    \
        adcs    x15, x15, x11;                  \
        mul     x11, x4, x8;                    \
        adcs    x16, x16, x11;                  \
        mul     x11, x4, x9;                    \
        adcs    x17, x17, x11;                  \
        mul     x11, x4, x10;                   \
        adcs    x19, x19, x11;                  \
        cset    x20, cs;                        \
        umulh   x11, x4, x5;                    \
        adds    x14, x14, x11;                  \
        umulh   x11, x4, x6;                    \
        adcs    x15, x15, x11;                  \
        umulh   x11, x4, x7;                    \
        adcs    x16, x16, x11;                  \
        umulh   x11, x4, x8;                    \
        adcs    x17, x17, x11;                  \
        umulh   x11, x4, x9;                    \
        adcs    x19, x19, x11;                  \
        umulh   x11, x4, x10;                   \
        adc     x20, x20, x11;                  \
        ldp     x3, x4, [P1+16];                \
        mul     x11, x3, x5;                    \
        adds    x14, x14, x11;                  \
        mul     x11, x3, x6;                    \
        adcs    x15, x15, x11;                  \
        mul     x11, x3, x7;                    \
        adcs    x16, x16, x11;                  \
        mul     x11, x3, x8;                    \
        adcs    x17, x17, x11;                  \
        mul     x11, x3, x9;                    \
        adcs    x19, x19, x11;                  \
        mul     x11, x3, x10;                   \
        adcs    x20, x20, x11;                  \
        cset    x21, cs;                        \
        umulh   x11, x3, x5;                    \
        adds    x15, x15, x11;                  \
        umulh   x11, x3, x6;                    \
        adcs    x16, x16, x11;                  \
        umulh   x11, x3, x7;                    \
        adcs    x17, x17, x11;                  \
        umulh   x11, x3, x8;                    \
        adcs    x19, x19, x11;                  \
        umulh   x11, x3, x9;                    \
        adcs    x20, x20, x11;                  \
        umulh   x11, x3, x10;                   \
        adc     x21, x21, x11;                  \
        mul     x11, x4, x5;                    \
        adds    x15, x15, x11;                  \
        mul     x11, x4, x6;                    \
        adcs    x16, x16, x11;                  \
        mul     x11, x4, x7;                    \
        adcs    x17, x17, x11;                  \
        mul     x11, x4, x8;                    \
        adcs    x19, x19, x11;                  \
        mul     x11, x4, x9;                    \
        adcs    x20, x20, x11;                  \
        mul     x11, x4, x10;                   \
        adcs    x21, x21, x11;                  \
        cset    x22, cs;                        \
        umulh   x11, x4, x5;                    \
        adds    x16, x16, x11;                  \
        umulh   x11, x4, x6;                    \
        adcs    x17, x17, x11;                  \
        umulh   x11, x4, x7;                    \
        adcs    x19, x19, x11;                  \
        umulh   x11, x4, x8;                    \
        adcs    x20, x20, x11;                  \
        umulh   x11, x4, x9;                    \
        adcs    x21, x21, x11;                  \
        umulh   x11, x4, x10;                   \
        adc     x22, x22, x11;                  \
        ldp     x3, x4, [P1+32];                \
        mul     x11, x3, x5;                    \
        adds    x16, x16, x11;                  \
        mul     x11, x3, x6;                    \
        adcs    x17, x17, x11;                  \
        mul     x11, x3, x7;                    \
        adcs    x19, x19, x11;                  \
        mul     x11, x3, x8;                    \
        adcs    x20, x20, x11;                  \
        mul     x11, x3, x9;                    \
        adcs    x21, x21, x11;                  \
        mul     x11, x3, x10;                   \
        adcs    x22, x22, x11;                  \
        cset    x2, cs;                         \
        umulh   x11, x3, x5;                    \
        adds    x17, x17, x11;                  \
        umulh   x11, x3, x6;                    \
        adcs    x19, x19, x11;                  \
        umulh   x11, x3, x7;                    \
        adcs    x20, x20, x11;                  \
        umulh   x11, x3, x8;                    \
        adcs    x21, x21, x11;                  \
        umulh   x11, x3, x9;                    \
        adcs    x22, x22, x11;                  \
        umulh   x11, x3, x10;                   \
        adc     x2, x2, x11;                    \
        mul     x11, x4, x5;                    \
        adds    x17, x17, x11;                  \
        mul     x11, x4, x6;                    \
        adcs    x19, x19, x11;                  \
        mul     x11, x4, x7;                    \
        adcs    x20, x20, x11;                  \
        mul     x11, x4, x8;                    \
        adcs    x21, x21, x11;                  \
        mul     x11, x4, x9;                    \
        adcs    x22, x22, x11;                  \
        mul     x11, x4, x10;                   \
        adcs    x2, x2, x11;                    \
        cset    x1, cs;                         \
        umulh   x11, x4, x5;                    \
        adds    x19, x19, x11;                  \
        umulh   x11, x4, x6;                    \
        adcs    x20, x20, x11;                  \
        umulh   x11, x4, x7;                    \
        adcs    x21, x21, x11;                  \
        umulh   x11, x4, x8;                    \
        adcs    x22, x22, x11;                  \
        umulh   x11, x4, x9;                    \
        adcs    x2, x2, x11;                    \
        umulh   x11, x4, x10;                   \
        adc     x1, x1, x11;                    \
        lsl     x7, x12, #32;                   \
        add     x12, x7, x12;                   \
        mov     x7, #0xffffffff00000001;        \
        umulh   x7, x7, x12;                    \
        mov     x6, #0xffffffff;                \
        mul     x5, x6, x12;                    \
        umulh   x6, x6, x12;                    \
        adds    x7, x7, x5;                     \
        adcs    x6, x6, x12;                    \
        adc     x5, xzr, xzr;                   \
        subs    x13, x13, x7;                   \
        sbcs    x14, x14, x6;                   \
        sbcs    x15, x15, x5;                   \
        sbcs    x16, x16, xzr;                  \
        sbcs    x17, x17, xzr;                  \
        sbc     x12, x12, xzr;                  \
        lsl     x7, x13, #32;                   \
        add     x13, x7, x13;                   \
        mov     x7, #0xffffffff00000001;        \
        umulh   x7, x7, x13;                    \
        mov     x6, #0xffffffff;                \
        mul     x5, x6, x13;                    \
        umulh   x6, x6, x13;                    \
        adds    x7, x7, x5;                     \
        adcs    x6, x6, x13;                    \
        adc     x5, xzr, xzr;                   \
        subs    x14, x14, x7;                   \
        sbcs    x15, x15, x6;                   \
        sbcs    x16, x16, x5;                   \
        sbcs    x17, x17, xzr;                  \
        sbcs    x12, x12, xzr;                  \
        sbc     x13, x13, xzr;                  \
        lsl     x7, x14, #32;                   \
        add     x14, x7, x14;                   \
        mov     x7, #0xffffffff00000001;        \
        umulh   x7, x7, x14;                    \
        mov     x6, #0xffffffff;                \
        mul     x5, x6, x14;                    \
        umulh   x6, x6, x14;                    \
        adds    x7, x7, x5;                     \
        adcs    x6, x6, x14;                    \
        adc     x5, xzr, xzr;                   \
        subs    x15, x15, x7;                   \
        sbcs    x16, x16, x6;                   \
        sbcs    x17, x17, x5;                   \
        sbcs    x12, x12, xzr;                  \
        sbcs    x13, x13, xzr;                  \
        sbc     x14, x14, xzr;                  \
        lsl     x7, x15, #32;                   \
        add     x15, x7, x15;                   \
        mov     x7, #0xffffffff00000001;        \
        umulh   x7, x7, x15;                    \
        mov     x6, #0xffffffff;                \
        mul     x5, x6, x15;                    \
        umulh   x6, x6, x15;                    \
        adds    x7, x7, x5;                     \
        adcs    x6, x6, x15;                    \
        adc     x5, xzr, xzr;                   \
        subs    x16, x16, x7;                   \
        sbcs    x17, x17, x6;                   \
        sbcs    x12, x12, x5;                   \
        sbcs    x13, x13, xzr;                  \
        sbcs    x14, x14, xzr;                  \
        sbc     x15, x15, xzr;                  \
        lsl     x7, x16, #32;                   \
        add     x16, x7, x16;                   \
        mov     x7, #0xffffffff00000001;        \
        umulh   x7, x7, x16;                    \
        mov     x6, #0xffffffff;                \
        mul     x5, x6, x16;                    \
        umulh   x6, x6, x16;                    \
        adds    x7, x7, x5;                     \
        adcs    x6, x6, x16;                    \
        adc     x5, xzr, xzr;                   \
        subs    x17, x17, x7;                   \
        sbcs    x12, x12, x6;                   \
        sbcs    x13, x13, x5;                   \
        sbcs    x14, x14, xzr;                  \
        sbcs    x15, x15, xzr;                  \
        sbc     x16, x16, xzr;                  \
        lsl     x7, x17, #32;                   \
        add     x17, x7, x17;                   \
        mov     x7, #0xffffffff00000001;        \
        umulh   x7, x7, x17;                    \
        mov     x6, #0xffffffff;                \
        mul     x5, x6, x17;                    \
        umulh   x6, x6, x17;                    \
        adds    x7, x7, x5;                     \
        adcs    x6, x6, x17;                    \
        adc     x5, xzr, xzr;                   \
        subs    x12, x12, x7;                   \
        sbcs    x13, x13, x6;                   \
        sbcs    x14, x14, x5;                   \
        sbcs    x15, x15, xzr;                  \
        sbcs    x16, x16, xzr;                  \
        sbc     x17, x17, xzr;                  \
        adds    x12, x12, x19;                  \
        adcs    x13, x13, x20;                  \
        adcs    x14, x14, x21;                  \
        adcs    x15, x15, x22;                  \
        adcs    x16, x16, x2;                   \
        adcs    x17, x17, x1;                   \
        adc     x10, xzr, xzr;                  \
        mov     x11, #0xffffffff00000001;       \
        adds    x19, x12, x11;                  \
        mov     x11, #0xffffffff;               \
        adcs    x20, x13, x11;                  \
        mov     x11, #0x1;                      \
        adcs    x21, x14, x11;                  \
        adcs    x22, x15, xzr;                  \
        adcs    x2, x16, xzr;                   \
        adcs    x1, x17, xzr;                   \
        adcs    x10, x10, xzr;                  \
        csel    x12, x12, x19, eq;              \
        csel    x13, x13, x20, eq;              \
        csel    x14, x14, x21, eq;              \
        csel    x15, x15, x22, eq;              \
        csel    x16, x16, x2, eq;               \
        csel    x17, x17, x1, eq;               \
        stp     x12, x13, [P0];                 \
        stp     x14, x15, [P0+16];              \
        stp     x16, x17, [P0+32]

// Corresponds exactly to bignum_montsqr_p384_alt

#define montsqr_p384(P0,P1)                     \
        ldp     x2, x3, [P1];                   \
        mul     x9, x2, x3;                     \
        umulh   x10, x2, x3;                    \
        ldp     x4, x5, [P1+16];                \
        mul     x8, x2, x4;                     \
        adds    x10, x10, x8;                   \
        mul     x11, x2, x5;                    \
        mul     x8, x3, x4;                     \
        adcs    x11, x11, x8;                   \
        umulh   x12, x2, x5;                    \
        mul     x8, x3, x5;                     \
        adcs    x12, x12, x8;                   \
        ldp     x6, x7, [P1+32];                \
        mul     x13, x2, x7;                    \
        mul     x8, x3, x6;                     \
        adcs    x13, x13, x8;                   \
        umulh   x14, x2, x7;                    \
        mul     x8, x3, x7;                     \
        adcs    x14, x14, x8;                   \
        mul     x15, x5, x6;                    \
        adcs    x15, x15, xzr;                  \
        umulh   x16, x5, x6;                    \
        adc     x16, x16, xzr;                  \
        umulh   x8, x2, x4;                     \
        adds    x11, x11, x8;                   \
        umulh   x8, x3, x4;                     \
        adcs    x12, x12, x8;                   \
        umulh   x8, x3, x5;                     \
        adcs    x13, x13, x8;                   \
        umulh   x8, x3, x6;                     \
        adcs    x14, x14, x8;                   \
        umulh   x8, x3, x7;                     \
        adcs    x15, x15, x8;                   \
        adc     x16, x16, xzr;                  \
        mul     x8, x2, x6;                     \
        adds    x12, x12, x8;                   \
        mul     x8, x4, x5;                     \
        adcs    x13, x13, x8;                   \
        mul     x8, x4, x6;                     \
        adcs    x14, x14, x8;                   \
        mul     x8, x4, x7;                     \
        adcs    x15, x15, x8;                   \
        mul     x8, x5, x7;                     \
        adcs    x16, x16, x8;                   \
        mul     x17, x6, x7;                    \
        adcs    x17, x17, xzr;                  \
        umulh   x19, x6, x7;                    \
        adc     x19, x19, xzr;                  \
        umulh   x8, x2, x6;                     \
        adds    x13, x13, x8;                   \
        umulh   x8, x4, x5;                     \
        adcs    x14, x14, x8;                   \
        umulh   x8, x4, x6;                     \
        adcs    x15, x15, x8;                   \
        umulh   x8, x4, x7;                     \
        adcs    x16, x16, x8;                   \
        umulh   x8, x5, x7;                     \
        adcs    x17, x17, x8;                   \
        adc     x19, x19, xzr;                  \
        adds    x9, x9, x9;                     \
        adcs    x10, x10, x10;                  \
        adcs    x11, x11, x11;                  \
        adcs    x12, x12, x12;                  \
        adcs    x13, x13, x13;                  \
        adcs    x14, x14, x14;                  \
        adcs    x15, x15, x15;                  \
        adcs    x16, x16, x16;                  \
        adcs    x17, x17, x17;                  \
        adcs    x19, x19, x19;                  \
        cset    x20, hs;                        \
        umulh   x8, x2, x2;                     \
        mul     x2, x2, x2;                     \
        adds    x9, x9, x8;                     \
        mul     x8, x3, x3;                     \
        adcs    x10, x10, x8;                   \
        umulh   x8, x3, x3;                     \
        adcs    x11, x11, x8;                   \
        mul     x8, x4, x4;                     \
        adcs    x12, x12, x8;                   \
        umulh   x8, x4, x4;                     \
        adcs    x13, x13, x8;                   \
        mul     x8, x5, x5;                     \
        adcs    x14, x14, x8;                   \
        umulh   x8, x5, x5;                     \
        adcs    x15, x15, x8;                   \
        mul     x8, x6, x6;                     \
        adcs    x16, x16, x8;                   \
        umulh   x8, x6, x6;                     \
        adcs    x17, x17, x8;                   \
        mul     x8, x7, x7;                     \
        adcs    x19, x19, x8;                   \
        umulh   x8, x7, x7;                     \
        adc     x20, x20, x8;                   \
        lsl     x5, x2, #32;                    \
        add     x2, x5, x2;                     \
        mov     x5, #-4294967295;               \
        umulh   x5, x5, x2;                     \
        mov     x4, #4294967295;                \
        mul     x3, x4, x2;                     \
        umulh   x4, x4, x2;                     \
        adds    x5, x5, x3;                     \
        adcs    x4, x4, x2;                     \
        adc     x3, xzr, xzr;                   \
        subs    x9, x9, x5;                     \
        sbcs    x10, x10, x4;                   \
        sbcs    x11, x11, x3;                   \
        sbcs    x12, x12, xzr;                  \
        sbcs    x13, x13, xzr;                  \
        sbc     x2, x2, xzr;                    \
        lsl     x5, x9, #32;                    \
        add     x9, x5, x9;                     \
        mov     x5, #-4294967295;               \
        umulh   x5, x5, x9;                     \
        mov     x4, #4294967295;                \
        mul     x3, x4, x9;                     \
        umulh   x4, x4, x9;                     \
        adds    x5, x5, x3;                     \
        adcs    x4, x4, x9;                     \
        adc     x3, xzr, xzr;                   \
        subs    x10, x10, x5;                   \
        sbcs    x11, x11, x4;                   \
        sbcs    x12, x12, x3;                   \
        sbcs    x13, x13, xzr;                  \
        sbcs    x2, x2, xzr;                    \
        sbc     x9, x9, xzr;                    \
        lsl     x5, x10, #32;                   \
        add     x10, x5, x10;                   \
        mov     x5, #-4294967295;               \
        umulh   x5, x5, x10;                    \
        mov     x4, #4294967295;                \
        mul     x3, x4, x10;                    \
        umulh   x4, x4, x10;                    \
        adds    x5, x5, x3;                     \
        adcs    x4, x4, x10;                    \
        adc     x3, xzr, xzr;                   \
        subs    x11, x11, x5;                   \
        sbcs    x12, x12, x4;                   \
        sbcs    x13, x13, x3;                   \
        sbcs    x2, x2, xzr;                    \
        sbcs    x9, x9, xzr;                    \
        sbc     x10, x10, xzr;                  \
        lsl     x5, x11, #32;                   \
        add     x11, x5, x11;                   \
        mov     x5, #-4294967295;               \
        umulh   x5, x5, x11;                    \
        mov     x4, #4294967295;                \
        mul     x3, x4, x11;                    \
        umulh   x4, x4, x11;                    \
        adds    x5, x5, x3;                     \
        adcs    x4, x4, x11;                    \
        adc     x3, xzr, xzr;                   \
        subs    x12, x12, x5;                   \
        sbcs    x13, x13, x4;                   \
        sbcs    x2, x2, x3;                     \
        sbcs    x9, x9, xzr;                    \
        sbcs    x10, x10, xzr;                  \
        sbc     x11, x11, xzr;                  \
        lsl     x5, x12, #32;                   \
        add     x12, x5, x12;                   \
        mov     x5, #-4294967295;               \
        umulh   x5, x5, x12;                    \
        mov     x4, #4294967295;                \
        mul     x3, x4, x12;                    \
        umulh   x4, x4, x12;                    \
        adds    x5, x5, x3;                     \
        adcs    x4, x4, x12;                    \
        adc     x3, xzr, xzr;                   \
        subs    x13, x13, x5;                   \
        sbcs    x2, x2, x4;                     \
        sbcs    x9, x9, x3;                     \
        sbcs    x10, x10, xzr;                  \
        sbcs    x11, x11, xzr;                  \
        sbc     x12, x12, xzr;                  \
        lsl     x5, x13, #32;                   \
        add     x13, x5, x13;                   \
        mov     x5, #-4294967295;               \
        umulh   x5, x5, x13;                    \
        mov     x4, #4294967295;                \
        mul     x3, x4, x13;                    \
        umulh   x4, x4, x13;                    \
        adds    x5, x5, x3;                     \
        adcs    x4, x4, x13;                    \
        adc     x3, xzr, xzr;                   \
        subs    x2, x2, x5;                     \
        sbcs    x9, x9, x4;                     \
        sbcs    x10, x10, x3;                   \
        sbcs    x11, x11, xzr;                  \
        sbcs    x12, x12, xzr;                  \
        sbc     x13, x13, xzr;                  \
        adds    x2, x2, x14;                    \
        adcs    x9, x9, x15;                    \
        adcs    x10, x10, x16;                  \
        adcs    x11, x11, x17;                  \
        adcs    x12, x12, x19;                  \
        adcs    x13, x13, x20;                  \
        adc     x6, xzr, xzr;                   \
        mov     x8, #-4294967295;               \
        adds    x14, x2, x8;                    \
        mov     x8, #4294967295;                \
        adcs    x15, x9, x8;                    \
        mov     x8, #1;                         \
        adcs    x16, x10, x8;                   \
        adcs    x17, x11, xzr;                  \
        adcs    x19, x12, xzr;                  \
        adcs    x20, x13, xzr;                  \
        adcs    x6, x6, xzr;                    \
        csel    x2, x2, x14, eq;                \
        csel    x9, x9, x15, eq;                \
        csel    x10, x10, x16, eq;              \
        csel    x11, x11, x17, eq;              \
        csel    x12, x12, x19, eq;              \
        csel    x13, x13, x20, eq;              \
        stp     x2, x9, [P0];                   \
        stp     x10, x11, [P0+16];              \
        stp     x12, x13, [P0+32]

// Almost-Montgomery variant which we use when an input to other muls
// with the other argument fully reduced (which is always safe). In
// fact, with the Karatsuba-based Montgomery mul here, we don't even
// *need* the restriction that the other argument is reduced.

#define amontsqr_p384(P0,P1)                    \
        ldp     x2, x3, [P1];                   \
        mul     x9, x2, x3;                     \
        umulh   x10, x2, x3;                    \
        ldp     x4, x5, [P1+16];                \
        mul     x8, x2, x4;                     \
        adds    x10, x10, x8;                   \
        mul     x11, x2, x5;                    \
        mul     x8, x3, x4;                     \
        adcs    x11, x11, x8;                   \
        umulh   x12, x2, x5;                    \
        mul     x8, x3, x5;                     \
        adcs    x12, x12, x8;                   \
        ldp     x6, x7, [P1+32];                \
        mul     x13, x2, x7;                    \
        mul     x8, x3, x6;                     \
        adcs    x13, x13, x8;                   \
        umulh   x14, x2, x7;                    \
        mul     x8, x3, x7;                     \
        adcs    x14, x14, x8;                   \
        mul     x15, x5, x6;                    \
        adcs    x15, x15, xzr;                  \
        umulh   x16, x5, x6;                    \
        adc     x16, x16, xzr;                  \
        umulh   x8, x2, x4;                     \
        adds    x11, x11, x8;                   \
        umulh   x8, x3, x4;                     \
        adcs    x12, x12, x8;                   \
        umulh   x8, x3, x5;                     \
        adcs    x13, x13, x8;                   \
        umulh   x8, x3, x6;                     \
        adcs    x14, x14, x8;                   \
        umulh   x8, x3, x7;                     \
        adcs    x15, x15, x8;                   \
        adc     x16, x16, xzr;                  \
        mul     x8, x2, x6;                     \
        adds    x12, x12, x8;                   \
        mul     x8, x4, x5;                     \
        adcs    x13, x13, x8;                   \
        mul     x8, x4, x6;                     \
        adcs    x14, x14, x8;                   \
        mul     x8, x4, x7;                     \
        adcs    x15, x15, x8;                   \
        mul     x8, x5, x7;                     \
        adcs    x16, x16, x8;                   \
        mul     x17, x6, x7;                    \
        adcs    x17, x17, xzr;                  \
        umulh   x19, x6, x7;                    \
        adc     x19, x19, xzr;                  \
        umulh   x8, x2, x6;                     \
        adds    x13, x13, x8;                   \
        umulh   x8, x4, x5;                     \
        adcs    x14, x14, x8;                   \
        umulh   x8, x4, x6;                     \
        adcs    x15, x15, x8;                   \
        umulh   x8, x4, x7;                     \
        adcs    x16, x16, x8;                   \
        umulh   x8, x5, x7;                     \
        adcs    x17, x17, x8;                   \
        adc     x19, x19, xzr;                  \
        adds    x9, x9, x9;                     \
        adcs    x10, x10, x10;                  \
        adcs    x11, x11, x11;                  \
        adcs    x12, x12, x12;                  \
        adcs    x13, x13, x13;                  \
        adcs    x14, x14, x14;                  \
        adcs    x15, x15, x15;                  \
        adcs    x16, x16, x16;                  \
        adcs    x17, x17, x17;                  \
        adcs    x19, x19, x19;                  \
        cset    x20, hs;                        \
        umulh   x8, x2, x2;                     \
        mul     x2, x2, x2;                     \
        adds    x9, x9, x8;                     \
        mul     x8, x3, x3;                     \
        adcs    x10, x10, x8;                   \
        umulh   x8, x3, x3;                     \
        adcs    x11, x11, x8;                   \
        mul     x8, x4, x4;                     \
        adcs    x12, x12, x8;                   \
        umulh   x8, x4, x4;                     \
        adcs    x13, x13, x8;                   \
        mul     x8, x5, x5;                     \
        adcs    x14, x14, x8;                   \
        umulh   x8, x5, x5;                     \
        adcs    x15, x15, x8;                   \
        mul     x8, x6, x6;                     \
        adcs    x16, x16, x8;                   \
        umulh   x8, x6, x6;                     \
        adcs    x17, x17, x8;                   \
        mul     x8, x7, x7;                     \
        adcs    x19, x19, x8;                   \
        umulh   x8, x7, x7;                     \
        adc     x20, x20, x8;                   \
        lsl     x5, x2, #32;                    \
        add     x2, x5, x2;                     \
        mov     x5, #-4294967295;               \
        umulh   x5, x5, x2;                     \
        mov     x4, #4294967295;                \
        mul     x3, x4, x2;                     \
        umulh   x4, x4, x2;                     \
        adds    x5, x5, x3;                     \
        adcs    x4, x4, x2;                     \
        adc     x3, xzr, xzr;                   \
        subs    x9, x9, x5;                     \
        sbcs    x10, x10, x4;                   \
        sbcs    x11, x11, x3;                   \
        sbcs    x12, x12, xzr;                  \
        sbcs    x13, x13, xzr;                  \
        sbc     x2, x2, xzr;                    \
        lsl     x5, x9, #32;                    \
        add     x9, x5, x9;                     \
        mov     x5, #-4294967295;               \
        umulh   x5, x5, x9;                     \
        mov     x4, #4294967295;                \
        mul     x3, x4, x9;                     \
        umulh   x4, x4, x9;                     \
        adds    x5, x5, x3;                     \
        adcs    x4, x4, x9;                     \
        adc     x3, xzr, xzr;                   \
        subs    x10, x10, x5;                   \
        sbcs    x11, x11, x4;                   \
        sbcs    x12, x12, x3;                   \
        sbcs    x13, x13, xzr;                  \
        sbcs    x2, x2, xzr;                    \
        sbc     x9, x9, xzr;                    \
        lsl     x5, x10, #32;                   \
        add     x10, x5, x10;                   \
        mov     x5, #-4294967295;               \
        umulh   x5, x5, x10;                    \
        mov     x4, #4294967295;                \
        mul     x3, x4, x10;                    \
        umulh   x4, x4, x10;                    \
        adds    x5, x5, x3;                     \
        adcs    x4, x4, x10;                    \
        adc     x3, xzr, xzr;                   \
        subs    x11, x11, x5;                   \
        sbcs    x12, x12, x4;                   \
        sbcs    x13, x13, x3;                   \
        sbcs    x2, x2, xzr;                    \
        sbcs    x9, x9, xzr;                    \
        sbc     x10, x10, xzr;                  \
        lsl     x5, x11, #32;                   \
        add     x11, x5, x11;                   \
        mov     x5, #-4294967295;               \
        umulh   x5, x5, x11;                    \
        mov     x4, #4294967295;                \
        mul     x3, x4, x11;                    \
        umulh   x4, x4, x11;                    \
        adds    x5, x5, x3;                     \
        adcs    x4, x4, x11;                    \
        adc     x3, xzr, xzr;                   \
        subs    x12, x12, x5;                   \
        sbcs    x13, x13, x4;                   \
        sbcs    x2, x2, x3;                     \
        sbcs    x9, x9, xzr;                    \
        sbcs    x10, x10, xzr;                  \
        sbc     x11, x11, xzr;                  \
        lsl     x5, x12, #32;                   \
        add     x12, x5, x12;                   \
        mov     x5, #-4294967295;               \
        umulh   x5, x5, x12;                    \
        mov     x4, #4294967295;                \
        mul     x3, x4, x12;                    \
        umulh   x4, x4, x12;                    \
        adds    x5, x5, x3;                     \
        adcs    x4, x4, x12;                    \
        adc     x3, xzr, xzr;                   \
        subs    x13, x13, x5;                   \
        sbcs    x2, x2, x4;                     \
        sbcs    x9, x9, x3;                     \
        sbcs    x10, x10, xzr;                  \
        sbcs    x11, x11, xzr;                  \
        sbc     x12, x12, xzr;                  \
        lsl     x5, x13, #32;                   \
        add     x13, x5, x13;                   \
        mov     x5, #-4294967295;               \
        umulh   x5, x5, x13;                    \
        mov     x4, #4294967295;                \
        mul     x3, x4, x13;                    \
        umulh   x4, x4, x13;                    \
        adds    x5, x5, x3;                     \
        adcs    x4, x4, x13;                    \
        adc     x3, xzr, xzr;                   \
        subs    x2, x2, x5;                     \
        sbcs    x9, x9, x4;                     \
        sbcs    x10, x10, x3;                   \
        sbcs    x11, x11, xzr;                  \
        sbcs    x12, x12, xzr;                  \
        sbc     x13, x13, xzr;                  \
        adds    x2, x2, x14;                    \
        adcs    x9, x9, x15;                    \
        adcs    x10, x10, x16;                  \
        adcs    x11, x11, x17;                  \
        adcs    x12, x12, x19;                  \
        adcs    x13, x13, x20;                  \
        mov     x14, #-4294967295;              \
        mov     x15, #4294967295;               \
        csel    x14, x14, xzr, cs;              \
        csel    x15, x15, xzr, cs;              \
        cset    x16, cs;                        \
        adds    x2, x2, x14;                    \
        adcs    x9, x9, x15;                    \
        adcs    x10, x10, x16;                  \
        adcs    x11, x11, xzr;                  \
        adcs    x12, x12, xzr;                  \
        adc     x13, x13, xzr;                  \
        stp     x2, x9, [P0];                   \
        stp     x10, x11, [P0+16];              \
        stp     x12, x13, [P0+32]

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

S2N_BN_SYMBOL(p384_montjadd):

// Save regs and make room on stack for temporary variables

        stp     x19, x20, [sp, #-16]!
        stp     x21, x22, [sp, #-16]!
        stp     x23, x24, [sp, #-16]!
        stp     x25, x26, [sp, #-16]!
        sub     sp, sp, NSPACE

// Move the input arguments to stable places

        mov     input_z, x0
        mov     input_x, x1
        mov     input_y, x2

// Main code, just a sequence of basic field operations
// 8 * multiply + 3 * square + 7 * subtract

        amontsqr_p384(z1sq,z_1)
        amontsqr_p384(z2sq,z_2)

        montmul_p384(y1a,z_2,y_1)
        montmul_p384(y2a,z_1,y_2)

        montmul_p384(x2a,z1sq,x_2)
        montmul_p384(x1a,z2sq,x_1)
        montmul_p384(y2a,z1sq,y2a)
        montmul_p384(y1a,z2sq,y1a)

        sub_p384(xd,x2a,x1a)
        sub_p384(yd,y2a,y1a)

        amontsqr_p384(zz,xd)
        montsqr_p384(ww,yd)

        montmul_p384(zzx1,zz,x1a)
        montmul_p384(zzx2,zz,x2a)

        sub_p384(x_3,ww,zzx1)
        sub_p384(t1,zzx2,zzx1)

        montmul_p384(xd,xd,z_1)

        sub_p384(x_3,x_3,zzx2)

        sub_p384(t2,zzx1,x_3)

        montmul_p384(t1,t1,y1a)
        montmul_p384(z_3,xd,z_2)
        montmul_p384(t2,yd,t2)

        sub_p384(y_3,t2,t1)

// Restore stack and registers

        add     sp, sp, NSPACE

        ldp     x25, x26, [sp], 16
        ldp     x23, x24, [sp], 16
        ldp     x21, x22, [sp], 16
        ldp     x19, x20, [sp], 16

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
