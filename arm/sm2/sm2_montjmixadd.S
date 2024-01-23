// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point mixed addition on GM/T 0003-2012 curve SM2 in Montgomery-Jacobian coordinates
//
//    extern void sm2_montjmixadd
//      (uint64_t p3[static 12],uint64_t p1[static 12],uint64_t p2[static 8]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_sm2.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
// The "mixed" part means that p2 only has x and y coordinates, with the
// implicit z coordinate assumed to be the identity.
//
// Standard ARM ABI: X0 = p3, X1 = p1, X2 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sm2_montjmixadd)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sm2_montjmixadd)

        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 32

// Stable homes for input arguments during main code sequence

#define input_z x15
#define input_x x16
#define input_y x17

// Pointer-offset pairs for inputs and outputs

#define x_1 input_x, #0
#define y_1 input_x, #NUMSIZE
#define z_1 input_x, #(2*NUMSIZE)

#define x_2 input_y, #0
#define y_2 input_y, #NUMSIZE

#define x_3 input_z, #0
#define y_3 input_z, #NUMSIZE
#define z_3 input_z, #(2*NUMSIZE)

// Pointer-offset pairs for temporaries, with some aliasing
// NSPACE is the total stack needed for these temporaries

#define zp2 sp, #(NUMSIZE*0)
#define ww sp, #(NUMSIZE*0)

#define yd sp, #(NUMSIZE*1)
#define y2a sp, #(NUMSIZE*1)

#define x2a sp, #(NUMSIZE*2)
#define zzx2 sp, #(NUMSIZE*2)

#define zz sp, #(NUMSIZE*3)
#define t1 sp, #(NUMSIZE*3)

#define t2 sp, #(NUMSIZE*4)
#define zzx1 sp, #(NUMSIZE*4)

#define xd sp, #(NUMSIZE*5)

#define NSPACE (NUMSIZE*6)

// Corresponds to bignum_montmul_sm2_alt except for registers

#define montmul_sm2(P0,P1,P2)                   \
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
        lsl     x11, x12, #32;                  \
        lsr     x6, x12, #32;                   \
        subs    x8, x11, x12;                   \
        sbc     x7, x6, xzr;                    \
        subs    x13, x13, x8;                   \
        sbcs    x14, x14, x7;                   \
        sbcs    x0, x0, x11;                    \
        sbc     x12, x12, x6;                   \
        lsl     x11, x13, #32;                  \
        lsr     x6, x13, #32;                   \
        subs    x8, x11, x13;                   \
        sbc     x7, x6, xzr;                    \
        subs    x14, x14, x8;                   \
        sbcs    x0, x0, x7;                     \
        sbcs    x12, x12, x11;                  \
        sbc     x13, x13, x6;                   \
        lsl     x11, x14, #32;                  \
        lsr     x6, x14, #32;                   \
        subs    x8, x11, x14;                   \
        sbc     x7, x6, xzr;                    \
        subs    x0, x0, x8;                     \
        sbcs    x12, x12, x7;                   \
        sbcs    x13, x13, x11;                  \
        sbc     x14, x14, x6;                   \
        lsl     x11, x0, #32;                   \
        lsr     x6, x0, #32;                    \
        subs    x8, x11, x0;                    \
        sbc     x7, x6, xzr;                    \
        subs    x12, x12, x8;                   \
        sbcs    x13, x13, x7;                   \
        sbcs    x14, x14, x11;                  \
        sbc     x0, x0, x6;                     \
        adds    x12, x12, x1;                   \
        adcs    x13, x13, x3;                   \
        adcs    x14, x14, x4;                   \
        adcs    x0, x0, x5;                     \
        cset    x8, cs;                         \
        mov     x11, #0xffffffff00000000;       \
        mov     x6, #0xfffffffeffffffff;        \
        adds    x1, x12, #0x1;                  \
        sbcs    x3, x13, x11;                   \
        adcs    x4, x14, xzr;                   \
        sbcs    x5, x0, x6;                     \
        sbcs    xzr, x8, xzr;                   \
        csel    x12, x12, x1, cc;               \
        csel    x13, x13, x3, cc;               \
        csel    x14, x14, x4, cc;               \
        csel    x0, x0, x5, cc;                 \
        stp     x12, x13, [P0];                 \
        stp     x14, x0, [P0+16]

// Corresponds to bignum_montsqr_sm2_alt exactly

#define montsqr_sm2(P0,P1)                      \
        ldp     x2, x3, [P1];                   \
        mul     x9, x2, x3;                     \
        umulh   x10, x2, x3;                    \
        ldp     x4, x5, [P1+16];                \
        mul     x11, x2, x5;                    \
        umulh   x12, x2, x5;                    \
        mul     x6, x2, x4;                     \
        umulh   x7, x2, x4;                     \
        adds    x10, x10, x6;                   \
        adcs    x11, x11, x7;                   \
        mul     x6, x3, x4;                     \
        umulh   x7, x3, x4;                     \
        adc     x7, x7, xzr;                    \
        adds    x11, x11, x6;                   \
        mul     x13, x4, x5;                    \
        umulh   x14, x4, x5;                    \
        adcs    x12, x12, x7;                   \
        mul     x6, x3, x5;                     \
        umulh   x7, x3, x5;                     \
        adc     x7, x7, xzr;                    \
        adds    x12, x12, x6;                   \
        adcs    x13, x13, x7;                   \
        adc     x14, x14, xzr;                  \
        adds    x9, x9, x9;                     \
        adcs    x10, x10, x10;                  \
        adcs    x11, x11, x11;                  \
        adcs    x12, x12, x12;                  \
        adcs    x13, x13, x13;                  \
        adcs    x14, x14, x14;                  \
        cset    x7, cs;                         \
        umulh   x6, x2, x2;                     \
        mul     x8, x2, x2;                     \
        adds    x9, x9, x6;                     \
        mul     x6, x3, x3;                     \
        adcs    x10, x10, x6;                   \
        umulh   x6, x3, x3;                     \
        adcs    x11, x11, x6;                   \
        mul     x6, x4, x4;                     \
        adcs    x12, x12, x6;                   \
        umulh   x6, x4, x4;                     \
        adcs    x13, x13, x6;                   \
        mul     x6, x5, x5;                     \
        adcs    x14, x14, x6;                   \
        umulh   x6, x5, x5;                     \
        adc     x7, x7, x6;                     \
        lsl     x4, x8, #32;                    \
        lsr     x5, x8, #32;                    \
        subs    x2, x4, x8;                     \
        sbc     x3, x5, xzr;                    \
        subs    x9, x9, x2;                     \
        sbcs    x10, x10, x3;                   \
        sbcs    x11, x11, x4;                   \
        sbc     x8, x8, x5;                     \
        lsl     x4, x9, #32;                    \
        lsr     x5, x9, #32;                    \
        subs    x2, x4, x9;                     \
        sbc     x3, x5, xzr;                    \
        subs    x10, x10, x2;                   \
        sbcs    x11, x11, x3;                   \
        sbcs    x8, x8, x4;                     \
        sbc     x9, x9, x5;                     \
        lsl     x4, x10, #32;                   \
        lsr     x5, x10, #32;                   \
        subs    x2, x4, x10;                    \
        sbc     x3, x5, xzr;                    \
        subs    x11, x11, x2;                   \
        sbcs    x8, x8, x3;                     \
        sbcs    x9, x9, x4;                     \
        sbc     x10, x10, x5;                   \
        lsl     x4, x11, #32;                   \
        lsr     x5, x11, #32;                   \
        subs    x2, x4, x11;                    \
        sbc     x3, x5, xzr;                    \
        subs    x8, x8, x2;                     \
        sbcs    x9, x9, x3;                     \
        sbcs    x10, x10, x4;                   \
        sbc     x11, x11, x5;                   \
        adds    x8, x8, x12;                    \
        adcs    x9, x9, x13;                    \
        adcs    x10, x10, x14;                  \
        adcs    x11, x11, x7;                   \
        cset    x2, cs;                         \
        mov     x3, #0xffffffff00000000;        \
        mov     x5, #0xfffffffeffffffff;        \
        adds    x12, x8, #0x1;                  \
        sbcs    x13, x9, x3;                    \
        adcs    x14, x10, xzr;                  \
        sbcs    x7, x11, x5;                    \
        sbcs    xzr, x2, xzr;                   \
        csel    x8, x8, x12, cc;                \
        csel    x9, x9, x13, cc;                \
        csel    x10, x10, x14, cc;              \
        csel    x11, x11, x7, cc;               \
        stp     x8, x9, [P0];                   \
        stp     x10, x11, [P0+16]

// Almost-Montgomery variant which we use when an input to other muls
// with the other argument fully reduced (which is always safe).

#define amontsqr_sm2(P0,P1)                     \
        ldp     x2, x3, [P1];                   \
        mul     x9, x2, x3;                     \
        umulh   x10, x2, x3;                    \
        ldp     x4, x5, [P1+16];                \
        mul     x11, x2, x5;                    \
        umulh   x12, x2, x5;                    \
        mul     x6, x2, x4;                     \
        umulh   x7, x2, x4;                     \
        adds    x10, x10, x6;                   \
        adcs    x11, x11, x7;                   \
        mul     x6, x3, x4;                     \
        umulh   x7, x3, x4;                     \
        adc     x7, x7, xzr;                    \
        adds    x11, x11, x6;                   \
        mul     x13, x4, x5;                    \
        umulh   x14, x4, x5;                    \
        adcs    x12, x12, x7;                   \
        mul     x6, x3, x5;                     \
        umulh   x7, x3, x5;                     \
        adc     x7, x7, xzr;                    \
        adds    x12, x12, x6;                   \
        adcs    x13, x13, x7;                   \
        adc     x14, x14, xzr;                  \
        adds    x9, x9, x9;                     \
        adcs    x10, x10, x10;                  \
        adcs    x11, x11, x11;                  \
        adcs    x12, x12, x12;                  \
        adcs    x13, x13, x13;                  \
        adcs    x14, x14, x14;                  \
        cset    x7, cs;                         \
        umulh   x6, x2, x2;                     \
        mul     x8, x2, x2;                     \
        adds    x9, x9, x6;                     \
        mul     x6, x3, x3;                     \
        adcs    x10, x10, x6;                   \
        umulh   x6, x3, x3;                     \
        adcs    x11, x11, x6;                   \
        mul     x6, x4, x4;                     \
        adcs    x12, x12, x6;                   \
        umulh   x6, x4, x4;                     \
        adcs    x13, x13, x6;                   \
        mul     x6, x5, x5;                     \
        adcs    x14, x14, x6;                   \
        umulh   x6, x5, x5;                     \
        adc     x7, x7, x6;                     \
        lsl     x4, x8, #32;                    \
        lsr     x5, x8, #32;                    \
        subs    x2, x4, x8;                     \
        sbc     x3, x5, xzr;                    \
        subs    x9, x9, x2;                     \
        sbcs    x10, x10, x3;                   \
        sbcs    x11, x11, x4;                   \
        sbc     x8, x8, x5;                     \
        lsl     x4, x9, #32;                    \
        lsr     x5, x9, #32;                    \
        subs    x2, x4, x9;                     \
        sbc     x3, x5, xzr;                    \
        subs    x10, x10, x2;                   \
        sbcs    x11, x11, x3;                   \
        sbcs    x8, x8, x4;                     \
        sbc     x9, x9, x5;                     \
        lsl     x4, x10, #32;                   \
        lsr     x5, x10, #32;                   \
        subs    x2, x4, x10;                    \
        sbc     x3, x5, xzr;                    \
        subs    x11, x11, x2;                   \
        sbcs    x8, x8, x3;                     \
        sbcs    x9, x9, x4;                     \
        sbc     x10, x10, x5;                   \
        lsl     x4, x11, #32;                   \
        lsr     x5, x11, #32;                   \
        subs    x2, x4, x11;                    \
        sbc     x3, x5, xzr;                    \
        subs    x8, x8, x2;                     \
        sbcs    x9, x9, x3;                     \
        sbcs    x10, x10, x4;                   \
        sbc     x11, x11, x5;                   \
        adds    x8, x8, x12;                    \
        adcs    x9, x9, x13;                    \
        adcs    x10, x10, x14;                  \
        adcs    x11, x11, x7;                   \
        csetm   x2, cs;                         \
        subs    x8, x8, x2;                     \
        and     x3, x2, #0xffffffff00000000;    \
        sbcs    x9, x9, x3;                     \
        and     x5, x2, #0xfffffffeffffffff;    \
        sbcs    x10, x10, x2;                   \
        sbc     x11, x11, x5;                   \
        stp     x8, x9, [P0];                   \
        stp     x10, x11, [P0+16]

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

S2N_BN_SYMBOL(sm2_montjmixadd):

// Make room on stack for temporary variables
// Move the input arguments to stable places

        sub     sp, sp, NSPACE

        mov     input_z, x0
        mov     input_x, x1
        mov     input_y, x2

// Main code, just a sequence of basic field operations
// 8 * multiply + 3 * square + 7 * subtract

        amontsqr_sm2(zp2,z_1)
        montmul_sm2(y2a,z_1,y_2)

        montmul_sm2(x2a,zp2,x_2)
        montmul_sm2(y2a,zp2,y2a)

        sub_sm2(xd,x2a,x_1)
        sub_sm2(yd,y2a,y_1)

        amontsqr_sm2(zz,xd)
        montsqr_sm2(ww,yd)

        montmul_sm2(zzx1,zz,x_1)
        montmul_sm2(zzx2,zz,x2a)

        sub_sm2(x_3,ww,zzx1)
        sub_sm2(t1,zzx2,zzx1)

        montmul_sm2(z_3,xd,z_1)

        sub_sm2(x_3,x_3,zzx2)

        sub_sm2(t2,zzx1,x_3)

        montmul_sm2(t1,t1,y_1)
        montmul_sm2(t2,yd,t2)

        sub_sm2(y_3,t2,t1)

// Restore stack and return

        add     sp, sp, NSPACE

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
