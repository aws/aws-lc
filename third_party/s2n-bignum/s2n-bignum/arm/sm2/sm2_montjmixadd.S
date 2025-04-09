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

#define input_z x17
#define input_x x19
#define input_y x20

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
#define resx sp, #(NUMSIZE*0)

#define yd sp, #(NUMSIZE*1)
#define y2a sp, #(NUMSIZE*1)

#define x2a sp, #(NUMSIZE*2)
#define zzx2 sp, #(NUMSIZE*2)

#define zz sp, #(NUMSIZE*3)
#define t1 sp, #(NUMSIZE*3)

#define t2 sp, #(NUMSIZE*4)
#define zzx1 sp, #(NUMSIZE*4)
#define resy sp, #(NUMSIZE*4)

#define xd sp, #(NUMSIZE*5)
#define resz sp, #(NUMSIZE*5)

#define NSPACE (NUMSIZE*6)

// Corresponds to bignum_montmul_sm2 with x0 in place of x17

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
        adcs    x0, x12, x14;                   \
        adcs    x14, x14, xzr;                  \
        adds    x12, x12, x16;                  \
        adcs    x13, x13, x0;                   \
        adcs    x14, x14, xzr;                  \
        subs    x15, x3, x4;                    \
        cneg    x15, x15, lo;                   \
        csetm   x1, lo;                         \
        subs    x0, x8, x7;                     \
        cneg    x0, x0, lo;                     \
        mul     x16, x15, x0;                   \
        umulh   x0, x15, x0;                    \
        cinv    x1, x1, lo;                     \
        eor     x16, x16, x1;                   \
        eor     x0, x0, x1;                     \
        cmn     x1, #1;                         \
        adcs    x12, x12, x16;                  \
        adcs    x13, x13, x0;                   \
        adc     x14, x14, x1;                   \
        lsl     x16, x11, #32;                  \
        lsr     x15, x11, #32;                  \
        subs    x1, x16, x11;                   \
        sbc     x0, x15, xzr;                   \
        subs    x12, x12, x1;                   \
        sbcs    x13, x13, x0;                   \
        sbcs    x14, x14, x16;                  \
        sbc     x11, x11, x15;                  \
        lsl     x16, x12, #32;                  \
        lsr     x15, x12, #32;                  \
        subs    x1, x16, x12;                   \
        sbc     x0, x15, xzr;                   \
        subs    x13, x13, x1;                   \
        sbcs    x14, x14, x0;                   \
        sbcs    x11, x11, x16;                  \
        sbc     x12, x12, x15;                  \
        stp     x13, x14, [P0];                 \
        stp     x11, x12, [P0+16];              \
        mul     x11, x5, x9;                    \
        mul     x13, x6, x10;                   \
        umulh   x12, x5, x9;                    \
        adds    x16, x11, x13;                  \
        umulh   x14, x6, x10;                   \
        adcs    x0, x12, x14;                   \
        adcs    x14, x14, xzr;                  \
        adds    x12, x12, x16;                  \
        adcs    x13, x13, x0;                   \
        adcs    x14, x14, xzr;                  \
        subs    x15, x5, x6;                    \
        cneg    x15, x15, lo;                   \
        csetm   x1, lo;                         \
        subs    x0, x10, x9;                    \
        cneg    x0, x0, lo;                     \
        mul     x16, x15, x0;                   \
        umulh   x0, x15, x0;                    \
        cinv    x1, x1, lo;                     \
        eor     x16, x16, x1;                   \
        eor     x0, x0, x1;                     \
        cmn     x1, #1;                         \
        adcs    x12, x12, x16;                  \
        adcs    x13, x13, x0;                   \
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
        adcs    x0, x12, x14;                   \
        adcs    x14, x14, xzr;                  \
        adds    x12, x12, x16;                  \
        adcs    x13, x13, x0;                   \
        adcs    x14, x14, xzr;                  \
        subs    x3, x3, x4;                     \
        cneg    x3, x3, lo;                     \
        csetm   x4, lo;                         \
        subs    x0, x8, x7;                     \
        cneg    x0, x0, lo;                     \
        mul     x16, x3, x0;                    \
        umulh   x0, x3, x0;                     \
        cinv    x4, x4, lo;                     \
        eor     x16, x16, x4;                   \
        eor     x0, x0, x4;                     \
        cmn     x4, #1;                         \
        adcs    x12, x12, x16;                  \
        adcs    x13, x13, x0;                   \
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
        sbc     x0, x15, xzr;                   \
        subs    x12, x12, x1;                   \
        sbcs    x13, x13, x0;                   \
        sbcs    x14, x14, x16;                  \
        sbc     x11, x11, x15;                  \
        lsl     x16, x12, #32;                  \
        lsr     x15, x12, #32;                  \
        subs    x1, x16, x12;                   \
        sbc     x0, x15, xzr;                   \
        subs    x13, x13, x1;                   \
        sbcs    x14, x14, x0;                   \
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

// Corresponds to bignum_montsqr_sm2 with x0 in place of x17

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
        umull   x0, w3, w3;                     \
        lsr     x11, x3, #32;                   \
        umull   x1, w11, w11;                   \
        umull   x11, w3, w11;                   \
        mul     x12, x2, x3;                    \
        umulh   x13, x2, x3;                    \
        adds    x0, x0, x11, lsl #33;           \
        lsr     x11, x11, #31;                  \
        adc     x1, x1, x11;                    \
        adds    x12, x12, x12;                  \
        adcs    x13, x13, x13;                  \
        adc     x1, x1, xzr;                    \
        adds    x16, x16, x12;                  \
        adcs    x0, x0, x13;                    \
        adc     x1, x1, xzr;                    \
        lsl     x12, x15, #32;                  \
        lsr     x11, x15, #32;                  \
        subs    x14, x12, x15;                  \
        sbc     x13, x11, xzr;                  \
        subs    x16, x16, x14;                  \
        sbcs    x0, x0, x13;                    \
        sbcs    x1, x1, x12;                    \
        sbc     x15, x15, x11;                  \
        lsl     x12, x16, #32;                  \
        lsr     x11, x16, #32;                  \
        subs    x14, x12, x16;                  \
        sbc     x13, x11, xzr;                  \
        subs    x0, x0, x14;                    \
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
        adds    x6, x6, x0;                     \
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

S2N_BN_SYMBOL(sm2_montjmixadd):

// Save regs and make room on stack for temporary variables

        stp     x19, x20, [sp, #-16]!
        sub     sp, sp, NSPACE

// Move the input arguments to stable places

        mov     input_z, x0
        mov     input_x, x1
        mov     input_y, x2

// Main code, just a sequence of basic field operations
// 8 * multiply + 3 * square + 7 * subtract

        montsqr_sm2(zp2,z_1)
        montmul_sm2(y2a,z_1,y_2)

        montmul_sm2(x2a,zp2,x_2)
        montmul_sm2(y2a,zp2,y2a)

        sub_sm2(xd,x2a,x_1)
        sub_sm2(yd,y2a,y_1)

        montsqr_sm2(zz,xd)
        montsqr_sm2(ww,yd)

        montmul_sm2(zzx1,zz,x_1)
        montmul_sm2(zzx2,zz,x2a)

        sub_sm2(resx,ww,zzx1)
        sub_sm2(t1,zzx2,zzx1)

        montmul_sm2(resz,xd,z_1)

        sub_sm2(resx,resx,zzx2)

        sub_sm2(t2,zzx1,resx)

        montmul_sm2(t1,t1,y_1)
        montmul_sm2(t2,yd,t2)

        sub_sm2(resy,t2,t1)

// Test if z_1 = 0 to decide if p1 = 0 (up to projective equivalence)

        ldp     x0, x1, [z_1]
        ldp     x2, x3, [z_1+16]
        orr     x4, x0, x1
        orr     x5, x2, x3
        orr     x4, x4, x5
        cmp     x4, xzr

// Multiplex: if p1 <> 0 just copy the computed result from the staging area.
// If p1 = 0 then return the point p2 augmented with a z = 1 coordinate (in
// Montgomery form so not the simple constant 1 but rather 2^256 - p_sm2),
// hence giving 0 + p2 = p2 for the final result.

        ldp     x0, x1, [resx]
        ldp     x12, x13, [x_2]
        csel    x0, x0, x12, ne
        csel    x1, x1, x13, ne
        ldp     x2, x3, [resx+16]
        ldp     x12, x13, [x_2+16]
        csel    x2, x2, x12, ne
        csel    x3, x3, x13, ne

        ldp     x4, x5, [resy]
        ldp     x12, x13, [y_2]
        csel    x4, x4, x12, ne
        csel    x5, x5, x13, ne
        ldp     x6, x7, [resy+16]
        ldp     x12, x13, [y_2+16]
        csel    x6, x6, x12, ne
        csel    x7, x7, x13, ne

        ldp     x8, x9, [resz]
        mov     x12, #0x0000000000000001
        mov     x13, #0x00000000ffffffff
        csel    x8, x8, x12, ne
        csel    x9, x9, x13, ne
        ldp     x10, x11, [resz+16]
        mov     x13, #0x0000000100000000
        csel    x10, x10, xzr, ne
        csel    x11, x11, x13, ne

        stp     x0, x1, [x_3]
        stp     x2, x3, [x_3+16]
        stp     x4, x5, [y_3]
        stp     x6, x7, [y_3+16]
        stp     x8, x9, [z_3]
        stp     x10, x11, [z_3+16]

// Restore registers and return

        add     sp, sp, NSPACE
        ldp     x19, x20, [sp], 16
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
