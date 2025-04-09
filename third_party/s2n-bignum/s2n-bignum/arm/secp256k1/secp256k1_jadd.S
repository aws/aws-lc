// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point addition on SECG curve secp256k1 in Jacobian coordinates
//
//    extern void secp256k1_jadd
//      (uint64_t p3[static 12],uint64_t p1[static 12],uint64_t p2[static 12]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples.
// A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3).
// It is assumed that all coordinates of the input points p1 and p2 are
// fully reduced mod p_256k1, that both z coordinates are nonzero and
// that neither p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents
// the same affine point as".
//
// Standard ARM ABI: X0 = p3, X1 = p1, X2 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(secp256k1_jadd)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(secp256k1_jadd)

        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 32

// Stable homes for input arguments during main code sequence

#define input_z x19
#define input_x x20
#define input_y x21

// The magic constant 2^256 - p_256k1

#define pconst x17

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

#define NSPACE (NUMSIZE*7)

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

// Corresponds exactly to bignum_sub_p256k1

#define sub_p256k1(P0,P1,P2)                    \
        ldp     x5, x6, [P1];                   \
        ldp     x4, x3, [P2];                   \
        subs    x5, x5, x4;                     \
        sbcs    x6, x6, x3;                     \
        ldp     x7, x8, [P1+16];                \
        ldp     x4, x3, [P2+16];                \
        sbcs    x7, x7, x4;                     \
        sbcs    x8, x8, x3;                     \
        mov     x4, #0x3d1;                     \
        orr     x3, x4, #0x100000000;           \
        csel    x3, x3, xzr, cc;                \
        subs    x5, x5, x3;                     \
        sbcs    x6, x6, xzr;                    \
        sbcs    x7, x7, xzr;                    \
        sbc     x8, x8, xzr;                    \
        stp     x5, x6, [P0];                   \
        stp     x7, x8, [P0+16]

S2N_BN_SYMBOL(secp256k1_jadd):

// Save registers and make room on stack for temporary variables

        sub     sp, sp, NSPACE+32
        stp     x19, x20, [sp, NSPACE]
        stp     x21, x22, [sp, NSPACE+16]

// Move the input arguments to stable place

        mov     input_z, x0
        mov     input_x, x1
        mov     input_y, x2

// Set up pconst =  4294968273, so p_256k1 = 2^256 - pconst

        mov     pconst, #977
        orr     pconst, pconst, #0x100000000

// Main code, just a sequence of basic field operations

        sqr_p256k1(z1sq,z_1)
        sqr_p256k1(z2sq,z_2)

        mul_p256k1(y1a,z_2,y_1)
        mul_p256k1(y2a,z_1,y_2)

        mul_p256k1(x2a,z1sq,x_2)
        mul_p256k1(x1a,z2sq,x_1)
        mul_p256k1(y2a,z1sq,y2a)
        mul_p256k1(y1a,z2sq,y1a)

        sub_p256k1(xd,x2a,x1a)
        sub_p256k1(yd,y2a,y1a)

        sqr_p256k1(zz,xd)
        sqr_p256k1(ww,yd)

        mul_p256k1(zzx1,zz,x1a)
        mul_p256k1(zzx2,zz,x2a)

        sub_p256k1(resx,ww,zzx1)
        sub_p256k1(t1,zzx2,zzx1)

        mul_p256k1(xd,xd,z_1)

        sub_p256k1(resx,resx,zzx2)

        sub_p256k1(t2,zzx1,resx)

        mul_p256k1(t1,t1,y1a)
        mul_p256k1(resz,xd,z_2)
        mul_p256k1(t2,yd,t2)

        sub_p256k1(resy,t2,t1)

// Load in the z coordinates of the inputs to check for P1 = 0 and P2 = 0
// The condition codes get set by a comparison (P2 != 0) - (P1 != 0)
// So  "HI" <=> CF /\ ~ZF <=> P1 = 0 /\ ~(P2 = 0)
// and "LO" <=> ~CF       <=> ~(P1 = 0) /\ P2 = 0

        ldp     x0, x1, [z_1]
        ldp     x2, x3, [z_1+16]

        orr     x12, x0, x1
        orr     x13, x2, x3
        orr     x12, x12, x13
        cmp     x12, xzr
        cset    x12, ne

        ldp     x4, x5, [z_2]
        ldp     x6, x7, [z_2+16]

        orr     x13, x4, x5
        orr     x14, x6, x7
        orr     x13, x13, x14
        cmp     x13, xzr
        cset    x13, ne

        cmp     x13, x12

// Multiplex the outputs accordingly, re-using the z's in registers

        ldp     x8, x9, [resz]
        csel    x8, x0, x8, lo
        csel    x9, x1, x9, lo
        csel    x8, x4, x8, hi
        csel    x9, x5, x9, hi
        ldp     x10, x11, [resz+16]
        csel    x10, x2, x10, lo
        csel    x11, x3, x11, lo
        csel    x10, x6, x10, hi
        csel    x11, x7, x11, hi

        ldp     x12, x13, [x_1]
        ldp     x0, x1, [resx]
        csel    x0, x12, x0, lo
        csel    x1, x13, x1, lo
        ldp     x12, x13, [x_2]
        csel    x0, x12, x0, hi
        csel    x1, x13, x1, hi

        ldp     x12, x13, [x_1+16]
        ldp     x2, x3, [resx+16]
        csel    x2, x12, x2, lo
        csel    x3, x13, x3, lo
        ldp     x12, x13, [x_2+16]
        csel    x2, x12, x2, hi
        csel    x3, x13, x3, hi

        ldp     x12, x13, [y_1]
        ldp     x4, x5, [resy]
        csel    x4, x12, x4, lo
        csel    x5, x13, x5, lo
        ldp     x12, x13, [y_2]
        csel    x4, x12, x4, hi
        csel    x5, x13, x5, hi

        ldp     x12, x13, [y_1+16]
        ldp     x6, x7, [resy+16]
        csel    x6, x12, x6, lo
        csel    x7, x13, x7, lo
        ldp     x12, x13, [y_2+16]
        csel    x6, x12, x6, hi
        csel    x7, x13, x7, hi

// Finally store back the multiplexed values

        stp     x0, x1, [x_3]
        stp     x2, x3, [x_3+16]
        stp     x4, x5, [y_3]
        stp     x6, x7, [y_3+16]
        stp     x8, x9, [z_3]
        stp     x10, x11, [z_3+16]

// Restore stack and return

        ldp     x19, x20, [sp, NSPACE]
        ldp     x21, x22, [sp, NSPACE+16]
        add     sp, sp, NSPACE+32
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
