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

#define input_z x15
#define input_x x16
#define input_y x17

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

// Corresponds exactly to bignum_mul_p256k1_alt

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
        mov     x7, #0x3d1;                     \
        orr     x7, x7, #0x100000000;           \
        mul     x11, x7, x1;                    \
        umulh   x9, x7, x1;                     \
        adds    x12, x12, x11;                  \
        mul     x11, x7, x3;                    \
        umulh   x3, x7, x3;                     \
        adcs    x13, x13, x11;                  \
        mul     x11, x7, x4;                    \
        umulh   x4, x7, x4;                     \
        adcs    x14, x14, x11;                  \
        mul     x11, x7, x5;                    \
        umulh   x5, x7, x5;                     \
        adcs    x0, x0, x11;                    \
        cset    x1, cs;                         \
        adds    x13, x13, x9;                   \
        adcs    x14, x14, x3;                   \
        adcs    x0, x0, x4;                     \
        adc     x1, x1, x5;                     \
        add     x8, x1, #0x1;                   \
        mul     x11, x7, x8;                    \
        umulh   x9, x7, x8;                     \
        adds    x12, x12, x11;                  \
        adcs    x13, x13, x9;                   \
        adcs    x14, x14, xzr;                  \
        adcs    x0, x0, xzr;                    \
        csel    x7, x7, xzr, cc;                \
        subs    x12, x12, x7;                   \
        sbcs    x13, x13, xzr;                  \
        sbcs    x14, x14, xzr;                  \
        sbc     x0, x0, xzr;                    \
        stp     x12, x13, [P0];                 \
        stp     x14, x0, [P0+16]

// Corresponds exactly to bignum_sqr_p256k1_alt

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
        mov     x3, #0x3d1;                     \
        orr     x3, x3, #0x100000000;           \
        mul     x7, x3, x12;                    \
        umulh   x4, x3, x12;                    \
        adds    x8, x8, x7;                     \
        mul     x7, x3, x13;                    \
        umulh   x13, x3, x13;                   \
        adcs    x9, x9, x7;                     \
        mul     x7, x3, x14;                    \
        umulh   x14, x3, x14;                   \
        adcs    x10, x10, x7;                   \
        mul     x7, x3, x6;                     \
        umulh   x6, x3, x6;                     \
        adcs    x11, x11, x7;                   \
        cset    x12, cs;                        \
        adds    x9, x9, x4;                     \
        adcs    x10, x10, x13;                  \
        adcs    x11, x11, x14;                  \
        adc     x12, x12, x6;                   \
        add     x2, x12, #0x1;                  \
        mul     x7, x3, x2;                     \
        umulh   x6, x3, x2;                     \
        adds    x8, x8, x7;                     \
        adcs    x9, x9, x6;                     \
        adcs    x10, x10, xzr;                  \
        adcs    x11, x11, xzr;                  \
        csel    x3, x3, xzr, cc;                \
        subs    x8, x8, x3;                     \
        sbcs    x9, x9, xzr;                    \
        sbcs    x10, x10, xzr;                  \
        sbc     x11, x11, xzr;                  \
        stp     x8, x9, [P0];                   \
        stp     x10, x11, [P0+16]

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

// Make room on stack for temporary variables
// Move the input arguments to stable places

        sub     sp, sp, NSPACE

        mov     input_z, x0
        mov     input_x, x1
        mov     input_y, x2

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

        sub_p256k1(x_3,ww,zzx1)
        sub_p256k1(t1,zzx2,zzx1)

        mul_p256k1(xd,xd,z_1)

        sub_p256k1(x_3,x_3,zzx2)

        sub_p256k1(t2,zzx1,x_3)

        mul_p256k1(t1,t1,y1a)
        mul_p256k1(z_3,xd,z_2)
        mul_p256k1(t2,yd,t2)

        sub_p256k1(y_3,t2,t1)

// Restore stack and return

        add     sp, sp, NSPACE
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
