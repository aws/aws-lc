// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// Projective scalar multiplication, x coordinate only, for curve25519
// Inputs scalar[4], point[4]; output res[8]
//
// extern void curve25519_pxscalarmul
//   (uint64_t res[static 8],uint64_t scalar[static 4],uint64_t point[static 4])
//
// Given the X coordinate of an input point = (X,Y) on curve25519, which
// could also be part of a projective representation (X,Y,1) of the same
// point, returns a projective representation (X,Z) = scalar * point, where
// scalar is a 256-bit number. The corresponding affine form is (X/Z,Y'),
// X/Z meaning division modulo 2^255-19, and Y' not being computed by
// this function (nor is any Y coordinate of the input point used).
//
// Standard ARM ABI: X0 = res, X1 = scalar, X2 = point
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(curve25519_pxscalarmul)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(curve25519_pxscalarmul)

        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 32

// Stable homes for input arguments during main code sequence
// and additional registers for loop counter and swap flag

#define res x17
#define point x19
#define scalar x20
#define i x21
#define swap x22

// Pointers to input x coord (we don't use y or z) and output coords.

#define x point, #0
#define resx res, #0
#define resz res, #NUMSIZE

// Pointer-offset pairs for temporaries on stack with some aliasing.
// Both dmsn and dnsm need space for >= 5 digits, and we allocate 8

#define zm sp, #(0*NUMSIZE)
#define sm sp, #(0*NUMSIZE)
#define dpro sp, #(0*NUMSIZE)

#define sn sp, #(1*NUMSIZE)

#define dm sp, #(2*NUMSIZE)

#define zn sp, #(3*NUMSIZE)
#define dn sp, #(3*NUMSIZE)
#define e sp, #(3*NUMSIZE)

#define dmsn sp, #(4*NUMSIZE)
#define p sp, #(4*NUMSIZE)

#define xm sp, #(6*NUMSIZE)
#define dnsm sp, #(6*NUMSIZE)
#define spro sp, #(6*NUMSIZE)

#define xn sp, #(8*NUMSIZE)
#define s sp, #(8*NUMSIZE)

#define d sp, #(9*NUMSIZE)

// Total size to reserve on the stack

#define NSPACE (10*NUMSIZE)

// Macros wrapping up the basic field operation calls
// bignum_mul_p25519 and bignum_sqr_p25519.
// These two are only trivially different from pure
// function calls to those subroutines.

#define mul_p25519(p0,p1,p2)                    \
        ldp     x3, x4, [p1];                   \
        ldp     x5, x6, [p2];                   \
        mul     x7, x3, x5;                     \
        umulh   x8, x3, x5;                     \
        mul     x9, x4, x6;                     \
        umulh   x10, x4, x6;                    \
        subs    x4, x4, x3;                     \
        cneg    x4, x4, cc;                     \
        csetm   x16, cc;                        \
        adds    x9, x9, x8;                     \
        adc     x10, x10, xzr;                  \
        subs    x3, x5, x6;                     \
        cneg    x3, x3, cc;                     \
        cinv    x16, x16, cc;                   \
        mul     x15, x4, x3;                    \
        umulh   x3, x4, x3;                     \
        adds    x8, x7, x9;                     \
        adcs    x9, x9, x10;                    \
        adc     x10, x10, xzr;                  \
        cmn     x16, #0x1;                      \
        eor     x15, x15, x16;                  \
        adcs    x8, x15, x8;                    \
        eor     x3, x3, x16;                    \
        adcs    x9, x3, x9;                     \
        adc     x10, x10, x16;                  \
        ldp     x3, x4, [p1+16];                \
        ldp     x5, x6, [p2+16];                \
        mul     x11, x3, x5;                    \
        umulh   x12, x3, x5;                    \
        mul     x13, x4, x6;                    \
        umulh   x14, x4, x6;                    \
        subs    x4, x4, x3;                     \
        cneg    x4, x4, cc;                     \
        csetm   x16, cc;                        \
        adds    x13, x13, x12;                  \
        adc     x14, x14, xzr;                  \
        subs    x3, x5, x6;                     \
        cneg    x3, x3, cc;                     \
        cinv    x16, x16, cc;                   \
        mul     x15, x4, x3;                    \
        umulh   x3, x4, x3;                     \
        adds    x12, x11, x13;                  \
        adcs    x13, x13, x14;                  \
        adc     x14, x14, xzr;                  \
        cmn     x16, #0x1;                      \
        eor     x15, x15, x16;                  \
        adcs    x12, x15, x12;                  \
        eor     x3, x3, x16;                    \
        adcs    x13, x3, x13;                   \
        adc     x14, x14, x16;                  \
        ldp     x3, x4, [p1+16];                \
        ldp     x15, x16, [p1];                 \
        subs    x3, x3, x15;                    \
        sbcs    x4, x4, x16;                    \
        csetm   x16, cc;                        \
        ldp     x15, x0, [p2];                  \
        subs    x5, x15, x5;                    \
        sbcs    x6, x0, x6;                     \
        csetm   x0, cc;                         \
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
        cneg    x4, x4, cc;                     \
        csetm   x9, cc;                         \
        adds    x15, x15, x0;                   \
        adc     x1, x1, xzr;                    \
        subs    x6, x5, x6;                     \
        cneg    x6, x6, cc;                     \
        cinv    x9, x9, cc;                     \
        mul     x5, x4, x6;                     \
        umulh   x6, x4, x6;                     \
        adds    x0, x2, x15;                    \
        adcs    x15, x15, x1;                   \
        adc     x1, x1, xzr;                    \
        cmn     x9, #0x1;                       \
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
        cmn     x16, #0x1;                      \
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
        mov     x3, #0x26;                      \
        and     x5, x11, #0xffffffff;           \
        lsr     x4, x11, #32;                   \
        mul     x5, x3, x5;                     \
        mul     x4, x3, x4;                     \
        adds    x7, x7, x5;                     \
        and     x5, x12, #0xffffffff;           \
        lsr     x12, x12, #32;                  \
        mul     x5, x3, x5;                     \
        mul     x12, x3, x12;                   \
        adcs    x8, x8, x5;                     \
        and     x5, x13, #0xffffffff;           \
        lsr     x13, x13, #32;                  \
        mul     x5, x3, x5;                     \
        mul     x13, x3, x13;                   \
        adcs    x9, x9, x5;                     \
        and     x5, x14, #0xffffffff;           \
        lsr     x14, x14, #32;                  \
        mul     x5, x3, x5;                     \
        mul     x14, x3, x14;                   \
        adcs    x10, x10, x5;                   \
        cset    x11, cs;                        \
        lsl     x5, x4, #32;                    \
        adds    x7, x7, x5;                     \
        extr    x5, x12, x4, #32;               \
        adcs    x8, x8, x5;                     \
        extr    x5, x13, x12, #32;              \
        adcs    x9, x9, x5;                     \
        extr    x5, x14, x13, #32;              \
        adcs    x10, x10, x5;                   \
        lsr     x5, x14, #32;                   \
        adc     x11, x11, x5;                   \
        cmn     x10, x10;                       \
        orr     x10, x10, #0x8000000000000000;  \
        adc     x0, x11, x11;                   \
        mov     x3, #0x13;                      \
        madd    x5, x3, x0, x3;                 \
        adds    x7, x7, x5;                     \
        adcs    x8, x8, xzr;                    \
        adcs    x9, x9, xzr;                    \
        adcs    x10, x10, xzr;                  \
        csel    x3, x3, xzr, cc;                \
        subs    x7, x7, x3;                     \
        sbcs    x8, x8, xzr;                    \
        sbcs    x9, x9, xzr;                    \
        sbc     x10, x10, xzr;                  \
        and     x10, x10, #0x7fffffffffffffff;  \
        stp     x7, x8, [p0];                   \
        stp     x9, x10, [p0+16]

#define sqr_p25519(p0,p1)                       \
        ldp     x6, x7, [p1];                   \
        ldp     x10, x11, [p1+16];              \
        mul     x4, x6, x10;                    \
        mul     x9, x7, x11;                    \
        umulh   x12, x6, x10;                   \
        subs    x13, x6, x7;                    \
        cneg    x13, x13, cc;                   \
        csetm   x3, cc;                         \
        subs    x2, x11, x10;                   \
        cneg    x2, x2, cc;                     \
        mul     x8, x13, x2;                    \
        umulh   x2, x13, x2;                    \
        cinv    x3, x3, cc;                     \
        eor     x8, x8, x3;                     \
        eor     x2, x2, x3;                     \
        adds    x5, x4, x12;                    \
        adc     x12, x12, xzr;                  \
        umulh   x13, x7, x11;                   \
        adds    x5, x5, x9;                     \
        adcs    x12, x12, x13;                  \
        adc     x13, x13, xzr;                  \
        adds    x12, x12, x9;                   \
        adc     x13, x13, xzr;                  \
        cmn     x3, #0x1;                       \
        adcs    x5, x5, x8;                     \
        adcs    x12, x12, x2;                   \
        adc     x13, x13, x3;                   \
        adds    x4, x4, x4;                     \
        adcs    x5, x5, x5;                     \
        adcs    x12, x12, x12;                  \
        adcs    x13, x13, x13;                  \
        adc     x14, xzr, xzr;                  \
        mul     x2, x6, x6;                     \
        mul     x8, x7, x7;                     \
        mul     x15, x6, x7;                    \
        umulh   x3, x6, x6;                     \
        umulh   x9, x7, x7;                     \
        umulh   x16, x6, x7;                    \
        adds    x3, x3, x15;                    \
        adcs    x8, x8, x16;                    \
        adc     x9, x9, xzr;                    \
        adds    x3, x3, x15;                    \
        adcs    x8, x8, x16;                    \
        adc     x9, x9, xzr;                    \
        adds    x4, x4, x8;                     \
        adcs    x5, x5, x9;                     \
        adcs    x12, x12, xzr;                  \
        adcs    x13, x13, xzr;                  \
        adc     x14, x14, xzr;                  \
        mul     x6, x10, x10;                   \
        mul     x8, x11, x11;                   \
        mul     x15, x10, x11;                  \
        umulh   x7, x10, x10;                   \
        umulh   x9, x11, x11;                   \
        umulh   x16, x10, x11;                  \
        adds    x7, x7, x15;                    \
        adcs    x8, x8, x16;                    \
        adc     x9, x9, xzr;                    \
        adds    x7, x7, x15;                    \
        adcs    x8, x8, x16;                    \
        adc     x9, x9, xzr;                    \
        adds    x6, x6, x12;                    \
        adcs    x7, x7, x13;                    \
        adcs    x8, x8, x14;                    \
        adc     x9, x9, xzr;                    \
        mov     x10, #0x26;                     \
        and     x11, x6, #0xffffffff;           \
        lsr     x12, x6, #32;                   \
        mul     x11, x10, x11;                  \
        mul     x12, x10, x12;                  \
        adds    x2, x2, x11;                    \
        and     x11, x7, #0xffffffff;           \
        lsr     x7, x7, #32;                    \
        mul     x11, x10, x11;                  \
        mul     x7, x10, x7;                    \
        adcs    x3, x3, x11;                    \
        and     x11, x8, #0xffffffff;           \
        lsr     x8, x8, #32;                    \
        mul     x11, x10, x11;                  \
        mul     x8, x10, x8;                    \
        adcs    x4, x4, x11;                    \
        and     x11, x9, #0xffffffff;           \
        lsr     x9, x9, #32;                    \
        mul     x11, x10, x11;                  \
        mul     x9, x10, x9;                    \
        adcs    x5, x5, x11;                    \
        cset    x6, cs;                         \
        lsl     x11, x12, #32;                  \
        adds    x2, x2, x11;                    \
        extr    x11, x7, x12, #32;              \
        adcs    x3, x3, x11;                    \
        extr    x11, x8, x7, #32;               \
        adcs    x4, x4, x11;                    \
        extr    x11, x9, x8, #32;               \
        adcs    x5, x5, x11;                    \
        lsr     x11, x9, #32;                   \
        adc     x6, x6, x11;                    \
        cmn     x5, x5;                         \
        orr     x5, x5, #0x8000000000000000;    \
        adc     x13, x6, x6;                    \
        mov     x10, #0x13;                     \
        madd    x11, x10, x13, x10;             \
        adds    x2, x2, x11;                    \
        adcs    x3, x3, xzr;                    \
        adcs    x4, x4, xzr;                    \
        adcs    x5, x5, xzr;                    \
        csel    x10, x10, xzr, cc;              \
        subs    x2, x2, x10;                    \
        sbcs    x3, x3, xzr;                    \
        sbcs    x4, x4, xzr;                    \
        sbc     x5, x5, xzr;                    \
        and     x5, x5, #0x7fffffffffffffff;    \
        stp     x2, x3, [p0];                   \
        stp     x4, x5, [p0+16]

// Multiplication just giving a 5-digit result (actually < 39 * 2^256)
// by not doing anything beyond the first stage of reduction

#define mul_5(p0,p1,p2)                         \
        ldp     x3, x4, [p1];                   \
        ldp     x5, x6, [p2];                   \
        mul     x7, x3, x5;                     \
        umulh   x8, x3, x5;                     \
        mul     x9, x4, x6;                     \
        umulh   x10, x4, x6;                    \
        subs    x4, x4, x3;                     \
        cneg    x4, x4, cc;                     \
        csetm   x16, cc;                        \
        adds    x9, x9, x8;                     \
        adc     x10, x10, xzr;                  \
        subs    x3, x5, x6;                     \
        cneg    x3, x3, cc;                     \
        cinv    x16, x16, cc;                   \
        mul     x15, x4, x3;                    \
        umulh   x3, x4, x3;                     \
        adds    x8, x7, x9;                     \
        adcs    x9, x9, x10;                    \
        adc     x10, x10, xzr;                  \
        cmn     x16, #0x1;                      \
        eor     x15, x15, x16;                  \
        adcs    x8, x15, x8;                    \
        eor     x3, x3, x16;                    \
        adcs    x9, x3, x9;                     \
        adc     x10, x10, x16;                  \
        ldp     x3, x4, [p1+16];                \
        ldp     x5, x6, [p2+16];                \
        mul     x11, x3, x5;                    \
        umulh   x12, x3, x5;                    \
        mul     x13, x4, x6;                    \
        umulh   x14, x4, x6;                    \
        subs    x4, x4, x3;                     \
        cneg    x4, x4, cc;                     \
        csetm   x16, cc;                        \
        adds    x13, x13, x12;                  \
        adc     x14, x14, xzr;                  \
        subs    x3, x5, x6;                     \
        cneg    x3, x3, cc;                     \
        cinv    x16, x16, cc;                   \
        mul     x15, x4, x3;                    \
        umulh   x3, x4, x3;                     \
        adds    x12, x11, x13;                  \
        adcs    x13, x13, x14;                  \
        adc     x14, x14, xzr;                  \
        cmn     x16, #0x1;                      \
        eor     x15, x15, x16;                  \
        adcs    x12, x15, x12;                  \
        eor     x3, x3, x16;                    \
        adcs    x13, x3, x13;                   \
        adc     x14, x14, x16;                  \
        ldp     x3, x4, [p1+16];                \
        ldp     x15, x16, [p1];                 \
        subs    x3, x3, x15;                    \
        sbcs    x4, x4, x16;                    \
        csetm   x16, cc;                        \
        ldp     x15, x0, [p2];                  \
        subs    x5, x15, x5;                    \
        sbcs    x6, x0, x6;                     \
        csetm   x0, cc;                         \
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
        cneg    x4, x4, cc;                     \
        csetm   x9, cc;                         \
        adds    x15, x15, x0;                   \
        adc     x1, x1, xzr;                    \
        subs    x6, x5, x6;                     \
        cneg    x6, x6, cc;                     \
        cinv    x9, x9, cc;                     \
        mul     x5, x4, x6;                     \
        umulh   x6, x4, x6;                     \
        adds    x0, x2, x15;                    \
        adcs    x15, x15, x1;                   \
        adc     x1, x1, xzr;                    \
        cmn     x9, #0x1;                       \
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
        cmn     x16, #0x1;                      \
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
        mov     x3, #0x26;                      \
        and     x5, x11, #0xffffffff;           \
        lsr     x4, x11, #32;                   \
        mul     x5, x3, x5;                     \
        mul     x4, x3, x4;                     \
        adds    x7, x7, x5;                     \
        and     x5, x12, #0xffffffff;           \
        lsr     x12, x12, #32;                  \
        mul     x5, x3, x5;                     \
        mul     x12, x3, x12;                   \
        adcs    x8, x8, x5;                     \
        and     x5, x13, #0xffffffff;           \
        lsr     x13, x13, #32;                  \
        mul     x5, x3, x5;                     \
        mul     x13, x3, x13;                   \
        adcs    x9, x9, x5;                     \
        and     x5, x14, #0xffffffff;           \
        lsr     x14, x14, #32;                  \
        mul     x5, x3, x5;                     \
        mul     x14, x3, x14;                   \
        adcs    x10, x10, x5;                   \
        cset    x11, cs;                        \
        lsl     x5, x4, #32;                    \
        adds    x7, x7, x5;                     \
        extr    x5, x12, x4, #32;               \
        adcs    x8, x8, x5;                     \
        extr    x5, x13, x12, #32;              \
        adcs    x9, x9, x5;                     \
        extr    x5, x14, x13, #32;              \
        adcs    x10, x10, x5;                   \
        lsr     x5, x14, #32;                   \
        adc     x11, x11, x5;                   \
        stp     x7, x8, [p0];                   \
        stp     x9, x10, [p0+16];               \
        str     x11, [p0+32]

// Squaring just giving a result < 2 * p_25519, which is done by
// basically skipping the +1 in the quotient estimate and the final
// optional correction.

#define sqr_4(p0,p1)                            \
        ldp     x6, x7, [p1];                   \
        ldp     x10, x11, [p1+16];              \
        mul     x4, x6, x10;                    \
        mul     x9, x7, x11;                    \
        umulh   x12, x6, x10;                   \
        subs    x13, x6, x7;                    \
        cneg    x13, x13, cc;                   \
        csetm   x3, cc;                         \
        subs    x2, x11, x10;                   \
        cneg    x2, x2, cc;                     \
        mul     x8, x13, x2;                    \
        umulh   x2, x13, x2;                    \
        cinv    x3, x3, cc;                     \
        eor     x8, x8, x3;                     \
        eor     x2, x2, x3;                     \
        adds    x5, x4, x12;                    \
        adc     x12, x12, xzr;                  \
        umulh   x13, x7, x11;                   \
        adds    x5, x5, x9;                     \
        adcs    x12, x12, x13;                  \
        adc     x13, x13, xzr;                  \
        adds    x12, x12, x9;                   \
        adc     x13, x13, xzr;                  \
        cmn     x3, #0x1;                       \
        adcs    x5, x5, x8;                     \
        adcs    x12, x12, x2;                   \
        adc     x13, x13, x3;                   \
        adds    x4, x4, x4;                     \
        adcs    x5, x5, x5;                     \
        adcs    x12, x12, x12;                  \
        adcs    x13, x13, x13;                  \
        adc     x14, xzr, xzr;                  \
        mul     x2, x6, x6;                     \
        mul     x8, x7, x7;                     \
        mul     x15, x6, x7;                    \
        umulh   x3, x6, x6;                     \
        umulh   x9, x7, x7;                     \
        umulh   x16, x6, x7;                    \
        adds    x3, x3, x15;                    \
        adcs    x8, x8, x16;                    \
        adc     x9, x9, xzr;                    \
        adds    x3, x3, x15;                    \
        adcs    x8, x8, x16;                    \
        adc     x9, x9, xzr;                    \
        adds    x4, x4, x8;                     \
        adcs    x5, x5, x9;                     \
        adcs    x12, x12, xzr;                  \
        adcs    x13, x13, xzr;                  \
        adc     x14, x14, xzr;                  \
        mul     x6, x10, x10;                   \
        mul     x8, x11, x11;                   \
        mul     x15, x10, x11;                  \
        umulh   x7, x10, x10;                   \
        umulh   x9, x11, x11;                   \
        umulh   x16, x10, x11;                  \
        adds    x7, x7, x15;                    \
        adcs    x8, x8, x16;                    \
        adc     x9, x9, xzr;                    \
        adds    x7, x7, x15;                    \
        adcs    x8, x8, x16;                    \
        adc     x9, x9, xzr;                    \
        adds    x6, x6, x12;                    \
        adcs    x7, x7, x13;                    \
        adcs    x8, x8, x14;                    \
        adc     x9, x9, xzr;                    \
        mov     x10, #0x26;                     \
        and     x11, x6, #0xffffffff;           \
        lsr     x12, x6, #32;                   \
        mul     x11, x10, x11;                  \
        mul     x12, x10, x12;                  \
        adds    x2, x2, x11;                    \
        and     x11, x7, #0xffffffff;           \
        lsr     x7, x7, #32;                    \
        mul     x11, x10, x11;                  \
        mul     x7, x10, x7;                    \
        adcs    x3, x3, x11;                    \
        and     x11, x8, #0xffffffff;           \
        lsr     x8, x8, #32;                    \
        mul     x11, x10, x11;                  \
        mul     x8, x10, x8;                    \
        adcs    x4, x4, x11;                    \
        and     x11, x9, #0xffffffff;           \
        lsr     x9, x9, #32;                    \
        mul     x11, x10, x11;                  \
        mul     x9, x10, x9;                    \
        adcs    x5, x5, x11;                    \
        cset    x6, cs;                         \
        lsl     x11, x12, #32;                  \
        adds    x2, x2, x11;                    \
        extr    x11, x7, x12, #32;              \
        adcs    x3, x3, x11;                    \
        extr    x11, x8, x7, #32;               \
        adcs    x4, x4, x11;                    \
        extr    x11, x9, x8, #32;               \
        adcs    x5, x5, x11;                    \
        lsr     x11, x9, #32;                   \
        adc     x6, x6, x11;                    \
        cmn     x5, x5;                         \
        bic     x5, x5, #0x8000000000000000;    \
        adc     x13, x6, x6;                    \
        mov     x10, #0x13;                     \
        mul     x11, x13, x10;                  \
        adds    x2, x2, x11;                    \
        adcs    x3, x3, xzr;                    \
        adcs    x4, x4, xzr;                    \
        adc     x5, x5, xzr;                    \
        stp     x2, x3, [p0];                   \
        stp     x4, x5, [p0+16]

// Plain 4-digit add without any normalization
// With inputs < p_25519 (indeed < 2^255) it still gives a 4-digit result

#define add_4(p0,p1,p2)                         \
        ldp     x0, x1, [p1];                   \
        ldp     x4, x5, [p2];                   \
        adds    x0, x0, x4;                     \
        adcs    x1, x1, x5;                     \
        ldp     x2, x3, [p1+16];                \
        ldp     x6, x7, [p2+16];                \
        adcs    x2, x2, x6;                     \
        adcs    x3, x3, x7;                     \
        stp     x0, x1, [p0];                   \
        stp     x2, x3, [p0+16]

// Add 5-digit inputs and normalize to 4 digits

#define add5_4(p0,p1,p2)                        \
        ldp     x0, x1, [p1];                   \
        ldp     x4, x5, [p2];                   \
        adds    x0, x0, x4;                     \
        adcs    x1, x1, x5;                     \
        ldp     x2, x3, [p1+16];                \
        ldp     x6, x7, [p2+16];                \
        adcs    x2, x2, x6;                     \
        adcs    x3, x3, x7;                     \
        ldr     x4, [p1+32];                    \
        ldr     x5, [p2+32];                    \
        adc     x4, x4, x5;                     \
        cmn     x3, x3;                         \
        bic     x3, x3, #0x8000000000000000;    \
        adc     x8, x4, x4;                     \
        mov     x7, #19;                        \
        mul     x11, x7, x8;                    \
        adds    x0, x0, x11;                    \
        adcs    x1, x1, xzr;                    \
        adcs    x2, x2, xzr;                    \
        adc     x3, x3, xzr;                    \
        stp     x0, x1, [p0];                   \
        stp     x2, x3, [p0+16]

// Subtraction of a pair of numbers < p_25519 just sufficient
// to give a 4-digit result. It actually always does (x - z) + (2^255-19)
// which in turn is done by (x - z) - (2^255+19) discarding the 2^256
// implicitly

#define sub_4(p0,p1,p2)                         \
        ldp     x5, x6, [p1];                   \
        ldp     x4, x3, [p2];                   \
        subs    x5, x5, x4;                     \
        sbcs    x6, x6, x3;                     \
        ldp     x7, x8, [p1+16];                \
        ldp     x4, x3, [p2+16];                \
        sbcs    x7, x7, x4;                     \
        sbcs    x8, x8, x3;                     \
        mov     x3, #19;                        \
        subs    x5, x5, x3;                     \
        sbcs    x6, x6, xzr;                    \
        sbcs    x7, x7, xzr;                    \
        mov     x4, #0x8000000000000000;        \
        sbc     x8, x8, x4;                     \
        stp     x5, x6, [p0];                   \
        stp     x7, x8, [p0+16]

// Modular subtraction with double modulus 2 * p_25519 = 2^256 - 38

#define sub_twice4(p0,p1,p2)                    \
        ldp     x5, x6, [p1];                   \
        ldp     x4, x3, [p2];                   \
        subs    x5, x5, x4;                     \
        sbcs    x6, x6, x3;                     \
        ldp     x7, x8, [p1+16];                \
        ldp     x4, x3, [p2+16];                \
        sbcs    x7, x7, x4;                     \
        sbcs    x8, x8, x3;                     \
        mov     x4, #38;                        \
        csel    x3, x4, xzr, lo;                \
        subs    x5, x5, x3;                     \
        sbcs    x6, x6, xzr;                    \
        sbcs    x7, x7, xzr;                    \
        sbc     x8, x8, xzr;                    \
        stp     x5, x6, [p0];                   \
        stp     x7, x8, [p0+16]

// 5-digit subtraction with upward bias to make it positive, adding
// 1000 * (2^255 - 19) = 2^256 * 500 - 19000, then normalizing to 4 digits

#define sub5_4(p0,p1,p2)                        \
        ldp     x0, x1, [p1];                   \
        ldp     x4, x5, [p2];                   \
        subs    x0, x0, x4;                     \
        sbcs    x1, x1, x5;                     \
        ldp     x2, x3, [p1+16];                \
        ldp     x6, x7, [p2+16];                \
        sbcs    x2, x2, x6;                     \
        sbcs    x3, x3, x7;                     \
        ldr     x4, [p1+32];                    \
        ldr     x5, [p2+32];                    \
        sbc     x4, x4, x5;                     \
        mov     x7, -19000;                     \
        adds x0, x0, x7;                        \
        sbcs    x1, x1, xzr;                    \
        sbcs    x2, x2, xzr;                    \
        sbcs    x3, x3, xzr;                    \
        mov     x7, 499;                        \
        adc     x4, x4, x7;                     \
        cmn     x3, x3;                         \
        bic     x3, x3, #0x8000000000000000;    \
        adc     x8, x4, x4;                     \
        mov     x7, #19;                        \
        mul     x11, x7, x8;                    \
        adds    x0, x0, x11;                    \
        adcs    x1, x1, xzr;                    \
        adcs    x2, x2, xzr;                    \
        adc     x3, x3, xzr;                    \
        stp     x0, x1, [p0];                   \
        stp     x2, x3, [p0+16]

// Combined z = c * x + y with reduction only < 2 * p_25519
// where c is initially in the X1 register. It is assumed
// that 19 * (c * x + y) < 2^60 * 2^256 so we don't need a
// high mul in the final part.

#define cmadd_4(p0,p2,p3)                       \
        ldp     x7, x8, [p2];                   \
        ldp     x9, x10, [p2+16];               \
        mul     x3, x1, x7;                     \
        mul     x4, x1, x8;                     \
        mul     x5, x1, x9;                     \
        mul     x6, x1, x10;                    \
        umulh   x7, x1, x7;                     \
        umulh   x8, x1, x8;                     \
        umulh   x9, x1, x9;                     \
        umulh   x10, x1, x10;                   \
        adds    x4, x4, x7;                     \
        adcs    x5, x5, x8;                     \
        adcs    x6, x6, x9;                     \
        adc     x10, x10, xzr;                  \
        ldp     x7, x8, [p3];                   \
        adds    x3, x3, x7;                     \
        adcs    x4, x4, x8;                     \
        ldp     x7, x8, [p3+16];                \
        adcs    x5, x5, x7;                     \
        adcs    x6, x6, x8;                     \
        adc     x10, x10, xzr;                  \
        cmn     x6, x6;                         \
        bic     x6, x6, #0x8000000000000000;    \
        adc     x8, x10, x10;                   \
        mov     x9, #19;                        \
        mul     x7, x8, x9;                     \
        adds    x3, x3, x7;                     \
        adcs    x4, x4, xzr;                    \
        adcs    x5, x5, xzr;                    \
        adc     x6, x6, xzr;                    \
        stp     x3, x4, [p0];                   \
        stp     x5, x6, [p0+16]

// Multiplex: z := if NZ then x else y

#define mux_4(p0,p1,p2)                         \
        ldp     x0, x1, [p1];                   \
        ldp     x2, x3, [p2];                   \
        csel    x0, x0, x2, ne;                 \
        csel    x1, x1, x3, ne;                 \
        stp     x0, x1, [p0];                   \
        ldp     x0, x1, [p1+16];                \
        ldp     x2, x3, [p2+16];                \
        csel    x0, x0, x2, ne;                 \
        csel    x1, x1, x3, ne;                 \
        stp     x0, x1, [p0+16]

S2N_BN_SYMBOL(curve25519_pxscalarmul):

// Save regs and make room for temporaries

        stp     x19, x22, [sp, -16]!
        stp     x20, x21, [sp, -16]!
        sub     sp, sp, #NSPACE

// Move the input arguments to stable places

        mov     res, x0
        mov     scalar, x1
        mov     point, x2

// Initialize (xn,zn) = (1,0) and (xm,zm) = (x,1) with swap = 0

        mov     x2, #1
        stp     x2, xzr, [xn]
        stp     xzr, xzr, [xn+16]
        stp     xzr, xzr, [zn]
        stp     xzr, xzr, [zn+16]
        ldp     x0, x1, [x]
        stp     x0, x1, [xm]
        ldp     x0, x1, [x+16]
        stp     x0, x1, [xm+16]
        ldp     x0, x1, [x+32]
        stp     x2, xzr, [zm]
        stp     xzr, xzr, [zm+16]
        mov     swap, xzr

// The outer loop from i = 255, ..., i = 0 (inclusive)

        mov     i, #255

loop:

// sm = xm + zm; sn = xn + zn; dm = xm - zm; dn = xn - zn
// The adds don't need any normalization as they're fed to muls
// Just make sure the subs fit in 4 digits

        sub_4(dm, xm, zm)
        add_4(sn, xn, zn)
        sub_4(dn, xn, zn)
        add_4(sm, xm, zm)

// ADDING: dmsn = dm * sn; dnsm = sm * dn
// DOUBLING: mux d = xt - zt and s = xt + zt for appropriate choice of (xt,zt)

        mul_5(dmsn,sn,dm)

        lsr     x0, i, #6
        ldr     x2, [scalar, x0, lsl #3]
        lsr     x2, x2, i
        and     x2, x2, #1

        cmp     swap, x2
        mov     swap, x2

        mux_4(d,dm,dn)
        mux_4(s,sm,sn)

        mul_5(dnsm,sm,dn)

// DOUBLING: d = (xt - zt)^2 normalized only to 4 digits

        sqr_4(d,d)

// ADDING: dpro = (dmsn - dnsm)^2, spro = (dmsn + dnsm)^2
// DOUBLING: s = (xt + zt)^2, normalized only to 4 digits

        sub5_4(dpro,dmsn,dnsm)
        sqr_4(s,s)
        add5_4(spro,dmsn,dnsm)
        sqr_4(dpro,dpro)

// DOUBLING: p = 4 * xt * zt = s - d

        sub_twice4(p,s,d)

// ADDING: xm' = (dmsn + dnsm)^2

        sqr_p25519(xm,spro)

// DOUBLING: e = 121666 * p + d

        mov     x1, 0xdb42
        orr     x1, x1, 0x10000
        cmadd_4(e,p,d)

// DOUBLING: xn' = (xt + zt)^2 * (xt - zt)^2 = s * d

        mul_p25519(xn,s,d)

// ADDING: zm' = x * (dmsn - dnsm)^2

        mul_p25519(zm,dpro,x)

// DOUBLING: zn' = (4 * xt * zt) * ((xt - zt)^2 + 121666 * (4 * xt * zt))
//               = p * (d + 121666 * p)

        mul_p25519(zn,p,e)

// Loop down as far as 0 (inclusive)

        subs    i, i, #1
        bcs     loop

// The main loop does not handle the special input of the 2-torsion
// point = (0,0). In that case we may get a spurious (0,0) as output
// when we want (0,1) [for odd scalar] or (1,0) [for even scalar].
// Test if x = 0 (this is equivalent for curve25519 to y = 0) and if
// so, patch zm = 1 [for odd multiple], xn = 1 [for even multiple].

        ldp     x0, x1, [point]
        orr     x0, x0, x1
        ldp     x2, x3, [point, #16]
        orr     x2, x2, x3
        orr     x0, x0, x2
        cmp     x0, xzr
        cset    x0, eq
        ldr     x1, [zm]
        orr     x1, x1, x0
        str     x1, [zm]
        ldr     x2, [xn]
        orr     x2, x2, x0
        str     x2, [xn]

// Multiplex into the final outputs

        cmp     swap, xzr

        mux_4(resx,xm,xn)
        mux_4(resz,zm,zn)

// Restore stack and registers

        add     sp, sp, #NSPACE
        ldp     x20, x21, [sp], 16
        ldp     x19, x22, [sp], 16

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
