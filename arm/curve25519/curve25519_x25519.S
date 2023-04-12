// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// The x25519 function for curve25519
// Inputs scalar[4], point[4]; output res[4]
//
// extern void curve25519_x25519
//   (uint64_t res[static 4],uint64_t scalar[static 4],uint64_t point[static 4])
//
// Given a scalar n and the X coordinate of an input point P = (X,Y) on
// curve25519 (Y can live in any extension field of characteristic 2^255-19),
// this returns the X coordinate of n * P = (X, Y), or 0 when n * P is the
// point at infinity. Both n and X inputs are first slightly modified/mangled
// as specified in the relevant RFC (https://www.rfc-editor.org/rfc/rfc7748);
// in particular the lower three bits of n are set to zero.
//
// Standard ARM ABI: X0 = res, X1 = scalar, X2 = point
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(curve25519_x25519)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(curve25519_x25519)

        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 32

// Stable homes for the input result argument during the whole body
// and other variables that are only needed prior to the modular inverse.

#define res x23
#define i x20
#define swap x21

// Pointers to result x coord to be written

#define resx res, #0

// Pointer-offset pairs for temporaries on stack with some aliasing.

#define scalar sp, #(0*NUMSIZE)

#define pointx sp, #(1*NUMSIZE)

#define zm sp, #(2*NUMSIZE)
#define sm sp, #(2*NUMSIZE)
#define dpro sp, #(2*NUMSIZE)

#define sn sp, #(3*NUMSIZE)

#define dm sp, #(4*NUMSIZE)

#define zn sp, #(5*NUMSIZE)
#define dn sp, #(5*NUMSIZE)
#define e sp, #(5*NUMSIZE)

#define dmsn sp, #(6*NUMSIZE)
#define p sp, #(6*NUMSIZE)

#define xm sp, #(7*NUMSIZE)
#define dnsm sp, #(7*NUMSIZE)
#define spro sp, #(7*NUMSIZE)

#define d sp, #(8*NUMSIZE)

#define xn sp, #(9*NUMSIZE)
#define s sp, #(9*NUMSIZE)

// Total size to reserve on the stack

#define NSPACE (10*NUMSIZE)

// Macro wrapping up the basic field operation bignum_mul_p25519, only
// trivially different from a pure function call to that subroutine.

#define mul_p25519(P0,P1,P2)                    \
        ldp     x3, x4, [P1];                   \
        ldp     x5, x6, [P2];                   \
        umull   x7, w3, w5;                     \
        lsr     x0, x3, #32;                    \
        umull   x15, w0, w5;                    \
        lsr     x16, x5, #32;                   \
        umull   x8, w16, w0;                    \
        umull   x16, w3, w16;                   \
        adds    x7, x7, x15, lsl #32;           \
        lsr     x15, x15, #32;                  \
        adc     x8, x8, x15;                    \
        adds    x7, x7, x16, lsl #32;           \
        lsr     x16, x16, #32;                  \
        adc     x8, x8, x16;                    \
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
        ldp     x3, x4, [P1+16];                \
        ldp     x5, x6, [P2+16];                \
        umull   x11, w3, w5;                    \
        lsr     x0, x3, #32;                    \
        umull   x15, w0, w5;                    \
        lsr     x16, x5, #32;                   \
        umull   x12, w16, w0;                   \
        umull   x16, w3, w16;                   \
        adds    x11, x11, x15, lsl #32;         \
        lsr     x15, x15, #32;                  \
        adc     x12, x12, x15;                  \
        adds    x11, x11, x16, lsl #32;         \
        lsr     x16, x16, #32;                  \
        adc     x12, x12, x16;                  \
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
        ldp     x3, x4, [P1+16];                \
        ldp     x15, x16, [P1];                 \
        subs    x3, x3, x15;                    \
        sbcs    x4, x4, x16;                    \
        csetm   x16, cc;                        \
        ldp     x15, x0, [P2];                  \
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
        umull   x4, w11, w3;                    \
        add     x4, x4, w7, uxtw;               \
        lsr     x7, x7, #32;                    \
        lsr     x11, x11, #32;                  \
        umaddl  x11, w11, w3, x7;               \
        mov     x7, x4;                         \
        umull   x4, w12, w3;                    \
        add     x4, x4, w8, uxtw;               \
        lsr     x8, x8, #32;                    \
        lsr     x12, x12, #32;                  \
        umaddl  x12, w12, w3, x8;               \
        mov     x8, x4;                         \
        umull   x4, w13, w3;                    \
        add     x4, x4, w9, uxtw;               \
        lsr     x9, x9, #32;                    \
        lsr     x13, x13, #32;                  \
        umaddl  x13, w13, w3, x9;               \
        mov     x9, x4;                         \
        umull   x4, w14, w3;                    \
        add     x4, x4, w10, uxtw;              \
        lsr     x10, x10, #32;                  \
        lsr     x14, x14, #32;                  \
        umaddl  x14, w14, w3, x10;              \
        mov     x10, x4;                        \
        lsr     x0, x14, #31;                   \
        mov     x5, #0x13;                      \
        umaddl  x5, w5, w0, x5;                 \
        add     x7, x7, x5;                     \
        adds    x7, x7, x11, lsl #32;           \
        extr    x3, x12, x11, #32;              \
        adcs    x8, x8, x3;                     \
        extr    x3, x13, x12, #32;              \
        adcs    x9, x9, x3;                     \
        extr    x3, x14, x13, #32;              \
        lsl     x5, x0, #63;                    \
        eor     x10, x10, x5;                   \
        adc     x10, x10, x3;                   \
        mov     x3, #0x13;                      \
        tst     x10, #0x8000000000000000;       \
        csel    x3, x3, xzr, pl;                \
        subs    x7, x7, x3;                     \
        sbcs    x8, x8, xzr;                    \
        sbcs    x9, x9, xzr;                    \
        sbc     x10, x10, xzr;                  \
        and     x10, x10, #0x7fffffffffffffff;  \
        stp     x7, x8, [P0];                   \
        stp     x9, x10, [P0+16]

// A version of multiplication that only guarantees output < 2 * p_25519.
// This basically skips the +1 and final correction in quotient estimation.

#define mul_4(P0,P1,P2)                         \
        ldp     x3, x4, [P1];                   \
        ldp     x5, x6, [P2];                   \
        umull   x7, w3, w5;                     \
        lsr     x0, x3, #32;                    \
        umull   x15, w0, w5;                    \
        lsr     x16, x5, #32;                   \
        umull   x8, w16, w0;                    \
        umull   x16, w3, w16;                   \
        adds    x7, x7, x15, lsl #32;           \
        lsr     x15, x15, #32;                  \
        adc     x8, x8, x15;                    \
        adds    x7, x7, x16, lsl #32;           \
        lsr     x16, x16, #32;                  \
        adc     x8, x8, x16;                    \
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
        ldp     x3, x4, [P1+16];                \
        ldp     x5, x6, [P2+16];                \
        umull   x11, w3, w5;                    \
        lsr     x0, x3, #32;                    \
        umull   x15, w0, w5;                    \
        lsr     x16, x5, #32;                   \
        umull   x12, w16, w0;                   \
        umull   x16, w3, w16;                   \
        adds    x11, x11, x15, lsl #32;         \
        lsr     x15, x15, #32;                  \
        adc     x12, x12, x15;                  \
        adds    x11, x11, x16, lsl #32;         \
        lsr     x16, x16, #32;                  \
        adc     x12, x12, x16;                  \
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
        ldp     x3, x4, [P1+16];                \
        ldp     x15, x16, [P1];                 \
        subs    x3, x3, x15;                    \
        sbcs    x4, x4, x16;                    \
        csetm   x16, cc;                        \
        ldp     x15, x0, [P2];                  \
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
        umull   x4, w11, w3;                    \
        add     x4, x4, w7, uxtw;               \
        lsr     x7, x7, #32;                    \
        lsr     x11, x11, #32;                  \
        umaddl  x11, w11, w3, x7;               \
        mov     x7, x4;                         \
        umull   x4, w12, w3;                    \
        add     x4, x4, w8, uxtw;               \
        lsr     x8, x8, #32;                    \
        lsr     x12, x12, #32;                  \
        umaddl  x12, w12, w3, x8;               \
        mov     x8, x4;                         \
        umull   x4, w13, w3;                    \
        add     x4, x4, w9, uxtw;               \
        lsr     x9, x9, #32;                    \
        lsr     x13, x13, #32;                  \
        umaddl  x13, w13, w3, x9;               \
        mov     x9, x4;                         \
        umull   x4, w14, w3;                    \
        add     x4, x4, w10, uxtw;              \
        lsr     x10, x10, #32;                  \
        lsr     x14, x14, #32;                  \
        umaddl  x14, w14, w3, x10;              \
        mov     x10, x4;                        \
        lsr     x0, x14, #31;                   \
        mov     x5, #0x13;                      \
        umull   x5, w5, w0;                     \
        add     x7, x7, x5;                     \
        adds    x7, x7, x11, lsl #32;           \
        extr    x3, x12, x11, #32;              \
        adcs    x8, x8, x3;                     \
        extr    x3, x13, x12, #32;              \
        adcs    x9, x9, x3;                     \
        extr    x3, x14, x13, #32;              \
        lsl     x5, x0, #63;                    \
        eor     x10, x10, x5;                   \
        adc     x10, x10, x3;                   \
        stp     x7, x8, [P0];                   \
        stp     x9, x10, [P0+16]

// Squaring just giving a result < 2 * p_25519, which is done by
// basically skipping the +1 in the quotient estimate and the final
// optional correction.

#define sqr_4(P0,P1)                            \
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
        csetm   x16, cc;                        \
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
        csetm   x16, cc;                        \
        subs    x4, x4, x12;                    \
        sbcs    x5, x5, x13;                    \
        sbcs    x6, x6, x15;                    \
        sbcs    x7, x7, x14;                    \
        adcs    x8, x8, x16;                    \
        adc     x9, x9, x16;                    \
        mov     x10, #0x26;                     \
        umull   x12, w6, w10;                   \
        add     x12, x12, w2, uxtw;             \
        lsr     x2, x2, #32;                    \
        lsr     x6, x6, #32;                    \
        umaddl  x6, w6, w10, x2;                \
        mov     x2, x12;                        \
        umull   x12, w7, w10;                   \
        add     x12, x12, w3, uxtw;             \
        lsr     x3, x3, #32;                    \
        lsr     x7, x7, #32;                    \
        umaddl  x7, w7, w10, x3;                \
        mov     x3, x12;                        \
        umull   x12, w8, w10;                   \
        add     x12, x12, w4, uxtw;             \
        lsr     x4, x4, #32;                    \
        lsr     x8, x8, #32;                    \
        umaddl  x8, w8, w10, x4;                \
        mov     x4, x12;                        \
        umull   x12, w9, w10;                   \
        add     x12, x12, w5, uxtw;             \
        lsr     x5, x5, #32;                    \
        lsr     x9, x9, #32;                    \
        umaddl  x9, w9, w10, x5;                \
        mov     x5, x12;                        \
        lsr     x13, x9, #31;                   \
        mov     x11, #0x13;                     \
        umull   x11, w11, w13;                  \
        add     x2, x2, x11;                    \
        adds    x2, x2, x6, lsl #32;            \
        extr    x10, x7, x6, #32;               \
        adcs    x3, x3, x10;                    \
        extr    x10, x8, x7, #32;               \
        adcs    x4, x4, x10;                    \
        extr    x10, x9, x8, #32;               \
        lsl     x11, x13, #63;                  \
        eor     x5, x5, x11;                    \
        adc     x5, x5, x10;                    \
        stp     x2, x3, [P0];                   \
        stp     x4, x5, [P0+16]

// Modular addition with double modulus 2 * p_25519 = 2^256 - 38.
// This only ensures that the result fits in 4 digits, not that it is reduced
// even w.r.t. double modulus. The result is always correct modulo provided
// the sum of the inputs is < 2^256 + 2^256 - 38, so in particular provided
// at least one of them is reduced double modulo.

#define add_twice4(P0,P1,P2)                    \
        ldp     x3, x4, [P1];                   \
        ldp     x7, x8, [P2];                   \
        adds    x3, x3, x7;                     \
        adcs    x4, x4, x8;                     \
        ldp     x5, x6, [P1+16];                \
        ldp     x7, x8, [P2+16];                \
        adcs    x5, x5, x7;                     \
        adcs    x6, x6, x8;                     \
        mov     x9, #38;                        \
        csel    x9, x9, xzr, cs;                \
        adds    x3, x3, x9;                     \
        adcs    x4, x4, xzr;                    \
        adcs    x5, x5, xzr;                    \
        adc     x6, x6, xzr;                    \
        stp     x3, x4, [P0];                   \
        stp     x5, x6, [P0+16]

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

S2N_BN_SYMBOL(curve25519_x25519):

// Save regs and make room for temporaries

        stp     x19, x20, [sp, -16]!
        stp     x21, x22, [sp, -16]!
        stp     x23, x24, [sp, -16]!
        sub     sp, sp, #NSPACE

// Move the output pointer to a stable place

        mov     res, x0

// Copy the inputs to the local variables with minimal mangling:
//
//  - The scalar is in principle turned into 01xxx...xxx000 but
//    in the structure below the special handling of these bits is
//    explicit in the main computation; the scalar is just copied.
//
//  - The point x coord is reduced mod 2^255 by masking off the
//    top bit. In the main loop we only need reduction < 2 * p_25519.

        ldp     x10, x11, [x1]
        stp     x10, x11, [scalar]
        ldp     x12, x13, [x1, #16]
        stp     x12, x13, [scalar+16]

        ldp     x10, x11, [x2]
        stp     x10, x11, [pointx]
        ldp     x12, x13, [x2, #16]
        and     x13, x13, #0x7fffffffffffffff
        stp     x12, x13, [pointx+16]

// Initialize with explicit doubling in order to handle set bit 254.
// Set swap = 1 and (xm,zm) = (x,1) then double as (xn,zn) = 2 * (x,1).
// We use the fact that the point x coordinate is still in registers.
// Since zm = 1 we could do the doubling with an operation count of
// 2 * S + M instead of 2 * S + 2 * M, but it doesn't seem worth
// the slight complication arising from a different linear combination.

        mov     swap, #1
        stp     x10, x11, [xm]
        stp     x12, x13, [xm+16]
        stp     swap, xzr, [zm]
        stp     xzr, xzr, [zm+16]

        sub_twice4(d,xm,zm)
        add_twice4(s,xm,zm)
        sqr_4(d,d)
        sqr_4(s,s)
        sub_twice4(p,s,d)
        mov     x1, 0xdb42
        orr     x1, x1, 0x10000
        cmadd_4(e,p,d)
        mul_4(xn,s,d)
        mul_4(zn,p,e)

// The main loop over unmodified bits from i = 253, ..., i = 3 (inclusive).
// This is a classic Montgomery ladder, with the main coordinates only
// reduced mod 2 * p_25519, some intermediate results even more loosely.

        mov     i, #253

curve25519_x25519_scalarloop:

// sm = xm + zm; sn = xn + zn; dm = xm - zm; dn = xn - zn

        sub_twice4(dm,xm,zm)
        add_twice4(sn,xn,zn)
        sub_twice4(dn,xn,zn)
        add_twice4(sm,xm,zm)

// ADDING: dmsn = dm * sn
// DOUBLING: mux d = xt - zt and s = xt + zt for appropriate choice of (xt,zt)

        mul_4(dmsn,sn,dm)

        lsr     x0, i, #6
        ldr     x2, [sp, x0, lsl #3]    // Exploiting scalar = sp exactly
        lsr     x2, x2, i
        and     x2, x2, #1

        cmp     swap, x2
        mov     swap, x2

        mux_4(d,dm,dn)
        mux_4(s,sm,sn)

// ADDING: dnsm = sm * dn

        mul_4(dnsm,sm,dn)

// DOUBLING: d = (xt - zt)^2

        sqr_4(d,d)

// ADDING: dpro = (dmsn - dnsm)^2, spro = (dmsn + dnsm)^2
// DOUBLING: s = (xt + zt)^2

        sub_twice4(dpro,dmsn,dnsm)
        sqr_4(s,s)
        add_twice4(spro,dmsn,dnsm)
        sqr_4(dpro,dpro)

// DOUBLING: p = 4 * xt * zt = s - d

        sub_twice4(p,s,d)

// ADDING: xm' = (dmsn + dnsm)^2

        sqr_4(xm,spro)

// DOUBLING: e = 121666 * p + d

        mov     x1, 0xdb42
        orr     x1, x1, 0x10000
        cmadd_4(e,p,d)

// DOUBLING: xn' = (xt + zt)^2 * (xt - zt)^2 = s * d

        mul_4(xn,s,d)

// ADDING: zm' = x * (dmsn - dnsm)^2

        mul_4(zm,dpro,pointx)

// DOUBLING: zn' = (4 * xt * zt) * ((xt - zt)^2 + 121666 * (4 * xt * zt))
//               = p * (d + 121666 * p)

        mul_4(zn,p,e)

// Loop down as far as 3 (inclusive)

        sub     i, i, #1
        cmp     i, #3
        bcs     curve25519_x25519_scalarloop

// Multiplex directly into (xn,zn) then do three pure doubling steps;
// this accounts for the implicit zeroing of the three lowest bits
// of the scalar. On the very last doubling we *fully* reduce zn mod
// p_25519 to ease checking for degeneracy below.

        cmp     swap, xzr
        mux_4(xn,xm,xn)
        mux_4(zn,zm,zn)

        sub_twice4(d,xn,zn)
        add_twice4(s,xn,zn)
        sqr_4(d,d)
        sqr_4(s,s)
        sub_twice4(p,s,d)
        mov     x1, 0xdb42
        orr     x1, x1, 0x10000
        cmadd_4(e,p,d)
        mul_4(xn,s,d)
        mul_4(zn,p,e)

        sub_twice4(d,xn,zn)
        add_twice4(s,xn,zn)
        sqr_4(d,d)
        sqr_4(s,s)
        sub_twice4(p,s,d)
        mov     x1, 0xdb42
        orr     x1, x1, 0x10000
        cmadd_4(e,p,d)
        mul_4(xn,s,d)
        mul_4(zn,p,e)

        sub_twice4(d,xn,zn)
        add_twice4(s,xn,zn)
        sqr_4(d,d)
        sqr_4(s,s)
        sub_twice4(p,s,d)
        mov     x1, 0xdb42
        orr     x1, x1, 0x10000
        cmadd_4(e,p,d)
        mul_4(xn,s,d)
        mul_p25519(zn,p,e)

// The projective result of the scalar multiplication is now (xn,zn).
// First set up the constant sn = 2^255 - 19 for the modular inverse.

        mov     x0, #-19
        mov     x1, #-1
        mov     x2, #0x7fffffffffffffff
        stp     x0, x1, [sn]
        stp     x1, x2, [sn+16]

// Prepare to call the modular inverse function to get zm = 1/zn

        mov     x0, #4
        add     x1, zm
        add     x2, zn
        add     x3, sn
        add     x4, p

// Inline copy of bignum_modinv, identical except for stripping out the
// prologue and epilogue saving and restoring registers and the initial
// test for k = 0 (which is trivially false here since k = 4). For more
// details and explanations see "arm/generic/bignum_modinv.S".

        lsl     x10, x0, #3
        add     x21, x4, x10
        add     x22, x21, x10
        mov     x10, xzr
curve25519_x25519_copyloop:
        ldr     x11, [x2, x10, lsl #3]
        ldr     x12, [x3, x10, lsl #3]
        str     x11, [x21, x10, lsl #3]
        str     x12, [x22, x10, lsl #3]
        str     x12, [x4, x10, lsl #3]
        str     xzr, [x1, x10, lsl #3]
        add     x10, x10, #0x1
        cmp     x10, x0
        b.cc    curve25519_x25519_copyloop
        ldr     x11, [x4]
        sub     x12, x11, #0x1
        str     x12, [x4]
        lsl     x20, x11, #2
        sub     x20, x11, x20
        eor     x20, x20, #0x2
        mov     x12, #0x1
        madd    x12, x11, x20, x12
        mul     x11, x12, x12
        madd    x20, x12, x20, x20
        mul     x12, x11, x11
        madd    x20, x11, x20, x20
        mul     x11, x12, x12
        madd    x20, x12, x20, x20
        madd    x20, x11, x20, x20
        lsl     x2, x0, #7
curve25519_x25519_outerloop:
        add     x10, x2, #0x3f
        lsr     x5, x10, #6
        cmp     x5, x0
        csel    x5, x0, x5, cs
        mov     x13, xzr
        mov     x15, xzr
        mov     x14, xzr
        mov     x16, xzr
        mov     x19, xzr
        mov     x10, xzr
curve25519_x25519_toploop:
        ldr     x11, [x21, x10, lsl #3]
        ldr     x12, [x22, x10, lsl #3]
        orr     x17, x11, x12
        cmp     x17, xzr
        and     x17, x19, x13
        csel    x15, x17, x15, ne
        and     x17, x19, x14
        csel    x16, x17, x16, ne
        csel    x13, x11, x13, ne
        csel    x14, x12, x14, ne
        csetm   x19, ne
        add     x10, x10, #0x1
        cmp     x10, x5
        b.cc    curve25519_x25519_toploop
        orr     x11, x13, x14
        clz     x12, x11
        negs    x17, x12
        lsl     x13, x13, x12
        csel    x15, x15, xzr, ne
        lsl     x14, x14, x12
        csel    x16, x16, xzr, ne
        lsr     x15, x15, x17
        lsr     x16, x16, x17
        orr     x13, x13, x15
        orr     x14, x14, x16
        ldr     x15, [x21]
        ldr     x16, [x22]
        mov     x6, #0x1
        mov     x7, xzr
        mov     x8, xzr
        mov     x9, #0x1
        mov     x10, #0x3a
        tst     x15, #0x1
curve25519_x25519_innerloop:
        csel    x11, x14, xzr, ne
        csel    x12, x16, xzr, ne
        csel    x17, x8, xzr, ne
        csel    x19, x9, xzr, ne
        ccmp    x13, x14, #0x2, ne
        sub     x11, x13, x11
        sub     x12, x15, x12
        csel    x14, x14, x13, cs
        cneg    x11, x11, cc
        csel    x16, x16, x15, cs
        cneg    x15, x12, cc
        csel    x8, x8, x6, cs
        csel    x9, x9, x7, cs
        tst     x12, #0x2
        add     x6, x6, x17
        add     x7, x7, x19
        lsr     x13, x11, #1
        lsr     x15, x15, #1
        add     x8, x8, x8
        add     x9, x9, x9
        sub     x10, x10, #0x1
        cbnz    x10, curve25519_x25519_innerloop
        mov     x13, xzr
        mov     x14, xzr
        mov     x17, xzr
        mov     x19, xzr
        mov     x10, xzr
curve25519_x25519_congloop:
        ldr     x11, [x4, x10, lsl #3]
        ldr     x12, [x1, x10, lsl #3]
        mul     x15, x6, x11
        mul     x16, x7, x12
        adds    x15, x15, x13
        umulh   x13, x6, x11
        adc     x13, x13, xzr
        adds    x15, x15, x16
        extr    x17, x15, x17, #58
        str     x17, [x4, x10, lsl #3]
        mov     x17, x15
        umulh   x15, x7, x12
        adc     x13, x13, x15
        mul     x15, x8, x11
        mul     x16, x9, x12
        adds    x15, x15, x14
        umulh   x14, x8, x11
        adc     x14, x14, xzr
        adds    x15, x15, x16
        extr    x19, x15, x19, #58
        str     x19, [x1, x10, lsl #3]
        mov     x19, x15
        umulh   x15, x9, x12
        adc     x14, x14, x15
        add     x10, x10, #0x1
        cmp     x10, x0
        b.cc    curve25519_x25519_congloop
        extr    x13, x13, x17, #58
        extr    x14, x14, x19, #58
        ldr     x11, [x4]
        mul     x17, x11, x20
        ldr     x12, [x3]
        mul     x15, x17, x12
        umulh   x16, x17, x12
        adds    x11, x11, x15
        mov     x10, #0x1
        sub     x11, x0, #0x1
        cbz     x11, curve25519_x25519_wmontend
curve25519_x25519_wmontloop:
        ldr     x11, [x3, x10, lsl #3]
        ldr     x12, [x4, x10, lsl #3]
        mul     x15, x17, x11
        adcs    x12, x12, x16
        umulh   x16, x17, x11
        adc     x16, x16, xzr
        adds    x12, x12, x15
        sub     x15, x10, #0x1
        str     x12, [x4, x15, lsl #3]
        add     x10, x10, #0x1
        sub     x11, x10, x0
        cbnz    x11, curve25519_x25519_wmontloop
curve25519_x25519_wmontend:
        adcs    x16, x16, x13
        adc     x13, xzr, xzr
        sub     x15, x10, #0x1
        str     x16, [x4, x15, lsl #3]
        negs    x10, xzr
curve25519_x25519_wcmploop:
        ldr     x11, [x4, x10, lsl #3]
        ldr     x12, [x3, x10, lsl #3]
        sbcs    xzr, x11, x12
        add     x10, x10, #0x1
        sub     x11, x10, x0
        cbnz    x11, curve25519_x25519_wcmploop
        sbcs    xzr, x13, xzr
        csetm   x13, cs
        negs    x10, xzr
curve25519_x25519_wcorrloop:
        ldr     x11, [x4, x10, lsl #3]
        ldr     x12, [x3, x10, lsl #3]
        and     x12, x12, x13
        sbcs    x11, x11, x12
        str     x11, [x4, x10, lsl #3]
        add     x10, x10, #0x1
        sub     x11, x10, x0
        cbnz    x11, curve25519_x25519_wcorrloop
        ldr     x11, [x1]
        mul     x17, x11, x20
        ldr     x12, [x3]
        mul     x15, x17, x12
        umulh   x16, x17, x12
        adds    x11, x11, x15
        mov     x10, #0x1
        sub     x11, x0, #0x1
        cbz     x11, curve25519_x25519_zmontend
curve25519_x25519_zmontloop:
        ldr     x11, [x3, x10, lsl #3]
        ldr     x12, [x1, x10, lsl #3]
        mul     x15, x17, x11
        adcs    x12, x12, x16
        umulh   x16, x17, x11
        adc     x16, x16, xzr
        adds    x12, x12, x15
        sub     x15, x10, #0x1
        str     x12, [x1, x15, lsl #3]
        add     x10, x10, #0x1
        sub     x11, x10, x0
        cbnz    x11, curve25519_x25519_zmontloop
curve25519_x25519_zmontend:
        adcs    x16, x16, x14
        adc     x14, xzr, xzr
        sub     x15, x10, #0x1
        str     x16, [x1, x15, lsl #3]
        negs    x10, xzr
curve25519_x25519_zcmploop:
        ldr     x11, [x1, x10, lsl #3]
        ldr     x12, [x3, x10, lsl #3]
        sbcs    xzr, x11, x12
        add     x10, x10, #0x1
        sub     x11, x10, x0
        cbnz    x11, curve25519_x25519_zcmploop
        sbcs    xzr, x14, xzr
        csetm   x14, cs
        negs    x10, xzr
curve25519_x25519_zcorrloop:
        ldr     x11, [x1, x10, lsl #3]
        ldr     x12, [x3, x10, lsl #3]
        and     x12, x12, x14
        sbcs    x11, x11, x12
        str     x11, [x1, x10, lsl #3]
        add     x10, x10, #0x1
        sub     x11, x10, x0
        cbnz    x11, curve25519_x25519_zcorrloop
        mov     x13, xzr
        mov     x14, xzr
        mov     x17, xzr
        mov     x19, xzr
        mov     x10, xzr
curve25519_x25519_crossloop:
        ldr     x11, [x21, x10, lsl #3]
        ldr     x12, [x22, x10, lsl #3]
        mul     x15, x6, x11
        mul     x16, x7, x12
        adds    x15, x15, x13
        umulh   x13, x6, x11
        adc     x13, x13, xzr
        subs    x15, x15, x16
        str     x15, [x21, x10, lsl #3]
        umulh   x15, x7, x12
        sub     x17, x15, x17
        sbcs    x13, x13, x17
        csetm   x17, cc
        mul     x15, x8, x11
        mul     x16, x9, x12
        adds    x15, x15, x14
        umulh   x14, x8, x11
        adc     x14, x14, xzr
        subs    x15, x15, x16
        str     x15, [x22, x10, lsl #3]
        umulh   x15, x9, x12
        sub     x19, x15, x19
        sbcs    x14, x14, x19
        csetm   x19, cc
        add     x10, x10, #0x1
        cmp     x10, x5
        b.cc    curve25519_x25519_crossloop
        cmn     x17, x17
        ldr     x15, [x21]
        mov     x10, xzr
        sub     x6, x5, #0x1
        cbz     x6, curve25519_x25519_negskip1
curve25519_x25519_negloop1:
        add     x11, x10, #0x8
        ldr     x12, [x21, x11]
        extr    x15, x12, x15, #58
        eor     x15, x15, x17
        adcs    x15, x15, xzr
        str     x15, [x21, x10]
        mov     x15, x12
        add     x10, x10, #0x8
        sub     x6, x6, #0x1
        cbnz    x6, curve25519_x25519_negloop1
curve25519_x25519_negskip1:
        extr    x15, x13, x15, #58
        eor     x15, x15, x17
        adcs    x15, x15, xzr
        str     x15, [x21, x10]
        cmn     x19, x19
        ldr     x15, [x22]
        mov     x10, xzr
        sub     x6, x5, #0x1
        cbz     x6, curve25519_x25519_negskip2
curve25519_x25519_negloop2:
        add     x11, x10, #0x8
        ldr     x12, [x22, x11]
        extr    x15, x12, x15, #58
        eor     x15, x15, x19
        adcs    x15, x15, xzr
        str     x15, [x22, x10]
        mov     x15, x12
        add     x10, x10, #0x8
        sub     x6, x6, #0x1
        cbnz    x6, curve25519_x25519_negloop2
curve25519_x25519_negskip2:
        extr    x15, x14, x15, #58
        eor     x15, x15, x19
        adcs    x15, x15, xzr
        str     x15, [x22, x10]
        mov     x10, xzr
        cmn     x17, x17
curve25519_x25519_wfliploop:
        ldr     x11, [x3, x10, lsl #3]
        ldr     x12, [x4, x10, lsl #3]
        and     x11, x11, x17
        eor     x12, x12, x17
        adcs    x11, x11, x12
        str     x11, [x4, x10, lsl #3]
        add     x10, x10, #0x1
        sub     x11, x10, x0
        cbnz    x11, curve25519_x25519_wfliploop
        mvn     x19, x19
        mov     x10, xzr
        cmn     x19, x19
curve25519_x25519_zfliploop:
        ldr     x11, [x3, x10, lsl #3]
        ldr     x12, [x1, x10, lsl #3]
        and     x11, x11, x19
        eor     x12, x12, x19
        adcs    x11, x11, x12
        str     x11, [x1, x10, lsl #3]
        add     x10, x10, #0x1
        sub     x11, x10, x0
        cbnz    x11, curve25519_x25519_zfliploop
        subs    x2, x2, #0x3a
        b.hi    curve25519_x25519_outerloop

// Since we eventually want to return 0 when the result is the point at
// infinity, we force xn = 0 whenever zn = 0. This avoids building in a
// dependency on the behavior of modular inverse in out-of-scope cases.

        ldp     x0, x1, [zn]
        ldp     x2, x3, [zn+16]
        orr     x0, x0, x1
        orr     x2, x2, x3
        orr     x4, x0, x2
        cmp     x4, xzr
        ldp     x0, x1, [xn]
        csel    x0, x0, xzr, ne
        csel    x1, x1, xzr, ne
        ldp     x2, x3, [xn+16]
        stp     x0, x1, [xn]
        csel    x2, x2, xzr, ne
        csel    x3, x3, xzr, ne
        stp     x2, x3, [xn+16]

// Now the result is xn * (1/zn), fully reduced modulo p.

        mul_p25519(resx,xn,zm)

// Restore stack and registers

        add     sp, sp, #NSPACE
        ldp     x23, x24, [sp], 16
        ldp     x21, x22, [sp], 16
        ldp     x19, x20, [sp], 16

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
