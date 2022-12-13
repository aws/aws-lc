// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// Extended projective doubling for edwards25519
// Input p1[12]; output p3[16]
//
// extern void edwards25519_epdouble
//   (uint64_t p3[static 16],uint64_t p1[static 12])
//
// If p1 is a point on edwards25519, returns its double p3 = 2 * p1.
// The output p3 is in extended projective coordinates, representing
// affine (x,y) by a quadruple (X,Y,Z,T) where x = X / Z, y = Y / Z
// and x * y = T / Z. The input p1 may also be in the same extended
// projective representation, but the final T field is not used so
// a more basic projective triple (X,Y,Z) suffices.
//
// Standard ARM ABI: X0 = p3, X1 = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(edwards25519_epdouble)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(edwards25519_epdouble)

        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 32

// Stable homes for input arguments during main code sequence

#define p3 x17
#define p1 x19

// Pointers to input and output coordinates

#define x_1 p1, #0
#define y_1 p1, #NUMSIZE
#define z_1 p1, #(2*NUMSIZE)

#define x_3 p3, #0
#define y_3 p3, #NUMSIZE
#define z_3 p3, #(2*NUMSIZE)
#define w_3 p3, #(3*NUMSIZE)

// Pointer-offset pairs for temporaries on stack

#define t0 sp, #(0*NUMSIZE)
#define t1 sp, #(1*NUMSIZE)
#define t2 sp, #(2*NUMSIZE)
#define t3 sp, #(3*NUMSIZE)
#define t4 sp, #(4*NUMSIZE)

// Total size to reserve on the stack

#define NSPACE (5*NUMSIZE)

// Macro wrapping up the basic field multiplication, only trivially
// different from a pure function call to bignum_mul_p25519.

#define mul_p25519(P0,P1,P2)                    \
        ldp     x3, x4, [P1];                   \
        ldp     x5, x6, [P2];                   \
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
        ldp     x3, x4, [P1+16];                \
        ldp     x5, x6, [P2+16];                \
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
        stp     x7, x8, [P0];                   \
        stp     x9, x10, [P0+16]

// Squaring just giving a result < 2 * p_25519, which is done by
// basically skipping the +1 in the quotient estimate and the final
// optional correction.

#define sqr_4(P0,P1)                            \
        ldp     x6, x7, [P1];                   \
        ldp     x10, x11, [P1+16];              \
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
        stp     x2, x3, [P0];                   \
        stp     x4, x5, [P0+16]

// Plain 4-digit adding without any normalization.
// With inputs < p_25519 (indeed < 2^255) it still gives a 4-digit result,
// indeed one < 2 * p_25519 for normalized inputs.

#define add_4(P0,P1,P2)                         \
        ldp     x0, x1, [P1];                   \
        ldp     x4, x5, [P2];                   \
        adds    x0, x0, x4;                     \
        adcs    x1, x1, x5;                     \
        ldp     x2, x3, [P1+16];                \
        ldp     x6, x7, [P2+16];                \
        adcs    x2, x2, x6;                     \
        adc     x3, x3, x7;                     \
        stp     x0, x1, [P0];                   \
        stp     x2, x3, [P0+16]

// Modular subtraction with double modulus 2 * p_25519 = 2^256 - 38

#define sub_twice4(P0,P1,P2)                    \
        ldp     x5, x6, [P1];                   \
        ldp     x4, x3, [P2];                   \
        subs    x5, x5, x4;                     \
        sbcs    x6, x6, x3;                     \
        ldp     x7, x8, [P1+16];                \
        ldp     x4, x3, [P2+16];                \
        sbcs    x7, x7, x4;                     \
        sbcs    x8, x8, x3;                     \
        mov     x4, #38;                        \
        csel    x3, x4, xzr, lo;                \
        subs    x5, x5, x3;                     \
        sbcs    x6, x6, xzr;                    \
        sbcs    x7, x7, xzr;                    \
        sbc     x8, x8, xzr;                    \
        stp     x5, x6, [P0];                   \
        stp     x7, x8, [P0+16]

// Modular addition and doubling with double modulus 2 * p_25519 = 2^256 - 38.
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

#define double_twice4(P0,P1)                    \
        ldp     x3, x4, [P1];                   \
        adds    x3, x3, x3;                     \
        adcs    x4, x4, x4;                     \
        ldp     x5, x6, [P1+16];                \
        adcs    x5, x5, x5;                     \
        adcs    x6, x6, x6;                     \
        mov     x9, #38;                        \
        csel    x9, x9, xzr, cs;                \
        adds    x3, x3, x9;                     \
        adcs    x4, x4, xzr;                    \
        adcs    x5, x5, xzr;                    \
        adc     x6, x6, xzr;                    \
        stp     x3, x4, [P0];                   \
        stp     x5, x6, [P0+16]

S2N_BN_SYMBOL(edwards25519_epdouble):

// Save regs and make room for temporaries

        stp     x19, x20, [sp, -16]!
        sub     sp, sp, #NSPACE

// Move the input arguments to stable places

        mov     p3, x0
        mov     p1, x1

// Main sequence

        add_4(t0,x_1,y_1)
        sqr_4(t1,z_1)
        sqr_4(t2,x_1)
        sqr_4(t3,y_1)
        double_twice4(t1,t1)
        sqr_4(t0,t0)
        add_twice4(t4,t2,t3)
        sub_twice4(t2,t2,t3)
        add_twice4(t3,t1,t2)
        sub_twice4(t1,t4,t0)
        mul_p25519(y_3,t2,t4)
        mul_p25519(z_3,t3,t2)
        mul_p25519(w_3,t1,t4)
        mul_p25519(x_3,t1,t3)

// Restore stack and registers

        add     sp, sp, #NSPACE
        ldp     x19, x20, [sp], 16
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
