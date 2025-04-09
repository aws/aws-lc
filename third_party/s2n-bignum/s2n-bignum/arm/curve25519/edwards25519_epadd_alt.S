// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Extended projective addition for edwards25519
// Inputs p1[16], p2[16]; output p3[16]
//
// extern void edwards25519_epadd_alt
//   (uint64_t p3[static 16],uint64_t p1[static 16],uint64_t p2[static 16])
//
// The output p3 and both inputs p1 and p2 are points (x,y) on
// edwards25519 represented in extended projective quadruples (X,Y,Z,T)
// where x = X / Z, y = Y / Z and x * y = T / Z.
//
// Standard ARM ABI: X0 = p3, X1 = p1, X2 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(edwards25519_epadd_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(edwards25519_epadd_alt)

        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 32

// Stable homes for input arguments during main code sequence

#define p3 x17
#define p1 x19
#define p2 x20

// Pointers to input and output coordinates

#define x_1 p1, #0
#define y_1 p1, #NUMSIZE
#define z_1 p1, #(2*NUMSIZE)
#define w_1 p1, #(3*NUMSIZE)

#define x_2 p2, #0
#define y_2 p2, #NUMSIZE
#define z_2 p2, #(2*NUMSIZE)
#define w_2 p2, #(3*NUMSIZE)

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
#define t5 sp, #(5*NUMSIZE)

// Total size to reserve on the stack

#define NSPACE (6*NUMSIZE)

// Macro wrapping up the basic field operation bignum_mul_p25519_alt, only
// trivially different from a pure function call to that subroutine.

#define mul_p25519(P0,P1,P2)                    \
        ldp     x3, x4, [P1];                   \
        ldp     x7, x8, [P2];                   \
        mul     x12, x3, x7;                    \
        umulh   x13, x3, x7;                    \
        mul     x11, x3, x8;                    \
        umulh   x14, x3, x8;                    \
        adds    x13, x13, x11;                  \
        ldp     x9, x10, [P2+16];               \
        mul     x11, x3, x9;                    \
        umulh   x15, x3, x9;                    \
        adcs    x14, x14, x11;                  \
        mul     x11, x3, x10;                   \
        umulh   x16, x3, x10;                   \
        adcs    x15, x15, x11;                  \
        adc     x16, x16, xzr;                  \
        ldp     x5, x6, [P1+16];                \
        mul     x11, x4, x7;                    \
        adds    x13, x13, x11;                  \
        mul     x11, x4, x8;                    \
        adcs    x14, x14, x11;                  \
        mul     x11, x4, x9;                    \
        adcs    x15, x15, x11;                  \
        mul     x11, x4, x10;                   \
        adcs    x16, x16, x11;                  \
        umulh   x3, x4, x10;                    \
        adc     x3, x3, xzr;                    \
        umulh   x11, x4, x7;                    \
        adds    x14, x14, x11;                  \
        umulh   x11, x4, x8;                    \
        adcs    x15, x15, x11;                  \
        umulh   x11, x4, x9;                    \
        adcs    x16, x16, x11;                  \
        adc     x3, x3, xzr;                    \
        mul     x11, x5, x7;                    \
        adds    x14, x14, x11;                  \
        mul     x11, x5, x8;                    \
        adcs    x15, x15, x11;                  \
        mul     x11, x5, x9;                    \
        adcs    x16, x16, x11;                  \
        mul     x11, x5, x10;                   \
        adcs    x3, x3, x11;                    \
        umulh   x4, x5, x10;                    \
        adc     x4, x4, xzr;                    \
        umulh   x11, x5, x7;                    \
        adds    x15, x15, x11;                  \
        umulh   x11, x5, x8;                    \
        adcs    x16, x16, x11;                  \
        umulh   x11, x5, x9;                    \
        adcs    x3, x3, x11;                    \
        adc     x4, x4, xzr;                    \
        mul     x11, x6, x7;                    \
        adds    x15, x15, x11;                  \
        mul     x11, x6, x8;                    \
        adcs    x16, x16, x11;                  \
        mul     x11, x6, x9;                    \
        adcs    x3, x3, x11;                    \
        mul     x11, x6, x10;                   \
        adcs    x4, x4, x11;                    \
        umulh   x5, x6, x10;                    \
        adc     x5, x5, xzr;                    \
        umulh   x11, x6, x7;                    \
        adds    x16, x16, x11;                  \
        umulh   x11, x6, x8;                    \
        adcs    x3, x3, x11;                    \
        umulh   x11, x6, x9;                    \
        adcs    x4, x4, x11;                    \
        adc     x5, x5, xzr;                    \
        mov     x7, #0x26;                      \
        mul     x11, x7, x16;                   \
        umulh   x9, x7, x16;                    \
        adds    x12, x12, x11;                  \
        mul     x11, x7, x3;                    \
        umulh   x3, x7, x3;                     \
        adcs    x13, x13, x11;                  \
        mul     x11, x7, x4;                    \
        umulh   x4, x7, x4;                     \
        adcs    x14, x14, x11;                  \
        mul     x11, x7, x5;                    \
        umulh   x5, x7, x5;                     \
        adcs    x15, x15, x11;                  \
        cset    x16, cs;                        \
        adds    x15, x15, x4;                   \
        adc     x16, x16, x5;                   \
        cmn     x15, x15;                       \
        orr     x15, x15, #0x8000000000000000;  \
        adc     x8, x16, x16;                   \
        mov     x7, #0x13;                      \
        madd    x11, x7, x8, x7;                \
        adds    x12, x12, x11;                  \
        adcs    x13, x13, x9;                   \
        adcs    x14, x14, x3;                   \
        adcs    x15, x15, xzr;                  \
        csel    x7, x7, xzr, cc;                \
        subs    x12, x12, x7;                   \
        sbcs    x13, x13, xzr;                  \
        sbcs    x14, x14, xzr;                  \
        sbc     x15, x15, xzr;                  \
        and     x15, x15, #0x7fffffffffffffff;  \
        stp     x12, x13, [P0];                 \
        stp     x14, x15, [P0+16]

// A version of multiplication that only guarantees output < 2 * p_25519.
// This basically skips the +1 and final correction in quotient estimation.

#define mul_4(P0,P1,P2)                         \
        ldp     x3, x4, [P1];                   \
        ldp     x7, x8, [P2];                   \
        mul     x12, x3, x7;                    \
        umulh   x13, x3, x7;                    \
        mul     x11, x3, x8;                    \
        umulh   x14, x3, x8;                    \
        adds    x13, x13, x11;                  \
        ldp     x9, x10, [P2+16];               \
        mul     x11, x3, x9;                    \
        umulh   x15, x3, x9;                    \
        adcs    x14, x14, x11;                  \
        mul     x11, x3, x10;                   \
        umulh   x16, x3, x10;                   \
        adcs    x15, x15, x11;                  \
        adc     x16, x16, xzr;                  \
        ldp     x5, x6, [P1+16];                \
        mul     x11, x4, x7;                    \
        adds    x13, x13, x11;                  \
        mul     x11, x4, x8;                    \
        adcs    x14, x14, x11;                  \
        mul     x11, x4, x9;                    \
        adcs    x15, x15, x11;                  \
        mul     x11, x4, x10;                   \
        adcs    x16, x16, x11;                  \
        umulh   x3, x4, x10;                    \
        adc     x3, x3, xzr;                    \
        umulh   x11, x4, x7;                    \
        adds    x14, x14, x11;                  \
        umulh   x11, x4, x8;                    \
        adcs    x15, x15, x11;                  \
        umulh   x11, x4, x9;                    \
        adcs    x16, x16, x11;                  \
        adc     x3, x3, xzr;                    \
        mul     x11, x5, x7;                    \
        adds    x14, x14, x11;                  \
        mul     x11, x5, x8;                    \
        adcs    x15, x15, x11;                  \
        mul     x11, x5, x9;                    \
        adcs    x16, x16, x11;                  \
        mul     x11, x5, x10;                   \
        adcs    x3, x3, x11;                    \
        umulh   x4, x5, x10;                    \
        adc     x4, x4, xzr;                    \
        umulh   x11, x5, x7;                    \
        adds    x15, x15, x11;                  \
        umulh   x11, x5, x8;                    \
        adcs    x16, x16, x11;                  \
        umulh   x11, x5, x9;                    \
        adcs    x3, x3, x11;                    \
        adc     x4, x4, xzr;                    \
        mul     x11, x6, x7;                    \
        adds    x15, x15, x11;                  \
        mul     x11, x6, x8;                    \
        adcs    x16, x16, x11;                  \
        mul     x11, x6, x9;                    \
        adcs    x3, x3, x11;                    \
        mul     x11, x6, x10;                   \
        adcs    x4, x4, x11;                    \
        umulh   x5, x6, x10;                    \
        adc     x5, x5, xzr;                    \
        umulh   x11, x6, x7;                    \
        adds    x16, x16, x11;                  \
        umulh   x11, x6, x8;                    \
        adcs    x3, x3, x11;                    \
        umulh   x11, x6, x9;                    \
        adcs    x4, x4, x11;                    \
        adc     x5, x5, xzr;                    \
        mov     x7, #0x26;                      \
        mul     x11, x7, x16;                   \
        umulh   x9, x7, x16;                    \
        adds    x12, x12, x11;                  \
        mul     x11, x7, x3;                    \
        umulh   x3, x7, x3;                     \
        adcs    x13, x13, x11;                  \
        mul     x11, x7, x4;                    \
        umulh   x4, x7, x4;                     \
        adcs    x14, x14, x11;                  \
        mul     x11, x7, x5;                    \
        umulh   x5, x7, x5;                     \
        adcs    x15, x15, x11;                  \
        cset    x16, cs;                        \
        adds    x15, x15, x4;                   \
        adc     x16, x16, x5;                   \
        cmn     x15, x15;                       \
        bic     x15, x15, #0x8000000000000000;  \
        adc     x8, x16, x16;                   \
        mov     x7, #0x13;                      \
        mul     x11, x7, x8;                    \
        adds    x12, x12, x11;                  \
        adcs    x13, x13, x9;                   \
        adcs    x14, x14, x3;                   \
        adc     x15, x15, xzr;                  \
        stp     x12, x13, [P0];                 \
        stp     x14, x15, [P0+16]

// Plain 4-digit add and doubling without any normalization
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

#define double_4(P0,P1)                         \
        ldp     x0, x1, [P1];                   \
        adds    x0, x0, x0;                     \
        adcs    x1, x1, x1;                     \
        ldp     x2, x3, [P1+16];                \
        adcs    x2, x2, x2;                     \
        adc     x3, x3, x3;                     \
        stp     x0, x1, [P0];                   \
        stp     x2, x3, [P0+16]

// Subtraction of a pair of numbers < p_25519 just sufficient
// to give a 4-digit result. It actually always does (x - z) + (2^255-19)
// which in turn is done by (x - z) - (2^255+19) discarding the 2^256
// implicitly

#define sub_4(P0,P1,P2)                         \
        ldp     x5, x6, [P1];                   \
        ldp     x4, x3, [P2];                   \
        subs    x5, x5, x4;                     \
        sbcs    x6, x6, x3;                     \
        ldp     x7, x8, [P1+16];                \
        ldp     x4, x3, [P2+16];                \
        sbcs    x7, x7, x4;                     \
        sbcs    x8, x8, x3;                     \
        mov     x3, #19;                        \
        subs    x5, x5, x3;                     \
        sbcs    x6, x6, xzr;                    \
        sbcs    x7, x7, xzr;                    \
        mov     x4, #0x8000000000000000;        \
        sbc     x8, x8, x4;                     \
        stp     x5, x6, [P0];                   \
        stp     x7, x8, [P0+16]

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

// Modular addition with inputs double modulus 2 * p_25519 = 2^256 - 38
// and in general only guaranteeing a 4-digit result, not even < 2 * p_25519.

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

// Load the constant k_25519 = 2 * d_25519 using immediate operations

#define load_k25519(P0)                         \
        movz    x0, #0xf159;                    \
        movz    x1, #0xb156;                    \
        movz    x2, #0xd130;                    \
        movz    x3, #0xfce7;                    \
        movk    x0, #0x26b2, lsl #16;           \
        movk    x1, #0x8283, lsl #16;           \
        movk    x2, #0xeef3, lsl #16;           \
        movk    x3, #0x56df, lsl #16;           \
        movk    x0, #0x9b94, lsl #32;           \
        movk    x1, #0x149a, lsl #32;           \
        movk    x2, #0x80f2, lsl #32;           \
        movk    x3, #0xd9dc, lsl #32;           \
        movk    x0, #0xebd6, lsl #48;           \
        movk    x1, #0x00e0, lsl #48;           \
        movk    x2, #0x198e, lsl #48;           \
        movk    x3, #0x2406, lsl #48;           \
        stp     x0, x1, [P0];                   \
        stp     x2, x3, [P0+16]

S2N_BN_SYMBOL(edwards25519_epadd_alt):

// Save regs and make room for temporaries

        stp     x19, x20, [sp, -16]!
        sub     sp, sp, #NSPACE

// Move the input arguments to stable places

        mov     p3, x0
        mov     p1, x1
        mov     p2, x2

// Main sequence

        mul_4(t0,w_1,w_2)

        sub_4(t1,y_1,x_1)
        sub_4(t2,y_2,x_2)
        add_4(t3,y_1,x_1)
        add_4(t4,y_2,x_2)
        double_4(t5,z_2)

        mul_4(t1,t1,t2)
        mul_4(t3,t3,t4)

        load_k25519(t2)
        mul_4(t2,t2,t0)

        mul_4(t4,z_1,t5)

        sub_twice4(t0,t3,t1)
        add_twice4(t5,t3,t1)
        sub_twice4(t1,t4,t2)
        add_twice4(t3,t4,t2)

        mul_p25519(w_3,t0,t5)
        mul_p25519(x_3,t0,t1)
        mul_p25519(y_3,t3,t5)
        mul_p25519(z_3,t1,t3)

// Restore stack and registers

        add     sp, sp, #NSPACE
        ldp     x19, x20, [sp], 16

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
