// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point doubling on NIST curve P-384 in Montgomery-Jacobian coordinates
//
//    extern void p384_montjdouble_alt
//      (uint64_t p3[static 18],uint64_t p1[static 18]);
//
// Does p3 := 2 * p1 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^384 * x) mod p_384.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
//
// Standard ARM ABI: X0 = p3, X1 = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p384_montjdouble_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p384_montjdouble_alt)
        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 48

// Stable homes for input arguments during main code sequence

#define input_z x23
#define input_x x24

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

// Corresponds exactly to bignum_montmul_p384_alt

#define montmul_p384(P0,P1,P2)                  \
        ldp     x3, x4, [P1] ASM_LINE_END                   \
        ldp     x5, x6, [P2] ASM_LINE_END                   \
        mul     x12, x3, x5 ASM_LINE_END                    \
        umulh   x13, x3, x5 ASM_LINE_END                    \
        mul     x11, x3, x6 ASM_LINE_END                    \
        umulh   x14, x3, x6 ASM_LINE_END                    \
        adds    x13, x13, x11 ASM_LINE_END                  \
        ldp     x7, x8, [P2+16] ASM_LINE_END                \
        mul     x11, x3, x7 ASM_LINE_END                    \
        umulh   x15, x3, x7 ASM_LINE_END                    \
        adcs    x14, x14, x11 ASM_LINE_END                  \
        mul     x11, x3, x8 ASM_LINE_END                    \
        umulh   x16, x3, x8 ASM_LINE_END                    \
        adcs    x15, x15, x11 ASM_LINE_END                  \
        ldp     x9, x10, [P2+32] ASM_LINE_END               \
        mul     x11, x3, x9 ASM_LINE_END                    \
        umulh   x17, x3, x9 ASM_LINE_END                    \
        adcs    x16, x16, x11 ASM_LINE_END                  \
        mul     x11, x3, x10 ASM_LINE_END                   \
        umulh   x19, x3, x10 ASM_LINE_END                   \
        adcs    x17, x17, x11 ASM_LINE_END                  \
        adc     x19, x19, xzr ASM_LINE_END                  \
        mul     x11, x4, x5 ASM_LINE_END                    \
        adds    x13, x13, x11 ASM_LINE_END                  \
        mul     x11, x4, x6 ASM_LINE_END                    \
        adcs    x14, x14, x11 ASM_LINE_END                  \
        mul     x11, x4, x7 ASM_LINE_END                    \
        adcs    x15, x15, x11 ASM_LINE_END                  \
        mul     x11, x4, x8 ASM_LINE_END                    \
        adcs    x16, x16, x11 ASM_LINE_END                  \
        mul     x11, x4, x9 ASM_LINE_END                    \
        adcs    x17, x17, x11 ASM_LINE_END                  \
        mul     x11, x4, x10 ASM_LINE_END                   \
        adcs    x19, x19, x11 ASM_LINE_END                  \
        cset    x20, cs ASM_LINE_END                        \
        umulh   x11, x4, x5 ASM_LINE_END                    \
        adds    x14, x14, x11 ASM_LINE_END                  \
        umulh   x11, x4, x6 ASM_LINE_END                    \
        adcs    x15, x15, x11 ASM_LINE_END                  \
        umulh   x11, x4, x7 ASM_LINE_END                    \
        adcs    x16, x16, x11 ASM_LINE_END                  \
        umulh   x11, x4, x8 ASM_LINE_END                    \
        adcs    x17, x17, x11 ASM_LINE_END                  \
        umulh   x11, x4, x9 ASM_LINE_END                    \
        adcs    x19, x19, x11 ASM_LINE_END                  \
        umulh   x11, x4, x10 ASM_LINE_END                   \
        adc     x20, x20, x11 ASM_LINE_END                  \
        ldp     x3, x4, [P1+16] ASM_LINE_END                \
        mul     x11, x3, x5 ASM_LINE_END                    \
        adds    x14, x14, x11 ASM_LINE_END                  \
        mul     x11, x3, x6 ASM_LINE_END                    \
        adcs    x15, x15, x11 ASM_LINE_END                  \
        mul     x11, x3, x7 ASM_LINE_END                    \
        adcs    x16, x16, x11 ASM_LINE_END                  \
        mul     x11, x3, x8 ASM_LINE_END                    \
        adcs    x17, x17, x11 ASM_LINE_END                  \
        mul     x11, x3, x9 ASM_LINE_END                    \
        adcs    x19, x19, x11 ASM_LINE_END                  \
        mul     x11, x3, x10 ASM_LINE_END                   \
        adcs    x20, x20, x11 ASM_LINE_END                  \
        cset    x21, cs ASM_LINE_END                        \
        umulh   x11, x3, x5 ASM_LINE_END                    \
        adds    x15, x15, x11 ASM_LINE_END                  \
        umulh   x11, x3, x6 ASM_LINE_END                    \
        adcs    x16, x16, x11 ASM_LINE_END                  \
        umulh   x11, x3, x7 ASM_LINE_END                    \
        adcs    x17, x17, x11 ASM_LINE_END                  \
        umulh   x11, x3, x8 ASM_LINE_END                    \
        adcs    x19, x19, x11 ASM_LINE_END                  \
        umulh   x11, x3, x9 ASM_LINE_END                    \
        adcs    x20, x20, x11 ASM_LINE_END                  \
        umulh   x11, x3, x10 ASM_LINE_END                   \
        adc     x21, x21, x11 ASM_LINE_END                  \
        mul     x11, x4, x5 ASM_LINE_END                    \
        adds    x15, x15, x11 ASM_LINE_END                  \
        mul     x11, x4, x6 ASM_LINE_END                    \
        adcs    x16, x16, x11 ASM_LINE_END                  \
        mul     x11, x4, x7 ASM_LINE_END                    \
        adcs    x17, x17, x11 ASM_LINE_END                  \
        mul     x11, x4, x8 ASM_LINE_END                    \
        adcs    x19, x19, x11 ASM_LINE_END                  \
        mul     x11, x4, x9 ASM_LINE_END                    \
        adcs    x20, x20, x11 ASM_LINE_END                  \
        mul     x11, x4, x10 ASM_LINE_END                   \
        adcs    x21, x21, x11 ASM_LINE_END                  \
        cset    x22, cs ASM_LINE_END                        \
        umulh   x11, x4, x5 ASM_LINE_END                    \
        adds    x16, x16, x11 ASM_LINE_END                  \
        umulh   x11, x4, x6 ASM_LINE_END                    \
        adcs    x17, x17, x11 ASM_LINE_END                  \
        umulh   x11, x4, x7 ASM_LINE_END                    \
        adcs    x19, x19, x11 ASM_LINE_END                  \
        umulh   x11, x4, x8 ASM_LINE_END                    \
        adcs    x20, x20, x11 ASM_LINE_END                  \
        umulh   x11, x4, x9 ASM_LINE_END                    \
        adcs    x21, x21, x11 ASM_LINE_END                  \
        umulh   x11, x4, x10 ASM_LINE_END                   \
        adc     x22, x22, x11 ASM_LINE_END                  \
        ldp     x3, x4, [P1+32] ASM_LINE_END                \
        mul     x11, x3, x5 ASM_LINE_END                    \
        adds    x16, x16, x11 ASM_LINE_END                  \
        mul     x11, x3, x6 ASM_LINE_END                    \
        adcs    x17, x17, x11 ASM_LINE_END                  \
        mul     x11, x3, x7 ASM_LINE_END                    \
        adcs    x19, x19, x11 ASM_LINE_END                  \
        mul     x11, x3, x8 ASM_LINE_END                    \
        adcs    x20, x20, x11 ASM_LINE_END                  \
        mul     x11, x3, x9 ASM_LINE_END                    \
        adcs    x21, x21, x11 ASM_LINE_END                  \
        mul     x11, x3, x10 ASM_LINE_END                   \
        adcs    x22, x22, x11 ASM_LINE_END                  \
        cset    x2, cs ASM_LINE_END                         \
        umulh   x11, x3, x5 ASM_LINE_END                    \
        adds    x17, x17, x11 ASM_LINE_END                  \
        umulh   x11, x3, x6 ASM_LINE_END                    \
        adcs    x19, x19, x11 ASM_LINE_END                  \
        umulh   x11, x3, x7 ASM_LINE_END                    \
        adcs    x20, x20, x11 ASM_LINE_END                  \
        umulh   x11, x3, x8 ASM_LINE_END                    \
        adcs    x21, x21, x11 ASM_LINE_END                  \
        umulh   x11, x3, x9 ASM_LINE_END                    \
        adcs    x22, x22, x11 ASM_LINE_END                  \
        umulh   x11, x3, x10 ASM_LINE_END                   \
        adc     x2, x2, x11 ASM_LINE_END                    \
        mul     x11, x4, x5 ASM_LINE_END                    \
        adds    x17, x17, x11 ASM_LINE_END                  \
        mul     x11, x4, x6 ASM_LINE_END                    \
        adcs    x19, x19, x11 ASM_LINE_END                  \
        mul     x11, x4, x7 ASM_LINE_END                    \
        adcs    x20, x20, x11 ASM_LINE_END                  \
        mul     x11, x4, x8 ASM_LINE_END                    \
        adcs    x21, x21, x11 ASM_LINE_END                  \
        mul     x11, x4, x9 ASM_LINE_END                    \
        adcs    x22, x22, x11 ASM_LINE_END                  \
        mul     x11, x4, x10 ASM_LINE_END                   \
        adcs    x2, x2, x11 ASM_LINE_END                    \
        cset    x1, cs ASM_LINE_END                         \
        umulh   x11, x4, x5 ASM_LINE_END                    \
        adds    x19, x19, x11 ASM_LINE_END                  \
        umulh   x11, x4, x6 ASM_LINE_END                    \
        adcs    x20, x20, x11 ASM_LINE_END                  \
        umulh   x11, x4, x7 ASM_LINE_END                    \
        adcs    x21, x21, x11 ASM_LINE_END                  \
        umulh   x11, x4, x8 ASM_LINE_END                    \
        adcs    x22, x22, x11 ASM_LINE_END                  \
        umulh   x11, x4, x9 ASM_LINE_END                    \
        adcs    x2, x2, x11 ASM_LINE_END                    \
        umulh   x11, x4, x10 ASM_LINE_END                   \
        adc     x1, x1, x11 ASM_LINE_END                    \
        lsl     x7, x12, #32 ASM_LINE_END                   \
        add     x12, x7, x12 ASM_LINE_END                   \
        mov     x7, #0xffffffff00000001 ASM_LINE_END        \
        umulh   x7, x7, x12 ASM_LINE_END                    \
        mov     x6, #0xffffffff ASM_LINE_END                \
        mul     x5, x6, x12 ASM_LINE_END                    \
        umulh   x6, x6, x12 ASM_LINE_END                    \
        adds    x7, x7, x5 ASM_LINE_END                     \
        adcs    x6, x6, x12 ASM_LINE_END                    \
        adc     x5, xzr, xzr ASM_LINE_END                   \
        subs    x13, x13, x7 ASM_LINE_END                   \
        sbcs    x14, x14, x6 ASM_LINE_END                   \
        sbcs    x15, x15, x5 ASM_LINE_END                   \
        sbcs    x16, x16, xzr ASM_LINE_END                  \
        sbcs    x17, x17, xzr ASM_LINE_END                  \
        sbc     x12, x12, xzr ASM_LINE_END                  \
        lsl     x7, x13, #32 ASM_LINE_END                   \
        add     x13, x7, x13 ASM_LINE_END                   \
        mov     x7, #0xffffffff00000001 ASM_LINE_END        \
        umulh   x7, x7, x13 ASM_LINE_END                    \
        mov     x6, #0xffffffff ASM_LINE_END                \
        mul     x5, x6, x13 ASM_LINE_END                    \
        umulh   x6, x6, x13 ASM_LINE_END                    \
        adds    x7, x7, x5 ASM_LINE_END                     \
        adcs    x6, x6, x13 ASM_LINE_END                    \
        adc     x5, xzr, xzr ASM_LINE_END                   \
        subs    x14, x14, x7 ASM_LINE_END                   \
        sbcs    x15, x15, x6 ASM_LINE_END                   \
        sbcs    x16, x16, x5 ASM_LINE_END                   \
        sbcs    x17, x17, xzr ASM_LINE_END                  \
        sbcs    x12, x12, xzr ASM_LINE_END                  \
        sbc     x13, x13, xzr ASM_LINE_END                  \
        lsl     x7, x14, #32 ASM_LINE_END                   \
        add     x14, x7, x14 ASM_LINE_END                   \
        mov     x7, #0xffffffff00000001 ASM_LINE_END        \
        umulh   x7, x7, x14 ASM_LINE_END                    \
        mov     x6, #0xffffffff ASM_LINE_END                \
        mul     x5, x6, x14 ASM_LINE_END                    \
        umulh   x6, x6, x14 ASM_LINE_END                    \
        adds    x7, x7, x5 ASM_LINE_END                     \
        adcs    x6, x6, x14 ASM_LINE_END                    \
        adc     x5, xzr, xzr ASM_LINE_END                   \
        subs    x15, x15, x7 ASM_LINE_END                   \
        sbcs    x16, x16, x6 ASM_LINE_END                   \
        sbcs    x17, x17, x5 ASM_LINE_END                   \
        sbcs    x12, x12, xzr ASM_LINE_END                  \
        sbcs    x13, x13, xzr ASM_LINE_END                  \
        sbc     x14, x14, xzr ASM_LINE_END                  \
        lsl     x7, x15, #32 ASM_LINE_END                   \
        add     x15, x7, x15 ASM_LINE_END                   \
        mov     x7, #0xffffffff00000001 ASM_LINE_END        \
        umulh   x7, x7, x15 ASM_LINE_END                    \
        mov     x6, #0xffffffff ASM_LINE_END                \
        mul     x5, x6, x15 ASM_LINE_END                    \
        umulh   x6, x6, x15 ASM_LINE_END                    \
        adds    x7, x7, x5 ASM_LINE_END                     \
        adcs    x6, x6, x15 ASM_LINE_END                    \
        adc     x5, xzr, xzr ASM_LINE_END                   \
        subs    x16, x16, x7 ASM_LINE_END                   \
        sbcs    x17, x17, x6 ASM_LINE_END                   \
        sbcs    x12, x12, x5 ASM_LINE_END                   \
        sbcs    x13, x13, xzr ASM_LINE_END                  \
        sbcs    x14, x14, xzr ASM_LINE_END                  \
        sbc     x15, x15, xzr ASM_LINE_END                  \
        lsl     x7, x16, #32 ASM_LINE_END                   \
        add     x16, x7, x16 ASM_LINE_END                   \
        mov     x7, #0xffffffff00000001 ASM_LINE_END        \
        umulh   x7, x7, x16 ASM_LINE_END                    \
        mov     x6, #0xffffffff ASM_LINE_END                \
        mul     x5, x6, x16 ASM_LINE_END                    \
        umulh   x6, x6, x16 ASM_LINE_END                    \
        adds    x7, x7, x5 ASM_LINE_END                     \
        adcs    x6, x6, x16 ASM_LINE_END                    \
        adc     x5, xzr, xzr ASM_LINE_END                   \
        subs    x17, x17, x7 ASM_LINE_END                   \
        sbcs    x12, x12, x6 ASM_LINE_END                   \
        sbcs    x13, x13, x5 ASM_LINE_END                   \
        sbcs    x14, x14, xzr ASM_LINE_END                  \
        sbcs    x15, x15, xzr ASM_LINE_END                  \
        sbc     x16, x16, xzr ASM_LINE_END                  \
        lsl     x7, x17, #32 ASM_LINE_END                   \
        add     x17, x7, x17 ASM_LINE_END                   \
        mov     x7, #0xffffffff00000001 ASM_LINE_END        \
        umulh   x7, x7, x17 ASM_LINE_END                    \
        mov     x6, #0xffffffff ASM_LINE_END                \
        mul     x5, x6, x17 ASM_LINE_END                    \
        umulh   x6, x6, x17 ASM_LINE_END                    \
        adds    x7, x7, x5 ASM_LINE_END                     \
        adcs    x6, x6, x17 ASM_LINE_END                    \
        adc     x5, xzr, xzr ASM_LINE_END                   \
        subs    x12, x12, x7 ASM_LINE_END                   \
        sbcs    x13, x13, x6 ASM_LINE_END                   \
        sbcs    x14, x14, x5 ASM_LINE_END                   \
        sbcs    x15, x15, xzr ASM_LINE_END                  \
        sbcs    x16, x16, xzr ASM_LINE_END                  \
        sbc     x17, x17, xzr ASM_LINE_END                  \
        adds    x12, x12, x19 ASM_LINE_END                  \
        adcs    x13, x13, x20 ASM_LINE_END                  \
        adcs    x14, x14, x21 ASM_LINE_END                  \
        adcs    x15, x15, x22 ASM_LINE_END                  \
        adcs    x16, x16, x2 ASM_LINE_END                   \
        adcs    x17, x17, x1 ASM_LINE_END                   \
        adc     x10, xzr, xzr ASM_LINE_END                  \
        mov     x11, #0xffffffff00000001 ASM_LINE_END       \
        adds    x19, x12, x11 ASM_LINE_END                  \
        mov     x11, #0xffffffff ASM_LINE_END               \
        adcs    x20, x13, x11 ASM_LINE_END                  \
        mov     x11, #0x1 ASM_LINE_END                      \
        adcs    x21, x14, x11 ASM_LINE_END                  \
        adcs    x22, x15, xzr ASM_LINE_END                  \
        adcs    x2, x16, xzr ASM_LINE_END                   \
        adcs    x1, x17, xzr ASM_LINE_END                   \
        adcs    x10, x10, xzr ASM_LINE_END                  \
        csel    x12, x12, x19, eq ASM_LINE_END              \
        csel    x13, x13, x20, eq ASM_LINE_END              \
        csel    x14, x14, x21, eq ASM_LINE_END              \
        csel    x15, x15, x22, eq ASM_LINE_END              \
        csel    x16, x16, x2, eq ASM_LINE_END               \
        csel    x17, x17, x1, eq ASM_LINE_END               \
        stp     x12, x13, [P0] ASM_LINE_END                 \
        stp     x14, x15, [P0+16] ASM_LINE_END              \
        stp     x16, x17, [P0+32]

// Corresponds exactly to bignum_montsqr_p384_alt

#define montsqr_p384(P0,P1)                     \
        ldp     x2, x3, [P1] ASM_LINE_END                   \
        mul     x9, x2, x3 ASM_LINE_END                     \
        umulh   x10, x2, x3 ASM_LINE_END                    \
        ldp     x4, x5, [P1+16] ASM_LINE_END                \
        mul     x8, x2, x4 ASM_LINE_END                     \
        adds    x10, x10, x8 ASM_LINE_END                   \
        mul     x11, x2, x5 ASM_LINE_END                    \
        mul     x8, x3, x4 ASM_LINE_END                     \
        adcs    x11, x11, x8 ASM_LINE_END                   \
        umulh   x12, x2, x5 ASM_LINE_END                    \
        mul     x8, x3, x5 ASM_LINE_END                     \
        adcs    x12, x12, x8 ASM_LINE_END                   \
        ldp     x6, x7, [P1+32] ASM_LINE_END                \
        mul     x13, x2, x7 ASM_LINE_END                    \
        mul     x8, x3, x6 ASM_LINE_END                     \
        adcs    x13, x13, x8 ASM_LINE_END                   \
        umulh   x14, x2, x7 ASM_LINE_END                    \
        mul     x8, x3, x7 ASM_LINE_END                     \
        adcs    x14, x14, x8 ASM_LINE_END                   \
        mul     x15, x5, x6 ASM_LINE_END                    \
        adcs    x15, x15, xzr ASM_LINE_END                  \
        umulh   x16, x5, x6 ASM_LINE_END                    \
        adc     x16, x16, xzr ASM_LINE_END                  \
        umulh   x8, x2, x4 ASM_LINE_END                     \
        adds    x11, x11, x8 ASM_LINE_END                   \
        umulh   x8, x3, x4 ASM_LINE_END                     \
        adcs    x12, x12, x8 ASM_LINE_END                   \
        umulh   x8, x3, x5 ASM_LINE_END                     \
        adcs    x13, x13, x8 ASM_LINE_END                   \
        umulh   x8, x3, x6 ASM_LINE_END                     \
        adcs    x14, x14, x8 ASM_LINE_END                   \
        umulh   x8, x3, x7 ASM_LINE_END                     \
        adcs    x15, x15, x8 ASM_LINE_END                   \
        adc     x16, x16, xzr ASM_LINE_END                  \
        mul     x8, x2, x6 ASM_LINE_END                     \
        adds    x12, x12, x8 ASM_LINE_END                   \
        mul     x8, x4, x5 ASM_LINE_END                     \
        adcs    x13, x13, x8 ASM_LINE_END                   \
        mul     x8, x4, x6 ASM_LINE_END                     \
        adcs    x14, x14, x8 ASM_LINE_END                   \
        mul     x8, x4, x7 ASM_LINE_END                     \
        adcs    x15, x15, x8 ASM_LINE_END                   \
        mul     x8, x5, x7 ASM_LINE_END                     \
        adcs    x16, x16, x8 ASM_LINE_END                   \
        mul     x17, x6, x7 ASM_LINE_END                    \
        adcs    x17, x17, xzr ASM_LINE_END                  \
        umulh   x19, x6, x7 ASM_LINE_END                    \
        adc     x19, x19, xzr ASM_LINE_END                  \
        umulh   x8, x2, x6 ASM_LINE_END                     \
        adds    x13, x13, x8 ASM_LINE_END                   \
        umulh   x8, x4, x5 ASM_LINE_END                     \
        adcs    x14, x14, x8 ASM_LINE_END                   \
        umulh   x8, x4, x6 ASM_LINE_END                     \
        adcs    x15, x15, x8 ASM_LINE_END                   \
        umulh   x8, x4, x7 ASM_LINE_END                     \
        adcs    x16, x16, x8 ASM_LINE_END                   \
        umulh   x8, x5, x7 ASM_LINE_END                     \
        adcs    x17, x17, x8 ASM_LINE_END                   \
        adc     x19, x19, xzr ASM_LINE_END                  \
        adds    x9, x9, x9 ASM_LINE_END                     \
        adcs    x10, x10, x10 ASM_LINE_END                  \
        adcs    x11, x11, x11 ASM_LINE_END                  \
        adcs    x12, x12, x12 ASM_LINE_END                  \
        adcs    x13, x13, x13 ASM_LINE_END                  \
        adcs    x14, x14, x14 ASM_LINE_END                  \
        adcs    x15, x15, x15 ASM_LINE_END                  \
        adcs    x16, x16, x16 ASM_LINE_END                  \
        adcs    x17, x17, x17 ASM_LINE_END                  \
        adcs    x19, x19, x19 ASM_LINE_END                  \
        cset    x20, hs ASM_LINE_END                        \
        umulh   x8, x2, x2 ASM_LINE_END                     \
        mul     x2, x2, x2 ASM_LINE_END                     \
        adds    x9, x9, x8 ASM_LINE_END                     \
        mul     x8, x3, x3 ASM_LINE_END                     \
        adcs    x10, x10, x8 ASM_LINE_END                   \
        umulh   x8, x3, x3 ASM_LINE_END                     \
        adcs    x11, x11, x8 ASM_LINE_END                   \
        mul     x8, x4, x4 ASM_LINE_END                     \
        adcs    x12, x12, x8 ASM_LINE_END                   \
        umulh   x8, x4, x4 ASM_LINE_END                     \
        adcs    x13, x13, x8 ASM_LINE_END                   \
        mul     x8, x5, x5 ASM_LINE_END                     \
        adcs    x14, x14, x8 ASM_LINE_END                   \
        umulh   x8, x5, x5 ASM_LINE_END                     \
        adcs    x15, x15, x8 ASM_LINE_END                   \
        mul     x8, x6, x6 ASM_LINE_END                     \
        adcs    x16, x16, x8 ASM_LINE_END                   \
        umulh   x8, x6, x6 ASM_LINE_END                     \
        adcs    x17, x17, x8 ASM_LINE_END                   \
        mul     x8, x7, x7 ASM_LINE_END                     \
        adcs    x19, x19, x8 ASM_LINE_END                   \
        umulh   x8, x7, x7 ASM_LINE_END                     \
        adc     x20, x20, x8 ASM_LINE_END                   \
        lsl     x5, x2, #32 ASM_LINE_END                    \
        add     x2, x5, x2 ASM_LINE_END                     \
        mov     x5, #-4294967295 ASM_LINE_END               \
        umulh   x5, x5, x2 ASM_LINE_END                     \
        mov     x4, #4294967295 ASM_LINE_END                \
        mul     x3, x4, x2 ASM_LINE_END                     \
        umulh   x4, x4, x2 ASM_LINE_END                     \
        adds    x5, x5, x3 ASM_LINE_END                     \
        adcs    x4, x4, x2 ASM_LINE_END                     \
        adc     x3, xzr, xzr ASM_LINE_END                   \
        subs    x9, x9, x5 ASM_LINE_END                     \
        sbcs    x10, x10, x4 ASM_LINE_END                   \
        sbcs    x11, x11, x3 ASM_LINE_END                   \
        sbcs    x12, x12, xzr ASM_LINE_END                  \
        sbcs    x13, x13, xzr ASM_LINE_END                  \
        sbc     x2, x2, xzr ASM_LINE_END                    \
        lsl     x5, x9, #32 ASM_LINE_END                    \
        add     x9, x5, x9 ASM_LINE_END                     \
        mov     x5, #-4294967295 ASM_LINE_END               \
        umulh   x5, x5, x9 ASM_LINE_END                     \
        mov     x4, #4294967295 ASM_LINE_END                \
        mul     x3, x4, x9 ASM_LINE_END                     \
        umulh   x4, x4, x9 ASM_LINE_END                     \
        adds    x5, x5, x3 ASM_LINE_END                     \
        adcs    x4, x4, x9 ASM_LINE_END                     \
        adc     x3, xzr, xzr ASM_LINE_END                   \
        subs    x10, x10, x5 ASM_LINE_END                   \
        sbcs    x11, x11, x4 ASM_LINE_END                   \
        sbcs    x12, x12, x3 ASM_LINE_END                   \
        sbcs    x13, x13, xzr ASM_LINE_END                  \
        sbcs    x2, x2, xzr ASM_LINE_END                    \
        sbc     x9, x9, xzr ASM_LINE_END                    \
        lsl     x5, x10, #32 ASM_LINE_END                   \
        add     x10, x5, x10 ASM_LINE_END                   \
        mov     x5, #-4294967295 ASM_LINE_END               \
        umulh   x5, x5, x10 ASM_LINE_END                    \
        mov     x4, #4294967295 ASM_LINE_END                \
        mul     x3, x4, x10 ASM_LINE_END                    \
        umulh   x4, x4, x10 ASM_LINE_END                    \
        adds    x5, x5, x3 ASM_LINE_END                     \
        adcs    x4, x4, x10 ASM_LINE_END                    \
        adc     x3, xzr, xzr ASM_LINE_END                   \
        subs    x11, x11, x5 ASM_LINE_END                   \
        sbcs    x12, x12, x4 ASM_LINE_END                   \
        sbcs    x13, x13, x3 ASM_LINE_END                   \
        sbcs    x2, x2, xzr ASM_LINE_END                    \
        sbcs    x9, x9, xzr ASM_LINE_END                    \
        sbc     x10, x10, xzr ASM_LINE_END                  \
        lsl     x5, x11, #32 ASM_LINE_END                   \
        add     x11, x5, x11 ASM_LINE_END                   \
        mov     x5, #-4294967295 ASM_LINE_END               \
        umulh   x5, x5, x11 ASM_LINE_END                    \
        mov     x4, #4294967295 ASM_LINE_END                \
        mul     x3, x4, x11 ASM_LINE_END                    \
        umulh   x4, x4, x11 ASM_LINE_END                    \
        adds    x5, x5, x3 ASM_LINE_END                     \
        adcs    x4, x4, x11 ASM_LINE_END                    \
        adc     x3, xzr, xzr ASM_LINE_END                   \
        subs    x12, x12, x5 ASM_LINE_END                   \
        sbcs    x13, x13, x4 ASM_LINE_END                   \
        sbcs    x2, x2, x3 ASM_LINE_END                     \
        sbcs    x9, x9, xzr ASM_LINE_END                    \
        sbcs    x10, x10, xzr ASM_LINE_END                  \
        sbc     x11, x11, xzr ASM_LINE_END                  \
        lsl     x5, x12, #32 ASM_LINE_END                   \
        add     x12, x5, x12 ASM_LINE_END                   \
        mov     x5, #-4294967295 ASM_LINE_END               \
        umulh   x5, x5, x12 ASM_LINE_END                    \
        mov     x4, #4294967295 ASM_LINE_END                \
        mul     x3, x4, x12 ASM_LINE_END                    \
        umulh   x4, x4, x12 ASM_LINE_END                    \
        adds    x5, x5, x3 ASM_LINE_END                     \
        adcs    x4, x4, x12 ASM_LINE_END                    \
        adc     x3, xzr, xzr ASM_LINE_END                   \
        subs    x13, x13, x5 ASM_LINE_END                   \
        sbcs    x2, x2, x4 ASM_LINE_END                     \
        sbcs    x9, x9, x3 ASM_LINE_END                     \
        sbcs    x10, x10, xzr ASM_LINE_END                  \
        sbcs    x11, x11, xzr ASM_LINE_END                  \
        sbc     x12, x12, xzr ASM_LINE_END                  \
        lsl     x5, x13, #32 ASM_LINE_END                   \
        add     x13, x5, x13 ASM_LINE_END                   \
        mov     x5, #-4294967295 ASM_LINE_END               \
        umulh   x5, x5, x13 ASM_LINE_END                    \
        mov     x4, #4294967295 ASM_LINE_END                \
        mul     x3, x4, x13 ASM_LINE_END                    \
        umulh   x4, x4, x13 ASM_LINE_END                    \
        adds    x5, x5, x3 ASM_LINE_END                     \
        adcs    x4, x4, x13 ASM_LINE_END                    \
        adc     x3, xzr, xzr ASM_LINE_END                   \
        subs    x2, x2, x5 ASM_LINE_END                     \
        sbcs    x9, x9, x4 ASM_LINE_END                     \
        sbcs    x10, x10, x3 ASM_LINE_END                   \
        sbcs    x11, x11, xzr ASM_LINE_END                  \
        sbcs    x12, x12, xzr ASM_LINE_END                  \
        sbc     x13, x13, xzr ASM_LINE_END                  \
        adds    x2, x2, x14 ASM_LINE_END                    \
        adcs    x9, x9, x15 ASM_LINE_END                    \
        adcs    x10, x10, x16 ASM_LINE_END                  \
        adcs    x11, x11, x17 ASM_LINE_END                  \
        adcs    x12, x12, x19 ASM_LINE_END                  \
        adcs    x13, x13, x20 ASM_LINE_END                  \
        adc     x6, xzr, xzr ASM_LINE_END                   \
        mov     x8, #-4294967295 ASM_LINE_END               \
        adds    x14, x2, x8 ASM_LINE_END                    \
        mov     x8, #4294967295 ASM_LINE_END                \
        adcs    x15, x9, x8 ASM_LINE_END                    \
        mov     x8, #1 ASM_LINE_END                         \
        adcs    x16, x10, x8 ASM_LINE_END                   \
        adcs    x17, x11, xzr ASM_LINE_END                  \
        adcs    x19, x12, xzr ASM_LINE_END                  \
        adcs    x20, x13, xzr ASM_LINE_END                  \
        adcs    x6, x6, xzr ASM_LINE_END                    \
        csel    x2, x2, x14, eq ASM_LINE_END                \
        csel    x9, x9, x15, eq ASM_LINE_END                \
        csel    x10, x10, x16, eq ASM_LINE_END              \
        csel    x11, x11, x17, eq ASM_LINE_END              \
        csel    x12, x12, x19, eq ASM_LINE_END              \
        csel    x13, x13, x20, eq ASM_LINE_END              \
        stp     x2, x9, [P0] ASM_LINE_END                   \
        stp     x10, x11, [P0+16] ASM_LINE_END              \
        stp     x12, x13, [P0+32]

// Corresponds exactly to bignum_sub_p384

#define sub_p384(P0,P1,P2)                      \
        ldp     x5, x6, [P1] ASM_LINE_END                   \
        ldp     x4, x3, [P2] ASM_LINE_END                   \
        subs    x5, x5, x4 ASM_LINE_END                     \
        sbcs    x6, x6, x3 ASM_LINE_END                     \
        ldp     x7, x8, [P1+16] ASM_LINE_END                \
        ldp     x4, x3, [P2+16] ASM_LINE_END                \
        sbcs    x7, x7, x4 ASM_LINE_END                     \
        sbcs    x8, x8, x3 ASM_LINE_END                     \
        ldp     x9, x10, [P1+32] ASM_LINE_END               \
        ldp     x4, x3, [P2+32] ASM_LINE_END                \
        sbcs    x9, x9, x4 ASM_LINE_END                     \
        sbcs    x10, x10, x3 ASM_LINE_END                   \
        csetm   x3, lo ASM_LINE_END                         \
        mov     x4, #4294967295 ASM_LINE_END                \
        and     x4, x4, x3 ASM_LINE_END                     \
        adds    x5, x5, x4 ASM_LINE_END                     \
        eor     x4, x4, x3 ASM_LINE_END                     \
        adcs    x6, x6, x4 ASM_LINE_END                     \
        mov     x4, #-2 ASM_LINE_END                        \
        and     x4, x4, x3 ASM_LINE_END                     \
        adcs    x7, x7, x4 ASM_LINE_END                     \
        adcs    x8, x8, x3 ASM_LINE_END                     \
        adcs    x9, x9, x3 ASM_LINE_END                     \
        adc     x10, x10, x3 ASM_LINE_END                   \
        stp     x5, x6, [P0] ASM_LINE_END                   \
        stp     x7, x8, [P0+16] ASM_LINE_END                \
        stp     x9, x10, [P0+32]

// Corresponds exactly to bignum_add_p384

#define add_p384(P0,P1,P2)                      \
        ldp     x5, x6, [P1] ASM_LINE_END                   \
        ldp     x4, x3, [P2] ASM_LINE_END                   \
        adds    x5, x5, x4 ASM_LINE_END                     \
        adcs    x6, x6, x3 ASM_LINE_END                     \
        ldp     x7, x8, [P1+16] ASM_LINE_END                \
        ldp     x4, x3, [P2+16] ASM_LINE_END                \
        adcs    x7, x7, x4 ASM_LINE_END                     \
        adcs    x8, x8, x3 ASM_LINE_END                     \
        ldp     x9, x10, [P1+32] ASM_LINE_END               \
        ldp     x4, x3, [P2+32] ASM_LINE_END                \
        adcs    x9, x9, x4 ASM_LINE_END                     \
        adcs    x10, x10, x3 ASM_LINE_END                   \
        adc     x3, xzr, xzr ASM_LINE_END                   \
        mov     x4, #0xffffffff ASM_LINE_END                \
        cmp     x5, x4 ASM_LINE_END                         \
        mov     x4, #0xffffffff00000000 ASM_LINE_END        \
        sbcs    xzr, x6, x4 ASM_LINE_END                    \
        mov     x4, #0xfffffffffffffffe ASM_LINE_END        \
        sbcs    xzr, x7, x4 ASM_LINE_END                    \
        adcs    xzr, x8, xzr ASM_LINE_END                   \
        adcs    xzr, x9, xzr ASM_LINE_END                   \
        adcs    xzr, x10, xzr ASM_LINE_END                  \
        adcs    x3, x3, xzr ASM_LINE_END                    \
        csetm   x3, ne ASM_LINE_END                         \
        mov     x4, #0xffffffff ASM_LINE_END                \
        and     x4, x4, x3 ASM_LINE_END                     \
        subs    x5, x5, x4 ASM_LINE_END                     \
        eor     x4, x4, x3 ASM_LINE_END                     \
        sbcs    x6, x6, x4 ASM_LINE_END                     \
        mov     x4, #0xfffffffffffffffe ASM_LINE_END        \
        and     x4, x4, x3 ASM_LINE_END                     \
        sbcs    x7, x7, x4 ASM_LINE_END                     \
        sbcs    x8, x8, x3 ASM_LINE_END                     \
        sbcs    x9, x9, x3 ASM_LINE_END                     \
        sbc     x10, x10, x3 ASM_LINE_END                   \
        stp     x5, x6, [P0] ASM_LINE_END                   \
        stp     x7, x8, [P0+16] ASM_LINE_END                \
        stp     x9, x10, [P0+32]

// P0 = 4 * P1 - P2

#define cmsub41_p384(P0,P1,P2)                  \
        ldp     x1, x2, [P1] ASM_LINE_END                   \
        ldp     x3, x4, [P1+16] ASM_LINE_END                \
        ldp     x5, x6, [P1+32] ASM_LINE_END                \
        lsl     x0, x1, #2 ASM_LINE_END                     \
        ldp     x7, x8, [P2] ASM_LINE_END                   \
        subs    x0, x0, x7 ASM_LINE_END                     \
        extr    x1, x2, x1, #62 ASM_LINE_END                \
        sbcs    x1, x1, x8 ASM_LINE_END                     \
        ldp     x7, x8, [P2+16] ASM_LINE_END                \
        extr    x2, x3, x2, #62 ASM_LINE_END                \
        sbcs    x2, x2, x7 ASM_LINE_END                     \
        extr    x3, x4, x3, #62 ASM_LINE_END                \
        sbcs    x3, x3, x8 ASM_LINE_END                     \
        extr    x4, x5, x4, #62 ASM_LINE_END                \
        ldp     x7, x8, [P2+32] ASM_LINE_END                \
        sbcs    x4, x4, x7 ASM_LINE_END                     \
        extr    x5, x6, x5, #62 ASM_LINE_END                \
        sbcs    x5, x5, x8 ASM_LINE_END                     \
        lsr     x6, x6, #62 ASM_LINE_END                    \
        adc     x6, x6, xzr ASM_LINE_END                    \
        lsl     x7, x6, #32 ASM_LINE_END                    \
        subs    x8, x6, x7 ASM_LINE_END                     \
        sbc     x7, x7, xzr ASM_LINE_END                    \
        adds    x0, x0, x8 ASM_LINE_END                     \
        adcs    x1, x1, x7 ASM_LINE_END                     \
        adcs    x2, x2, x6 ASM_LINE_END                     \
        adcs    x3, x3, xzr ASM_LINE_END                    \
        adcs    x4, x4, xzr ASM_LINE_END                    \
        adcs    x5, x5, xzr ASM_LINE_END                    \
        csetm   x8, cc ASM_LINE_END                         \
        mov     x9, #0xffffffff ASM_LINE_END                \
        and     x9, x9, x8 ASM_LINE_END                     \
        adds    x0, x0, x9 ASM_LINE_END                     \
        eor     x9, x9, x8 ASM_LINE_END                     \
        adcs    x1, x1, x9 ASM_LINE_END                     \
        mov     x9, #0xfffffffffffffffe ASM_LINE_END        \
        and     x9, x9, x8 ASM_LINE_END                     \
        adcs    x2, x2, x9 ASM_LINE_END                     \
        adcs    x3, x3, x8 ASM_LINE_END                     \
        adcs    x4, x4, x8 ASM_LINE_END                     \
        adc     x5, x5, x8 ASM_LINE_END                     \
        stp     x0, x1, [P0] ASM_LINE_END                   \
        stp     x2, x3, [P0+16] ASM_LINE_END                \
        stp     x4, x5, [P0+32]

// P0 = C * P1 - D * P2

#define cmsub_p384(P0,C,P1,D,P2)                \
        ldp     x0, x1, [P2] ASM_LINE_END                   \
        mov     x6, #0x00000000ffffffff ASM_LINE_END        \
        subs    x6, x6, x0 ASM_LINE_END                     \
        mov     x7, #0xffffffff00000000 ASM_LINE_END        \
        sbcs    x7, x7, x1 ASM_LINE_END                     \
        ldp     x0, x1, [P2+16] ASM_LINE_END                \
        mov     x8, #0xfffffffffffffffe ASM_LINE_END        \
        sbcs    x8, x8, x0 ASM_LINE_END                     \
        mov     x13, #0xffffffffffffffff ASM_LINE_END       \
        sbcs    x9, x13, x1 ASM_LINE_END                    \
        ldp     x0, x1, [P2+32] ASM_LINE_END                \
        sbcs    x10, x13, x0 ASM_LINE_END                   \
        sbc     x11, x13, x1 ASM_LINE_END                   \
        mov     x12, D ASM_LINE_END                         \
        mul     x0, x12, x6 ASM_LINE_END                    \
        mul     x1, x12, x7 ASM_LINE_END                    \
        mul     x2, x12, x8 ASM_LINE_END                    \
        mul     x3, x12, x9 ASM_LINE_END                    \
        mul     x4, x12, x10 ASM_LINE_END                   \
        mul     x5, x12, x11 ASM_LINE_END                   \
        umulh   x6, x12, x6 ASM_LINE_END                    \
        umulh   x7, x12, x7 ASM_LINE_END                    \
        umulh   x8, x12, x8 ASM_LINE_END                    \
        umulh   x9, x12, x9 ASM_LINE_END                    \
        umulh   x10, x12, x10 ASM_LINE_END                  \
        umulh   x12, x12, x11 ASM_LINE_END                  \
        adds    x1, x1, x6 ASM_LINE_END                     \
        adcs    x2, x2, x7 ASM_LINE_END                     \
        adcs    x3, x3, x8 ASM_LINE_END                     \
        adcs    x4, x4, x9 ASM_LINE_END                     \
        adcs    x5, x5, x10 ASM_LINE_END                    \
        mov     x6, #1 ASM_LINE_END                         \
        adc     x6, x12, x6 ASM_LINE_END                    \
        ldp     x8, x9, [P1] ASM_LINE_END                   \
        ldp     x10, x11, [P1+16] ASM_LINE_END              \
        ldp     x12, x13, [P1+32] ASM_LINE_END              \
        mov     x14, C ASM_LINE_END                         \
        mul     x15, x14, x8 ASM_LINE_END                   \
        umulh   x8, x14, x8 ASM_LINE_END                    \
        adds    x0, x0, x15 ASM_LINE_END                    \
        mul     x15, x14, x9 ASM_LINE_END                   \
        umulh   x9, x14, x9 ASM_LINE_END                    \
        adcs    x1, x1, x15 ASM_LINE_END                    \
        mul     x15, x14, x10 ASM_LINE_END                  \
        umulh   x10, x14, x10 ASM_LINE_END                  \
        adcs    x2, x2, x15 ASM_LINE_END                    \
        mul     x15, x14, x11 ASM_LINE_END                  \
        umulh   x11, x14, x11 ASM_LINE_END                  \
        adcs    x3, x3, x15 ASM_LINE_END                    \
        mul     x15, x14, x12 ASM_LINE_END                  \
        umulh   x12, x14, x12 ASM_LINE_END                  \
        adcs    x4, x4, x15 ASM_LINE_END                    \
        mul     x15, x14, x13 ASM_LINE_END                  \
        umulh   x13, x14, x13 ASM_LINE_END                  \
        adcs    x5, x5, x15 ASM_LINE_END                    \
        adc     x6, x6, xzr ASM_LINE_END                    \
        adds    x1, x1, x8 ASM_LINE_END                     \
        adcs    x2, x2, x9 ASM_LINE_END                     \
        adcs    x3, x3, x10 ASM_LINE_END                    \
        adcs    x4, x4, x11 ASM_LINE_END                    \
        adcs    x5, x5, x12 ASM_LINE_END                    \
        adcs    x6, x6, x13 ASM_LINE_END                    \
        lsl     x7, x6, #32 ASM_LINE_END                    \
        subs    x8, x6, x7 ASM_LINE_END                     \
        sbc     x7, x7, xzr ASM_LINE_END                    \
        adds    x0, x0, x8 ASM_LINE_END                     \
        adcs    x1, x1, x7 ASM_LINE_END                     \
        adcs    x2, x2, x6 ASM_LINE_END                     \
        adcs    x3, x3, xzr ASM_LINE_END                    \
        adcs    x4, x4, xzr ASM_LINE_END                    \
        adcs    x5, x5, xzr ASM_LINE_END                    \
        csetm   x6, cc ASM_LINE_END                         \
        mov     x7, #0xffffffff ASM_LINE_END                \
        and     x7, x7, x6 ASM_LINE_END                     \
        adds    x0, x0, x7 ASM_LINE_END                     \
        eor     x7, x7, x6 ASM_LINE_END                     \
        adcs    x1, x1, x7 ASM_LINE_END                     \
        mov     x7, #0xfffffffffffffffe ASM_LINE_END        \
        and     x7, x7, x6 ASM_LINE_END                     \
        adcs    x2, x2, x7 ASM_LINE_END                     \
        adcs    x3, x3, x6 ASM_LINE_END                     \
        adcs    x4, x4, x6 ASM_LINE_END                     \
        adc     x5, x5, x6 ASM_LINE_END                     \
        stp     x0, x1, [P0] ASM_LINE_END                   \
        stp     x2, x3, [P0+16] ASM_LINE_END                \
        stp     x4, x5, [P0+32]

// A weak version of add that only guarantees sum in 6 digits

#define weakadd_p384(P0,P1,P2)                  \
        ldp     x5, x6, [P1] ASM_LINE_END                   \
        ldp     x4, x3, [P2] ASM_LINE_END                   \
        adds    x5, x5, x4 ASM_LINE_END                     \
        adcs    x6, x6, x3 ASM_LINE_END                     \
        ldp     x7, x8, [P1+16] ASM_LINE_END                \
        ldp     x4, x3, [P2+16] ASM_LINE_END                \
        adcs    x7, x7, x4 ASM_LINE_END                     \
        adcs    x8, x8, x3 ASM_LINE_END                     \
        ldp     x9, x10, [P1+32] ASM_LINE_END               \
        ldp     x4, x3, [P2+32] ASM_LINE_END                \
        adcs    x9, x9, x4 ASM_LINE_END                     \
        adcs    x10, x10, x3 ASM_LINE_END                   \
        csetm   x3, cs ASM_LINE_END                         \
        mov     x4, #0xffffffff ASM_LINE_END                \
        and     x4, x4, x3 ASM_LINE_END                     \
        subs    x5, x5, x4 ASM_LINE_END                     \
        eor     x4, x4, x3 ASM_LINE_END                     \
        sbcs    x6, x6, x4 ASM_LINE_END                     \
        mov     x4, #0xfffffffffffffffe ASM_LINE_END        \
        and     x4, x4, x3 ASM_LINE_END                     \
        sbcs    x7, x7, x4 ASM_LINE_END                     \
        sbcs    x8, x8, x3 ASM_LINE_END                     \
        sbcs    x9, x9, x3 ASM_LINE_END                     \
        sbc     x10, x10, x3 ASM_LINE_END                   \
        stp     x5, x6, [P0] ASM_LINE_END                   \
        stp     x7, x8, [P0+16] ASM_LINE_END                \
        stp     x9, x10, [P0+32]

// P0 = 3 * P1 - 8 * P2

#define cmsub38_p384(P0,P1,P2)                  \
        ldp     x0, x1, [P2] ASM_LINE_END                   \
        mov     x6, #0x00000000ffffffff ASM_LINE_END        \
        subs    x6, x6, x0 ASM_LINE_END                     \
        mov     x7, #0xffffffff00000000 ASM_LINE_END        \
        sbcs    x7, x7, x1 ASM_LINE_END                     \
        ldp     x0, x1, [P2+16] ASM_LINE_END                \
        mov     x8, #0xfffffffffffffffe ASM_LINE_END        \
        sbcs    x8, x8, x0 ASM_LINE_END                     \
        mov     x13, #0xffffffffffffffff ASM_LINE_END       \
        sbcs    x9, x13, x1 ASM_LINE_END                    \
        ldp     x0, x1, [P2+32] ASM_LINE_END                \
        sbcs    x10, x13, x0 ASM_LINE_END                   \
        sbc     x11, x13, x1 ASM_LINE_END                   \
        lsl     x0, x6, #3 ASM_LINE_END                     \
        extr    x1, x7, x6, #61 ASM_LINE_END                \
        extr    x2, x8, x7, #61 ASM_LINE_END                \
        extr    x3, x9, x8, #61 ASM_LINE_END                \
        extr    x4, x10, x9, #61 ASM_LINE_END               \
        extr    x5, x11, x10, #61 ASM_LINE_END              \
        lsr     x6, x11, #61 ASM_LINE_END                   \
        add     x6, x6, #1 ASM_LINE_END                     \
        ldp     x8, x9, [P1] ASM_LINE_END                   \
        ldp     x10, x11, [P1+16] ASM_LINE_END              \
        ldp     x12, x13, [P1+32] ASM_LINE_END              \
        mov     x14, 3 ASM_LINE_END                         \
        mul     x15, x14, x8 ASM_LINE_END                   \
        umulh   x8, x14, x8 ASM_LINE_END                    \
        adds    x0, x0, x15 ASM_LINE_END                    \
        mul     x15, x14, x9 ASM_LINE_END                   \
        umulh   x9, x14, x9 ASM_LINE_END                    \
        adcs    x1, x1, x15 ASM_LINE_END                    \
        mul     x15, x14, x10 ASM_LINE_END                  \
        umulh   x10, x14, x10 ASM_LINE_END                  \
        adcs    x2, x2, x15 ASM_LINE_END                    \
        mul     x15, x14, x11 ASM_LINE_END                  \
        umulh   x11, x14, x11 ASM_LINE_END                  \
        adcs    x3, x3, x15 ASM_LINE_END                    \
        mul     x15, x14, x12 ASM_LINE_END                  \
        umulh   x12, x14, x12 ASM_LINE_END                  \
        adcs    x4, x4, x15 ASM_LINE_END                    \
        mul     x15, x14, x13 ASM_LINE_END                  \
        umulh   x13, x14, x13 ASM_LINE_END                  \
        adcs    x5, x5, x15 ASM_LINE_END                    \
        adc     x6, x6, xzr ASM_LINE_END                    \
        adds    x1, x1, x8 ASM_LINE_END                     \
        adcs    x2, x2, x9 ASM_LINE_END                     \
        adcs    x3, x3, x10 ASM_LINE_END                    \
        adcs    x4, x4, x11 ASM_LINE_END                    \
        adcs    x5, x5, x12 ASM_LINE_END                    \
        adcs    x6, x6, x13 ASM_LINE_END                    \
        lsl     x7, x6, #32 ASM_LINE_END                    \
        subs    x8, x6, x7 ASM_LINE_END                     \
        sbc     x7, x7, xzr ASM_LINE_END                    \
        adds    x0, x0, x8 ASM_LINE_END                     \
        adcs    x1, x1, x7 ASM_LINE_END                     \
        adcs    x2, x2, x6 ASM_LINE_END                     \
        adcs    x3, x3, xzr ASM_LINE_END                    \
        adcs    x4, x4, xzr ASM_LINE_END                    \
        adcs    x5, x5, xzr ASM_LINE_END                    \
        csetm   x6, cc ASM_LINE_END                         \
        mov     x7, #0xffffffff ASM_LINE_END                \
        and     x7, x7, x6 ASM_LINE_END                     \
        adds    x0, x0, x7 ASM_LINE_END                     \
        eor     x7, x7, x6 ASM_LINE_END                     \
        adcs    x1, x1, x7 ASM_LINE_END                     \
        mov     x7, #0xfffffffffffffffe ASM_LINE_END        \
        and     x7, x7, x6 ASM_LINE_END                     \
        adcs    x2, x2, x7 ASM_LINE_END                     \
        adcs    x3, x3, x6 ASM_LINE_END                     \
        adcs    x4, x4, x6 ASM_LINE_END                     \
        adc     x5, x5, x6 ASM_LINE_END                     \
        stp     x0, x1, [P0] ASM_LINE_END                   \
        stp     x2, x3, [P0+16] ASM_LINE_END                \
        stp     x4, x5, [P0+32]

S2N_BN_SYMBOL(p384_montjdouble_alt):

// Save regs and make room on stack for temporary variables

        stp     x19, x20, [sp, #-16]!
        stp     x21, x22, [sp, #-16]!
        stp     x23, x24, [sp, #-16]!
        sub     sp, sp, NSPACE

// Move the input arguments to stable places

        mov     input_z, x0
        mov     input_x, x1

// Main code, just a sequence of basic field operations

// z2 = z^2
// y2 = y^2

        montsqr_p384(z2,z_1)
        montsqr_p384(y2,y_1)

// x2p = x^2 - z^4 = (x + z^2) * (x - z^2)

        weakadd_p384(t1,x_1,z2)
        sub_p384(t2,x_1,z2)
        montmul_p384(x2p,t1,t2)

// t1 = y + z
// x4p = x2p^2
// xy2 = x * y^2

        add_p384(t1,y_1,z_1)
        montsqr_p384(x4p,x2p)
        montmul_p384(xy2,x_1,y2)

// t2 = (y + z)^2

        montsqr_p384(t2,t1)

// d = 12 * xy2 - 9 * x4p
// t1 = y^2 + 2 * y * z

        cmsub_p384(d,12,xy2,9,x4p)
        sub_p384(t1,t2,z2)

// y4 = y^4

        montsqr_p384(y4,y2)

// z_3' = 2 * y * z
// dx2 = d * x2p

        sub_p384(z_3,t1,y2)
        montmul_p384(dx2,d,x2p)

// x' = 4 * xy2 - d

        cmsub41_p384(x_3,xy2,d)

// y' = 3 * dx2 - 8 * y4

        cmsub38_p384(y_3,dx2,y4)

// Restore stack and registers

        add     sp, sp, NSPACE

        ldp     x23, x24, [sp], 16
        ldp     x21, x22, [sp], 16
        ldp     x19, x20, [sp], 16

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
