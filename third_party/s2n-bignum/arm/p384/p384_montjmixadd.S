// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point mixed addition on NIST curve P-384 in Montgomery-Jacobian coordinates
//
//    extern void p384_montjmixadd
//      (uint64_t p3[static 18],uint64_t p1[static 18],uint64_t p2[static 12]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^384 * x) mod p_384.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
// The "mixed" part means that p2 only has x and y coordinates, with the
// implicit z coordinate assumed to be the identity.
//
// Standard ARM ABI: X0 = p3, X1 = p1, X2 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p384_montjmixadd)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p384_montjmixadd)
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

// Corresponds to bignum_montmul_p384 except x24 -> x0

#define montmul_p384(P0,P1,P2)                  \
        ldp     x3, x4, [P1] ASM_LINE_END                   \
        ldp     x5, x6, [P1+16] ASM_LINE_END                \
        ldp     x7, x8, [P1+32] ASM_LINE_END                \
        ldp     x9, x10, [P2] ASM_LINE_END                  \
        ldp     x11, x12, [P2+16] ASM_LINE_END              \
        ldp     x13, x14, [P2+32] ASM_LINE_END              \
        mul     x15, x3, x9 ASM_LINE_END                    \
        mul     x21, x4, x10 ASM_LINE_END                   \
        mul     x22, x5, x11 ASM_LINE_END                   \
        umulh   x23, x3, x9 ASM_LINE_END                    \
        umulh   x0, x4, x10 ASM_LINE_END                    \
        umulh   x1, x5, x11 ASM_LINE_END                    \
        adds    x23, x23, x21 ASM_LINE_END                  \
        adcs    x0, x0, x22 ASM_LINE_END                    \
        adc     x1, x1, xzr ASM_LINE_END                    \
        adds    x16, x23, x15 ASM_LINE_END                  \
        adcs    x17, x0, x23 ASM_LINE_END                   \
        adcs    x19, x1, x0 ASM_LINE_END                    \
        adc     x20, x1, xzr ASM_LINE_END                   \
        adds    x17, x17, x15 ASM_LINE_END                  \
        adcs    x19, x19, x23 ASM_LINE_END                  \
        adcs    x20, x20, x0 ASM_LINE_END                   \
        adc     x1, x1, xzr ASM_LINE_END                    \
        subs    x0, x3, x4 ASM_LINE_END                     \
        cneg    x0, x0, lo ASM_LINE_END                     \
        csetm   x23, lo ASM_LINE_END                        \
        subs    x22, x10, x9 ASM_LINE_END                   \
        cneg    x22, x22, lo ASM_LINE_END                   \
        mul     x21, x0, x22 ASM_LINE_END                   \
        umulh   x22, x0, x22 ASM_LINE_END                   \
        cinv    x23, x23, lo ASM_LINE_END                   \
        eor     x21, x21, x23 ASM_LINE_END                  \
        eor     x22, x22, x23 ASM_LINE_END                  \
        cmn     x23, #1 ASM_LINE_END                        \
        adcs    x16, x16, x21 ASM_LINE_END                  \
        adcs    x17, x17, x22 ASM_LINE_END                  \
        adcs    x19, x19, x23 ASM_LINE_END                  \
        adcs    x20, x20, x23 ASM_LINE_END                  \
        adc     x1, x1, x23 ASM_LINE_END                    \
        subs    x0, x3, x5 ASM_LINE_END                     \
        cneg    x0, x0, lo ASM_LINE_END                     \
        csetm   x23, lo ASM_LINE_END                        \
        subs    x22, x11, x9 ASM_LINE_END                   \
        cneg    x22, x22, lo ASM_LINE_END                   \
        mul     x21, x0, x22 ASM_LINE_END                   \
        umulh   x22, x0, x22 ASM_LINE_END                   \
        cinv    x23, x23, lo ASM_LINE_END                   \
        eor     x21, x21, x23 ASM_LINE_END                  \
        eor     x22, x22, x23 ASM_LINE_END                  \
        cmn     x23, #1 ASM_LINE_END                        \
        adcs    x17, x17, x21 ASM_LINE_END                  \
        adcs    x19, x19, x22 ASM_LINE_END                  \
        adcs    x20, x20, x23 ASM_LINE_END                  \
        adc     x1, x1, x23 ASM_LINE_END                    \
        subs    x0, x4, x5 ASM_LINE_END                     \
        cneg    x0, x0, lo ASM_LINE_END                     \
        csetm   x23, lo ASM_LINE_END                        \
        subs    x22, x11, x10 ASM_LINE_END                  \
        cneg    x22, x22, lo ASM_LINE_END                   \
        mul     x21, x0, x22 ASM_LINE_END                   \
        umulh   x22, x0, x22 ASM_LINE_END                   \
        cinv    x23, x23, lo ASM_LINE_END                   \
        eor     x21, x21, x23 ASM_LINE_END                  \
        eor     x22, x22, x23 ASM_LINE_END                  \
        cmn     x23, #1 ASM_LINE_END                        \
        adcs    x19, x19, x21 ASM_LINE_END                  \
        adcs    x20, x20, x22 ASM_LINE_END                  \
        adc     x1, x1, x23 ASM_LINE_END                    \
        lsl     x23, x15, #32 ASM_LINE_END                  \
        add     x15, x23, x15 ASM_LINE_END                  \
        lsr     x23, x15, #32 ASM_LINE_END                  \
        subs    x23, x23, x15 ASM_LINE_END                  \
        sbc     x22, x15, xzr ASM_LINE_END                  \
        extr    x23, x22, x23, #32 ASM_LINE_END             \
        lsr     x22, x22, #32 ASM_LINE_END                  \
        adds    x22, x22, x15 ASM_LINE_END                  \
        adc     x21, xzr, xzr ASM_LINE_END                  \
        subs    x16, x16, x23 ASM_LINE_END                  \
        sbcs    x17, x17, x22 ASM_LINE_END                  \
        sbcs    x19, x19, x21 ASM_LINE_END                  \
        sbcs    x20, x20, xzr ASM_LINE_END                  \
        sbcs    x1, x1, xzr ASM_LINE_END                    \
        sbc     x15, x15, xzr ASM_LINE_END                  \
        lsl     x23, x16, #32 ASM_LINE_END                  \
        add     x16, x23, x16 ASM_LINE_END                  \
        lsr     x23, x16, #32 ASM_LINE_END                  \
        subs    x23, x23, x16 ASM_LINE_END                  \
        sbc     x22, x16, xzr ASM_LINE_END                  \
        extr    x23, x22, x23, #32 ASM_LINE_END             \
        lsr     x22, x22, #32 ASM_LINE_END                  \
        adds    x22, x22, x16 ASM_LINE_END                  \
        adc     x21, xzr, xzr ASM_LINE_END                  \
        subs    x17, x17, x23 ASM_LINE_END                  \
        sbcs    x19, x19, x22 ASM_LINE_END                  \
        sbcs    x20, x20, x21 ASM_LINE_END                  \
        sbcs    x1, x1, xzr ASM_LINE_END                    \
        sbcs    x15, x15, xzr ASM_LINE_END                  \
        sbc     x16, x16, xzr ASM_LINE_END                  \
        lsl     x23, x17, #32 ASM_LINE_END                  \
        add     x17, x23, x17 ASM_LINE_END                  \
        lsr     x23, x17, #32 ASM_LINE_END                  \
        subs    x23, x23, x17 ASM_LINE_END                  \
        sbc     x22, x17, xzr ASM_LINE_END                  \
        extr    x23, x22, x23, #32 ASM_LINE_END             \
        lsr     x22, x22, #32 ASM_LINE_END                  \
        adds    x22, x22, x17 ASM_LINE_END                  \
        adc     x21, xzr, xzr ASM_LINE_END                  \
        subs    x19, x19, x23 ASM_LINE_END                  \
        sbcs    x20, x20, x22 ASM_LINE_END                  \
        sbcs    x1, x1, x21 ASM_LINE_END                    \
        sbcs    x15, x15, xzr ASM_LINE_END                  \
        sbcs    x16, x16, xzr ASM_LINE_END                  \
        sbc     x17, x17, xzr ASM_LINE_END                  \
        stp     x19, x20, [P0] ASM_LINE_END                 \
        stp     x1, x15, [P0+16] ASM_LINE_END               \
        stp     x16, x17, [P0+32] ASM_LINE_END              \
        mul     x15, x6, x12 ASM_LINE_END                   \
        mul     x21, x7, x13 ASM_LINE_END                   \
        mul     x22, x8, x14 ASM_LINE_END                   \
        umulh   x23, x6, x12 ASM_LINE_END                   \
        umulh   x0, x7, x13 ASM_LINE_END                    \
        umulh   x1, x8, x14 ASM_LINE_END                    \
        adds    x23, x23, x21 ASM_LINE_END                  \
        adcs    x0, x0, x22 ASM_LINE_END                    \
        adc     x1, x1, xzr ASM_LINE_END                    \
        adds    x16, x23, x15 ASM_LINE_END                  \
        adcs    x17, x0, x23 ASM_LINE_END                   \
        adcs    x19, x1, x0 ASM_LINE_END                    \
        adc     x20, x1, xzr ASM_LINE_END                   \
        adds    x17, x17, x15 ASM_LINE_END                  \
        adcs    x19, x19, x23 ASM_LINE_END                  \
        adcs    x20, x20, x0 ASM_LINE_END                   \
        adc     x1, x1, xzr ASM_LINE_END                    \
        subs    x0, x6, x7 ASM_LINE_END                     \
        cneg    x0, x0, lo ASM_LINE_END                     \
        csetm   x23, lo ASM_LINE_END                        \
        subs    x22, x13, x12 ASM_LINE_END                  \
        cneg    x22, x22, lo ASM_LINE_END                   \
        mul     x21, x0, x22 ASM_LINE_END                   \
        umulh   x22, x0, x22 ASM_LINE_END                   \
        cinv    x23, x23, lo ASM_LINE_END                   \
        eor     x21, x21, x23 ASM_LINE_END                  \
        eor     x22, x22, x23 ASM_LINE_END                  \
        cmn     x23, #1 ASM_LINE_END                        \
        adcs    x16, x16, x21 ASM_LINE_END                  \
        adcs    x17, x17, x22 ASM_LINE_END                  \
        adcs    x19, x19, x23 ASM_LINE_END                  \
        adcs    x20, x20, x23 ASM_LINE_END                  \
        adc     x1, x1, x23 ASM_LINE_END                    \
        subs    x0, x6, x8 ASM_LINE_END                     \
        cneg    x0, x0, lo ASM_LINE_END                     \
        csetm   x23, lo ASM_LINE_END                        \
        subs    x22, x14, x12 ASM_LINE_END                  \
        cneg    x22, x22, lo ASM_LINE_END                   \
        mul     x21, x0, x22 ASM_LINE_END                   \
        umulh   x22, x0, x22 ASM_LINE_END                   \
        cinv    x23, x23, lo ASM_LINE_END                   \
        eor     x21, x21, x23 ASM_LINE_END                  \
        eor     x22, x22, x23 ASM_LINE_END                  \
        cmn     x23, #1 ASM_LINE_END                        \
        adcs    x17, x17, x21 ASM_LINE_END                  \
        adcs    x19, x19, x22 ASM_LINE_END                  \
        adcs    x20, x20, x23 ASM_LINE_END                  \
        adc     x1, x1, x23 ASM_LINE_END                    \
        subs    x0, x7, x8 ASM_LINE_END                     \
        cneg    x0, x0, lo ASM_LINE_END                     \
        csetm   x23, lo ASM_LINE_END                        \
        subs    x22, x14, x13 ASM_LINE_END                  \
        cneg    x22, x22, lo ASM_LINE_END                   \
        mul     x21, x0, x22 ASM_LINE_END                   \
        umulh   x22, x0, x22 ASM_LINE_END                   \
        cinv    x23, x23, lo ASM_LINE_END                   \
        eor     x21, x21, x23 ASM_LINE_END                  \
        eor     x22, x22, x23 ASM_LINE_END                  \
        cmn     x23, #1 ASM_LINE_END                        \
        adcs    x19, x19, x21 ASM_LINE_END                  \
        adcs    x20, x20, x22 ASM_LINE_END                  \
        adc     x1, x1, x23 ASM_LINE_END                    \
        subs    x6, x6, x3 ASM_LINE_END                     \
        sbcs    x7, x7, x4 ASM_LINE_END                     \
        sbcs    x8, x8, x5 ASM_LINE_END                     \
        ngc     x3, xzr ASM_LINE_END                        \
        cmn     x3, #1 ASM_LINE_END                         \
        eor     x6, x6, x3 ASM_LINE_END                     \
        adcs    x6, x6, xzr ASM_LINE_END                    \
        eor     x7, x7, x3 ASM_LINE_END                     \
        adcs    x7, x7, xzr ASM_LINE_END                    \
        eor     x8, x8, x3 ASM_LINE_END                     \
        adc     x8, x8, xzr ASM_LINE_END                    \
        subs    x9, x9, x12 ASM_LINE_END                    \
        sbcs    x10, x10, x13 ASM_LINE_END                  \
        sbcs    x11, x11, x14 ASM_LINE_END                  \
        ngc     x14, xzr ASM_LINE_END                       \
        cmn     x14, #1 ASM_LINE_END                        \
        eor     x9, x9, x14 ASM_LINE_END                    \
        adcs    x9, x9, xzr ASM_LINE_END                    \
        eor     x10, x10, x14 ASM_LINE_END                  \
        adcs    x10, x10, xzr ASM_LINE_END                  \
        eor     x11, x11, x14 ASM_LINE_END                  \
        adc     x11, x11, xzr ASM_LINE_END                  \
        eor     x14, x3, x14 ASM_LINE_END                   \
        ldp     x21, x22, [P0] ASM_LINE_END                 \
        adds    x15, x15, x21 ASM_LINE_END                  \
        adcs    x16, x16, x22 ASM_LINE_END                  \
        ldp     x21, x22, [P0+16] ASM_LINE_END              \
        adcs    x17, x17, x21 ASM_LINE_END                  \
        adcs    x19, x19, x22 ASM_LINE_END                  \
        ldp     x21, x22, [P0+32] ASM_LINE_END              \
        adcs    x20, x20, x21 ASM_LINE_END                  \
        adcs    x1, x1, x22 ASM_LINE_END                    \
        adc     x2, xzr, xzr ASM_LINE_END                   \
        stp     x15, x16, [P0] ASM_LINE_END                 \
        stp     x17, x19, [P0+16] ASM_LINE_END              \
        stp     x20, x1, [P0+32] ASM_LINE_END               \
        mul     x15, x6, x9 ASM_LINE_END                    \
        mul     x21, x7, x10 ASM_LINE_END                   \
        mul     x22, x8, x11 ASM_LINE_END                   \
        umulh   x23, x6, x9 ASM_LINE_END                    \
        umulh   x0, x7, x10 ASM_LINE_END                    \
        umulh   x1, x8, x11 ASM_LINE_END                    \
        adds    x23, x23, x21 ASM_LINE_END                  \
        adcs    x0, x0, x22 ASM_LINE_END                    \
        adc     x1, x1, xzr ASM_LINE_END                    \
        adds    x16, x23, x15 ASM_LINE_END                  \
        adcs    x17, x0, x23 ASM_LINE_END                   \
        adcs    x19, x1, x0 ASM_LINE_END                    \
        adc     x20, x1, xzr ASM_LINE_END                   \
        adds    x17, x17, x15 ASM_LINE_END                  \
        adcs    x19, x19, x23 ASM_LINE_END                  \
        adcs    x20, x20, x0 ASM_LINE_END                   \
        adc     x1, x1, xzr ASM_LINE_END                    \
        subs    x0, x6, x7 ASM_LINE_END                     \
        cneg    x0, x0, lo ASM_LINE_END                     \
        csetm   x23, lo ASM_LINE_END                        \
        subs    x22, x10, x9 ASM_LINE_END                   \
        cneg    x22, x22, lo ASM_LINE_END                   \
        mul     x21, x0, x22 ASM_LINE_END                   \
        umulh   x22, x0, x22 ASM_LINE_END                   \
        cinv    x23, x23, lo ASM_LINE_END                   \
        eor     x21, x21, x23 ASM_LINE_END                  \
        eor     x22, x22, x23 ASM_LINE_END                  \
        cmn     x23, #1 ASM_LINE_END                        \
        adcs    x16, x16, x21 ASM_LINE_END                  \
        adcs    x17, x17, x22 ASM_LINE_END                  \
        adcs    x19, x19, x23 ASM_LINE_END                  \
        adcs    x20, x20, x23 ASM_LINE_END                  \
        adc     x1, x1, x23 ASM_LINE_END                    \
        subs    x0, x6, x8 ASM_LINE_END                     \
        cneg    x0, x0, lo ASM_LINE_END                     \
        csetm   x23, lo ASM_LINE_END                        \
        subs    x22, x11, x9 ASM_LINE_END                   \
        cneg    x22, x22, lo ASM_LINE_END                   \
        mul     x21, x0, x22 ASM_LINE_END                   \
        umulh   x22, x0, x22 ASM_LINE_END                   \
        cinv    x23, x23, lo ASM_LINE_END                   \
        eor     x21, x21, x23 ASM_LINE_END                  \
        eor     x22, x22, x23 ASM_LINE_END                  \
        cmn     x23, #1 ASM_LINE_END                        \
        adcs    x17, x17, x21 ASM_LINE_END                  \
        adcs    x19, x19, x22 ASM_LINE_END                  \
        adcs    x20, x20, x23 ASM_LINE_END                  \
        adc     x1, x1, x23 ASM_LINE_END                    \
        subs    x0, x7, x8 ASM_LINE_END                     \
        cneg    x0, x0, lo ASM_LINE_END                     \
        csetm   x23, lo ASM_LINE_END                        \
        subs    x22, x11, x10 ASM_LINE_END                  \
        cneg    x22, x22, lo ASM_LINE_END                   \
        mul     x21, x0, x22 ASM_LINE_END                   \
        umulh   x22, x0, x22 ASM_LINE_END                   \
        cinv    x23, x23, lo ASM_LINE_END                   \
        eor     x21, x21, x23 ASM_LINE_END                  \
        eor     x22, x22, x23 ASM_LINE_END                  \
        cmn     x23, #1 ASM_LINE_END                        \
        adcs    x19, x19, x21 ASM_LINE_END                  \
        adcs    x20, x20, x22 ASM_LINE_END                  \
        adc     x1, x1, x23 ASM_LINE_END                    \
        ldp     x3, x4, [P0] ASM_LINE_END                   \
        ldp     x5, x6, [P0+16] ASM_LINE_END                \
        ldp     x7, x8, [P0+32] ASM_LINE_END                \
        cmn     x14, #1 ASM_LINE_END                        \
        eor     x15, x15, x14 ASM_LINE_END                  \
        adcs    x15, x15, x3 ASM_LINE_END                   \
        eor     x16, x16, x14 ASM_LINE_END                  \
        adcs    x16, x16, x4 ASM_LINE_END                   \
        eor     x17, x17, x14 ASM_LINE_END                  \
        adcs    x17, x17, x5 ASM_LINE_END                   \
        eor     x19, x19, x14 ASM_LINE_END                  \
        adcs    x19, x19, x6 ASM_LINE_END                   \
        eor     x20, x20, x14 ASM_LINE_END                  \
        adcs    x20, x20, x7 ASM_LINE_END                   \
        eor     x1, x1, x14 ASM_LINE_END                    \
        adcs    x1, x1, x8 ASM_LINE_END                     \
        adcs    x9, x14, x2 ASM_LINE_END                    \
        adcs    x10, x14, xzr ASM_LINE_END                  \
        adcs    x11, x14, xzr ASM_LINE_END                  \
        adc     x12, x14, xzr ASM_LINE_END                  \
        adds    x19, x19, x3 ASM_LINE_END                   \
        adcs    x20, x20, x4 ASM_LINE_END                   \
        adcs    x1, x1, x5 ASM_LINE_END                     \
        adcs    x9, x9, x6 ASM_LINE_END                     \
        adcs    x10, x10, x7 ASM_LINE_END                   \
        adcs    x11, x11, x8 ASM_LINE_END                   \
        adc     x12, x12, x2 ASM_LINE_END                   \
        lsl     x23, x15, #32 ASM_LINE_END                  \
        add     x15, x23, x15 ASM_LINE_END                  \
        lsr     x23, x15, #32 ASM_LINE_END                  \
        subs    x23, x23, x15 ASM_LINE_END                  \
        sbc     x22, x15, xzr ASM_LINE_END                  \
        extr    x23, x22, x23, #32 ASM_LINE_END             \
        lsr     x22, x22, #32 ASM_LINE_END                  \
        adds    x22, x22, x15 ASM_LINE_END                  \
        adc     x21, xzr, xzr ASM_LINE_END                  \
        subs    x16, x16, x23 ASM_LINE_END                  \
        sbcs    x17, x17, x22 ASM_LINE_END                  \
        sbcs    x19, x19, x21 ASM_LINE_END                  \
        sbcs    x20, x20, xzr ASM_LINE_END                  \
        sbcs    x1, x1, xzr ASM_LINE_END                    \
        sbc     x15, x15, xzr ASM_LINE_END                  \
        lsl     x23, x16, #32 ASM_LINE_END                  \
        add     x16, x23, x16 ASM_LINE_END                  \
        lsr     x23, x16, #32 ASM_LINE_END                  \
        subs    x23, x23, x16 ASM_LINE_END                  \
        sbc     x22, x16, xzr ASM_LINE_END                  \
        extr    x23, x22, x23, #32 ASM_LINE_END             \
        lsr     x22, x22, #32 ASM_LINE_END                  \
        adds    x22, x22, x16 ASM_LINE_END                  \
        adc     x21, xzr, xzr ASM_LINE_END                  \
        subs    x17, x17, x23 ASM_LINE_END                  \
        sbcs    x19, x19, x22 ASM_LINE_END                  \
        sbcs    x20, x20, x21 ASM_LINE_END                  \
        sbcs    x1, x1, xzr ASM_LINE_END                    \
        sbcs    x15, x15, xzr ASM_LINE_END                  \
        sbc     x16, x16, xzr ASM_LINE_END                  \
        lsl     x23, x17, #32 ASM_LINE_END                  \
        add     x17, x23, x17 ASM_LINE_END                  \
        lsr     x23, x17, #32 ASM_LINE_END                  \
        subs    x23, x23, x17 ASM_LINE_END                  \
        sbc     x22, x17, xzr ASM_LINE_END                  \
        extr    x23, x22, x23, #32 ASM_LINE_END             \
        lsr     x22, x22, #32 ASM_LINE_END                  \
        adds    x22, x22, x17 ASM_LINE_END                  \
        adc     x21, xzr, xzr ASM_LINE_END                  \
        subs    x19, x19, x23 ASM_LINE_END                  \
        sbcs    x20, x20, x22 ASM_LINE_END                  \
        sbcs    x1, x1, x21 ASM_LINE_END                    \
        sbcs    x15, x15, xzr ASM_LINE_END                  \
        sbcs    x16, x16, xzr ASM_LINE_END                  \
        sbc     x17, x17, xzr ASM_LINE_END                  \
        adds    x9, x9, x15 ASM_LINE_END                    \
        adcs    x10, x10, x16 ASM_LINE_END                  \
        adcs    x11, x11, x17 ASM_LINE_END                  \
        adc     x12, x12, xzr ASM_LINE_END                  \
        add     x22, x12, #1 ASM_LINE_END                   \
        lsl     x21, x22, #32 ASM_LINE_END                  \
        subs    x0, x22, x21 ASM_LINE_END                   \
        sbc     x21, x21, xzr ASM_LINE_END                  \
        adds    x19, x19, x0 ASM_LINE_END                   \
        adcs    x20, x20, x21 ASM_LINE_END                  \
        adcs    x1, x1, x22 ASM_LINE_END                    \
        adcs    x9, x9, xzr ASM_LINE_END                    \
        adcs    x10, x10, xzr ASM_LINE_END                  \
        adcs    x11, x11, xzr ASM_LINE_END                  \
        csetm   x22, lo ASM_LINE_END                        \
        mov     x23, #4294967295 ASM_LINE_END               \
        and     x23, x23, x22 ASM_LINE_END                  \
        adds    x19, x19, x23 ASM_LINE_END                  \
        eor     x23, x23, x22 ASM_LINE_END                  \
        adcs    x20, x20, x23 ASM_LINE_END                  \
        mov     x23, #-2 ASM_LINE_END                       \
        and     x23, x23, x22 ASM_LINE_END                  \
        adcs    x1, x1, x23 ASM_LINE_END                    \
        adcs    x9, x9, x22 ASM_LINE_END                    \
        adcs    x10, x10, x22 ASM_LINE_END                  \
        adc     x11, x11, x22 ASM_LINE_END                  \
        stp     x19, x20, [P0] ASM_LINE_END                 \
        stp     x1, x9, [P0+16] ASM_LINE_END                \
        stp     x10, x11, [P0+32]

// Corresponds exactly to bignum_montsqr_p384

#define montsqr_p384(P0,P1)                     \
        ldp     x2, x3, [P1] ASM_LINE_END                   \
        ldp     x4, x5, [P1+16] ASM_LINE_END                \
        ldp     x6, x7, [P1+32] ASM_LINE_END                \
        mul     x14, x2, x3 ASM_LINE_END                    \
        mul     x15, x2, x4 ASM_LINE_END                    \
        mul     x16, x3, x4 ASM_LINE_END                    \
        mul     x8, x2, x2 ASM_LINE_END                     \
        mul     x10, x3, x3 ASM_LINE_END                    \
        mul     x12, x4, x4 ASM_LINE_END                    \
        umulh   x17, x2, x3 ASM_LINE_END                    \
        adds    x15, x15, x17 ASM_LINE_END                  \
        umulh   x17, x2, x4 ASM_LINE_END                    \
        adcs    x16, x16, x17 ASM_LINE_END                  \
        umulh   x17, x3, x4 ASM_LINE_END                    \
        adcs    x17, x17, xzr ASM_LINE_END                  \
        umulh   x9, x2, x2 ASM_LINE_END                     \
        umulh   x11, x3, x3 ASM_LINE_END                    \
        umulh   x13, x4, x4 ASM_LINE_END                    \
        adds    x14, x14, x14 ASM_LINE_END                  \
        adcs    x15, x15, x15 ASM_LINE_END                  \
        adcs    x16, x16, x16 ASM_LINE_END                  \
        adcs    x17, x17, x17 ASM_LINE_END                  \
        adc     x13, x13, xzr ASM_LINE_END                  \
        adds    x9, x9, x14 ASM_LINE_END                    \
        adcs    x10, x10, x15 ASM_LINE_END                  \
        adcs    x11, x11, x16 ASM_LINE_END                  \
        adcs    x12, x12, x17 ASM_LINE_END                  \
        adc     x13, x13, xzr ASM_LINE_END                  \
        lsl     x16, x8, #32 ASM_LINE_END                   \
        add     x8, x16, x8 ASM_LINE_END                    \
        lsr     x16, x8, #32 ASM_LINE_END                   \
        subs    x16, x16, x8 ASM_LINE_END                   \
        sbc     x15, x8, xzr ASM_LINE_END                   \
        extr    x16, x15, x16, #32 ASM_LINE_END             \
        lsr     x15, x15, #32 ASM_LINE_END                  \
        adds    x15, x15, x8 ASM_LINE_END                   \
        adc     x14, xzr, xzr ASM_LINE_END                  \
        subs    x9, x9, x16 ASM_LINE_END                    \
        sbcs    x10, x10, x15 ASM_LINE_END                  \
        sbcs    x11, x11, x14 ASM_LINE_END                  \
        sbcs    x12, x12, xzr ASM_LINE_END                  \
        sbcs    x13, x13, xzr ASM_LINE_END                  \
        sbc     x8, x8, xzr ASM_LINE_END                    \
        lsl     x16, x9, #32 ASM_LINE_END                   \
        add     x9, x16, x9 ASM_LINE_END                    \
        lsr     x16, x9, #32 ASM_LINE_END                   \
        subs    x16, x16, x9 ASM_LINE_END                   \
        sbc     x15, x9, xzr ASM_LINE_END                   \
        extr    x16, x15, x16, #32 ASM_LINE_END             \
        lsr     x15, x15, #32 ASM_LINE_END                  \
        adds    x15, x15, x9 ASM_LINE_END                   \
        adc     x14, xzr, xzr ASM_LINE_END                  \
        subs    x10, x10, x16 ASM_LINE_END                  \
        sbcs    x11, x11, x15 ASM_LINE_END                  \
        sbcs    x12, x12, x14 ASM_LINE_END                  \
        sbcs    x13, x13, xzr ASM_LINE_END                  \
        sbcs    x8, x8, xzr ASM_LINE_END                    \
        sbc     x9, x9, xzr ASM_LINE_END                    \
        lsl     x16, x10, #32 ASM_LINE_END                  \
        add     x10, x16, x10 ASM_LINE_END                  \
        lsr     x16, x10, #32 ASM_LINE_END                  \
        subs    x16, x16, x10 ASM_LINE_END                  \
        sbc     x15, x10, xzr ASM_LINE_END                  \
        extr    x16, x15, x16, #32 ASM_LINE_END             \
        lsr     x15, x15, #32 ASM_LINE_END                  \
        adds    x15, x15, x10 ASM_LINE_END                  \
        adc     x14, xzr, xzr ASM_LINE_END                  \
        subs    x11, x11, x16 ASM_LINE_END                  \
        sbcs    x12, x12, x15 ASM_LINE_END                  \
        sbcs    x13, x13, x14 ASM_LINE_END                  \
        sbcs    x8, x8, xzr ASM_LINE_END                    \
        sbcs    x9, x9, xzr ASM_LINE_END                    \
        sbc     x10, x10, xzr ASM_LINE_END                  \
        stp     x11, x12, [P0] ASM_LINE_END                 \
        stp     x13, x8, [P0+16] ASM_LINE_END               \
        stp     x9, x10, [P0+32] ASM_LINE_END               \
        mul     x8, x2, x5 ASM_LINE_END                     \
        mul     x14, x3, x6 ASM_LINE_END                    \
        mul     x15, x4, x7 ASM_LINE_END                    \
        umulh   x16, x2, x5 ASM_LINE_END                    \
        umulh   x17, x3, x6 ASM_LINE_END                    \
        umulh   x1, x4, x7 ASM_LINE_END                     \
        adds    x16, x16, x14 ASM_LINE_END                  \
        adcs    x17, x17, x15 ASM_LINE_END                  \
        adc     x1, x1, xzr ASM_LINE_END                    \
        adds    x9, x16, x8 ASM_LINE_END                    \
        adcs    x10, x17, x16 ASM_LINE_END                  \
        adcs    x11, x1, x17 ASM_LINE_END                   \
        adc     x12, x1, xzr ASM_LINE_END                   \
        adds    x10, x10, x8 ASM_LINE_END                   \
        adcs    x11, x11, x16 ASM_LINE_END                  \
        adcs    x12, x12, x17 ASM_LINE_END                  \
        adc     x13, x1, xzr ASM_LINE_END                   \
        subs    x17, x2, x3 ASM_LINE_END                    \
        cneg    x17, x17, lo ASM_LINE_END                   \
        csetm   x14, lo ASM_LINE_END                        \
        subs    x15, x6, x5 ASM_LINE_END                    \
        cneg    x15, x15, lo ASM_LINE_END                   \
        mul     x16, x17, x15 ASM_LINE_END                  \
        umulh   x15, x17, x15 ASM_LINE_END                  \
        cinv    x14, x14, lo ASM_LINE_END                   \
        eor     x16, x16, x14 ASM_LINE_END                  \
        eor     x15, x15, x14 ASM_LINE_END                  \
        cmn     x14, #1 ASM_LINE_END                        \
        adcs    x9, x9, x16 ASM_LINE_END                    \
        adcs    x10, x10, x15 ASM_LINE_END                  \
        adcs    x11, x11, x14 ASM_LINE_END                  \
        adcs    x12, x12, x14 ASM_LINE_END                  \
        adc     x13, x13, x14 ASM_LINE_END                  \
        subs    x17, x2, x4 ASM_LINE_END                    \
        cneg    x17, x17, lo ASM_LINE_END                   \
        csetm   x14, lo ASM_LINE_END                        \
        subs    x15, x7, x5 ASM_LINE_END                    \
        cneg    x15, x15, lo ASM_LINE_END                   \
        mul     x16, x17, x15 ASM_LINE_END                  \
        umulh   x15, x17, x15 ASM_LINE_END                  \
        cinv    x14, x14, lo ASM_LINE_END                   \
        eor     x16, x16, x14 ASM_LINE_END                  \
        eor     x15, x15, x14 ASM_LINE_END                  \
        cmn     x14, #1 ASM_LINE_END                        \
        adcs    x10, x10, x16 ASM_LINE_END                  \
        adcs    x11, x11, x15 ASM_LINE_END                  \
        adcs    x12, x12, x14 ASM_LINE_END                  \
        adc     x13, x13, x14 ASM_LINE_END                  \
        subs    x17, x3, x4 ASM_LINE_END                    \
        cneg    x17, x17, lo ASM_LINE_END                   \
        csetm   x14, lo ASM_LINE_END                        \
        subs    x15, x7, x6 ASM_LINE_END                    \
        cneg    x15, x15, lo ASM_LINE_END                   \
        mul     x16, x17, x15 ASM_LINE_END                  \
        umulh   x15, x17, x15 ASM_LINE_END                  \
        cinv    x14, x14, lo ASM_LINE_END                   \
        eor     x16, x16, x14 ASM_LINE_END                  \
        eor     x15, x15, x14 ASM_LINE_END                  \
        cmn     x14, #1 ASM_LINE_END                        \
        adcs    x11, x11, x16 ASM_LINE_END                  \
        adcs    x12, x12, x15 ASM_LINE_END                  \
        adc     x13, x13, x14 ASM_LINE_END                  \
        adds    x8, x8, x8 ASM_LINE_END                     \
        adcs    x9, x9, x9 ASM_LINE_END                     \
        adcs    x10, x10, x10 ASM_LINE_END                  \
        adcs    x11, x11, x11 ASM_LINE_END                  \
        adcs    x12, x12, x12 ASM_LINE_END                  \
        adcs    x13, x13, x13 ASM_LINE_END                  \
        adc     x17, xzr, xzr ASM_LINE_END                  \
        ldp     x2, x3, [P0] ASM_LINE_END                   \
        adds    x8, x8, x2 ASM_LINE_END                     \
        adcs    x9, x9, x3 ASM_LINE_END                     \
        ldp     x2, x3, [P0+16] ASM_LINE_END                \
        adcs    x10, x10, x2 ASM_LINE_END                   \
        adcs    x11, x11, x3 ASM_LINE_END                   \
        ldp     x2, x3, [P0+32] ASM_LINE_END                \
        adcs    x12, x12, x2 ASM_LINE_END                   \
        adcs    x13, x13, x3 ASM_LINE_END                   \
        adc     x17, x17, xzr ASM_LINE_END                  \
        lsl     x4, x8, #32 ASM_LINE_END                    \
        add     x8, x4, x8 ASM_LINE_END                     \
        lsr     x4, x8, #32 ASM_LINE_END                    \
        subs    x4, x4, x8 ASM_LINE_END                     \
        sbc     x3, x8, xzr ASM_LINE_END                    \
        extr    x4, x3, x4, #32 ASM_LINE_END                \
        lsr     x3, x3, #32 ASM_LINE_END                    \
        adds    x3, x3, x8 ASM_LINE_END                     \
        adc     x2, xzr, xzr ASM_LINE_END                   \
        subs    x9, x9, x4 ASM_LINE_END                     \
        sbcs    x10, x10, x3 ASM_LINE_END                   \
        sbcs    x11, x11, x2 ASM_LINE_END                   \
        sbcs    x12, x12, xzr ASM_LINE_END                  \
        sbcs    x13, x13, xzr ASM_LINE_END                  \
        sbc     x8, x8, xzr ASM_LINE_END                    \
        lsl     x4, x9, #32 ASM_LINE_END                    \
        add     x9, x4, x9 ASM_LINE_END                     \
        lsr     x4, x9, #32 ASM_LINE_END                    \
        subs    x4, x4, x9 ASM_LINE_END                     \
        sbc     x3, x9, xzr ASM_LINE_END                    \
        extr    x4, x3, x4, #32 ASM_LINE_END                \
        lsr     x3, x3, #32 ASM_LINE_END                    \
        adds    x3, x3, x9 ASM_LINE_END                     \
        adc     x2, xzr, xzr ASM_LINE_END                   \
        subs    x10, x10, x4 ASM_LINE_END                   \
        sbcs    x11, x11, x3 ASM_LINE_END                   \
        sbcs    x12, x12, x2 ASM_LINE_END                   \
        sbcs    x13, x13, xzr ASM_LINE_END                  \
        sbcs    x8, x8, xzr ASM_LINE_END                    \
        sbc     x9, x9, xzr ASM_LINE_END                    \
        lsl     x4, x10, #32 ASM_LINE_END                   \
        add     x10, x4, x10 ASM_LINE_END                   \
        lsr     x4, x10, #32 ASM_LINE_END                   \
        subs    x4, x4, x10 ASM_LINE_END                    \
        sbc     x3, x10, xzr ASM_LINE_END                   \
        extr    x4, x3, x4, #32 ASM_LINE_END                \
        lsr     x3, x3, #32 ASM_LINE_END                    \
        adds    x3, x3, x10 ASM_LINE_END                    \
        adc     x2, xzr, xzr ASM_LINE_END                   \
        subs    x11, x11, x4 ASM_LINE_END                   \
        sbcs    x12, x12, x3 ASM_LINE_END                   \
        sbcs    x13, x13, x2 ASM_LINE_END                   \
        sbcs    x8, x8, xzr ASM_LINE_END                    \
        sbcs    x9, x9, xzr ASM_LINE_END                    \
        sbc     x10, x10, xzr ASM_LINE_END                  \
        adds    x17, x17, x8 ASM_LINE_END                   \
        adcs    x8, x9, xzr ASM_LINE_END                    \
        adcs    x9, x10, xzr ASM_LINE_END                   \
        adcs    x10, xzr, xzr ASM_LINE_END                  \
        mul     x1, x5, x5 ASM_LINE_END                     \
        adds    x11, x11, x1 ASM_LINE_END                   \
        mul     x14, x6, x6 ASM_LINE_END                    \
        mul     x15, x7, x7 ASM_LINE_END                    \
        umulh   x1, x5, x5 ASM_LINE_END                     \
        adcs    x12, x12, x1 ASM_LINE_END                   \
        umulh   x1, x6, x6 ASM_LINE_END                     \
        adcs    x13, x13, x14 ASM_LINE_END                  \
        adcs    x17, x17, x1 ASM_LINE_END                   \
        umulh   x1, x7, x7 ASM_LINE_END                     \
        adcs    x8, x8, x15 ASM_LINE_END                    \
        adcs    x9, x9, x1 ASM_LINE_END                     \
        adc     x10, x10, xzr ASM_LINE_END                  \
        mul     x1, x5, x6 ASM_LINE_END                     \
        mul     x14, x5, x7 ASM_LINE_END                    \
        mul     x15, x6, x7 ASM_LINE_END                    \
        umulh   x16, x5, x6 ASM_LINE_END                    \
        adds    x14, x14, x16 ASM_LINE_END                  \
        umulh   x16, x5, x7 ASM_LINE_END                    \
        adcs    x15, x15, x16 ASM_LINE_END                  \
        umulh   x16, x6, x7 ASM_LINE_END                    \
        adc     x16, x16, xzr ASM_LINE_END                  \
        adds    x1, x1, x1 ASM_LINE_END                     \
        adcs    x14, x14, x14 ASM_LINE_END                  \
        adcs    x15, x15, x15 ASM_LINE_END                  \
        adcs    x16, x16, x16 ASM_LINE_END                  \
        adc     x5, xzr, xzr ASM_LINE_END                   \
        adds    x12, x12, x1 ASM_LINE_END                   \
        adcs    x13, x13, x14 ASM_LINE_END                  \
        adcs    x17, x17, x15 ASM_LINE_END                  \
        adcs    x8, x8, x16 ASM_LINE_END                    \
        adcs    x9, x9, x5 ASM_LINE_END                     \
        adc     x10, x10, xzr ASM_LINE_END                  \
        mov     x1, #-4294967295 ASM_LINE_END               \
        mov     x14, #4294967295 ASM_LINE_END               \
        mov     x15, #1 ASM_LINE_END                        \
        cmn     x11, x1 ASM_LINE_END                        \
        adcs    xzr, x12, x14 ASM_LINE_END                  \
        adcs    xzr, x13, x15 ASM_LINE_END                  \
        adcs    xzr, x17, xzr ASM_LINE_END                  \
        adcs    xzr, x8, xzr ASM_LINE_END                   \
        adcs    xzr, x9, xzr ASM_LINE_END                   \
        adc     x10, x10, xzr ASM_LINE_END                  \
        neg     x10, x10 ASM_LINE_END                       \
        and     x1, x1, x10 ASM_LINE_END                    \
        adds    x11, x11, x1 ASM_LINE_END                   \
        and     x14, x14, x10 ASM_LINE_END                  \
        adcs    x12, x12, x14 ASM_LINE_END                  \
        and     x15, x15, x10 ASM_LINE_END                  \
        adcs    x13, x13, x15 ASM_LINE_END                  \
        adcs    x17, x17, xzr ASM_LINE_END                  \
        adcs    x8, x8, xzr ASM_LINE_END                    \
        adc     x9, x9, xzr ASM_LINE_END                    \
        stp     x11, x12, [P0] ASM_LINE_END                 \
        stp     x13, x17, [P0+16] ASM_LINE_END              \
        stp     x8, x9, [P0+32]

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

S2N_BN_SYMBOL(p384_montjmixadd):

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

        montsqr_p384(zp2,z_1)
        montmul_p384(y2a,z_1,y_2)

        montmul_p384(x2a,zp2,x_2)
        montmul_p384(y2a,zp2,y2a)

        sub_p384(xd,x2a,x_1)
        sub_p384(yd,y2a,y_1)

        montsqr_p384(zz,xd)
        montsqr_p384(ww,yd)

        montmul_p384(zzx1,zz,x_1)
        montmul_p384(zzx2,zz,x2a)

        sub_p384(resx,ww,zzx1)
        sub_p384(t1,zzx2,zzx1)

        montmul_p384(resz,xd,z_1)

        sub_p384(resx,resx,zzx2)

        sub_p384(t2,zzx1,resx)

        montmul_p384(t1,t1,y_1)
        montmul_p384(t2,yd,t2)

        sub_p384(resy,t2,t1)

// Test if z_1 = 0 to decide if p1 = 0 (up to projective equivalence)

        ldp     x0, x1, [z_1]
        ldp     x2, x3, [z_1+16]
        ldp     x4, x5, [z_1+32]
        orr     x6, x0, x1
        orr     x7, x2, x3
        orr     x8, x4, x5
        orr     x6, x6, x7
        orr     x6, x6, x8
        cmp     x6, xzr

// Multiplex: if p1 <> 0 just copy the computed result from the staging area.
// If p1 = 0 then return the point p2 augmented with a z = 1 coordinate (in
// Montgomery form so not the simple constant 1 but rather 2^384 - p_384),
// hence giving 0 + p2 = p2 for the final result.

        ldp     x0, x1, [resx]
        ldp     x19, x20, [x_2]
        csel    x0, x0, x19, ne
        csel    x1, x1, x20, ne
        ldp     x2, x3, [resx+16]
        ldp     x19, x20, [x_2+16]
        csel    x2, x2, x19, ne
        csel    x3, x3, x20, ne
        ldp     x4, x5, [resx+32]
        ldp     x19, x20, [x_2+32]
        csel    x4, x4, x19, ne
        csel    x5, x5, x20, ne

        ldp     x6, x7, [resy]
        ldp     x19, x20, [y_2]
        csel    x6, x6, x19, ne
        csel    x7, x7, x20, ne
        ldp     x8, x9, [resy+16]
        ldp     x19, x20, [y_2+16]
        csel    x8, x8, x19, ne
        csel    x9, x9, x20, ne
        ldp     x10, x11, [resy+32]
        ldp     x19, x20, [y_2+32]
        csel    x10, x10, x19, ne
        csel    x11, x11, x20, ne

        ldp     x12, x13, [resz]
        mov     x19, #0xffffffff00000001
        mov     x20, #0x00000000ffffffff
        csel    x12, x12, x19, ne
        csel    x13, x13, x20, ne
        ldp     x14, x15, [resz+16]
        mov     x19, #1
        csel    x14, x14, x19, ne
        csel    x15, x15, xzr, ne
        ldp     x16, x17, [resz+32]
        csel    x16, x16, xzr, ne
        csel    x17, x17, xzr, ne

        stp     x0, x1, [x_3]
        stp     x2, x3, [x_3+16]
        stp     x4, x5, [x_3+32]
        stp     x6, x7, [y_3]
        stp     x8, x9, [y_3+16]
        stp     x10, x11, [y_3+32]
        stp     x12, x13, [z_3]
        stp     x14, x15, [z_3+16]
        stp     x16, x17, [z_3+32]

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
