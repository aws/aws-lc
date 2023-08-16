// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// Square, z := x^2
// Input x[16]; output z[32]; temporary buffer t[>=24]
//
//    extern void bignum_ksqr_16_32
//     (uint64_t z[static 32], uint64_t x[static 16], uint64_t t[static 24]);
//
// This is a Karatsuba-style function squaring half-sized results
// and using temporary buffer t for intermediate results.
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = t
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_ksqr_16_32)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_ksqr_16_32)
        .text
        .balign 4

// Subroutine-safe copies of the output, inputs and temporary buffer pointers

#define z x23
#define x x24
#define t x25

// More variables for sign masks, with s also necessarily subroutine-safe

#define s x19


S2N_BN_SYMBOL(bignum_ksqr_16_32):

// Save registers, including return address

        stp     x19, x20, [sp, #-16]!
        stp     x21, x22, [sp, #-16]!
        stp     x23, x24, [sp, #-16]!
        stp     x25, x30, [sp, #-16]!

// Move parameters into subroutine-safe places

        mov     z, x0
        mov     x, x1
        mov     t, x2

// Compute L = x_lo * y_lo in bottom half of buffer (size 8 x 8 -> 16)

        bl      bignum_ksqr_16_32_local_sqr_8_16

// Compute absolute difference [t..] = |x_lo - x_hi|

        ldp     x10, x11, [x]
        ldp     x8, x9, [x, #64]
        subs    x10, x10, x8
        sbcs    x11, x11, x9
        ldp     x12, x13, [x, #16]
        ldp     x8, x9, [x, #80]
        sbcs    x12, x12, x8
        sbcs    x13, x13, x9
        ldp     x14, x15, [x, #32]
        ldp     x8, x9, [x, #96]
        sbcs    x14, x14, x8
        sbcs    x15, x15, x9
        ldp     x16, x17, [x, #48]
        ldp     x8, x9, [x, #112]
        sbcs    x16, x16, x8
        sbcs    x17, x17, x9
        csetm   s, cc
        adds    xzr, s, s
        eor     x10, x10, s
        adcs    x10, x10, xzr
        eor     x11, x11, s
        adcs    x11, x11, xzr
        stp     x10, x11, [t]
        eor     x12, x12, s
        adcs    x12, x12, xzr
        eor     x13, x13, s
        adcs    x13, x13, xzr
        stp     x12, x13, [t, #16]
        eor     x14, x14, s
        adcs    x14, x14, xzr
        eor     x15, x15, s
        adcs    x15, x15, xzr
        stp     x14, x15, [t, #32]
        eor     x16, x16, s
        adcs    x16, x16, xzr
        eor     x17, x17, s
        adcs    x17, x17, xzr
        stp     x16, x17, [t, #48]

// Compute H = x_hi * y_hi in top half of buffer (size 8 x 8 -> 16)

        add     x0, z, #128
        add     x1, x, #64
        bl      bignum_ksqr_16_32_local_sqr_8_16

// Compute H' = H + L_top in place of H (it cannot overflow)
// First add 8-sized block then propagate carry through next 8

        ldp     x10, x11, [z, #128]
        ldp     x12, x13, [z, #64]
        adds    x10, x10, x12
        adcs    x11, x11, x13
        stp     x10, x11, [z, #128]

        ldp     x10, x11, [z, #128+16]
        ldp     x12, x13, [z, #64+16]
        adcs    x10, x10, x12
        adcs    x11, x11, x13
        stp     x10, x11, [z, #128+16]

        ldp     x10, x11, [z, #128+32]
        ldp     x12, x13, [z, #64+32]
        adcs    x10, x10, x12
        adcs    x11, x11, x13
        stp     x10, x11, [z, #128+32]

        ldp     x10, x11, [z, #128+48]
        ldp     x12, x13, [z, #64+48]
        adcs    x10, x10, x12
        adcs    x11, x11, x13
        stp     x10, x11, [z, #128+48]

        ldp     x10, x11, [z, #128+64]
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        stp     x10, x11, [z, #128+64]

        ldp     x10, x11, [z, #128+80]
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        stp     x10, x11, [z, #128+80]

        ldp     x10, x11, [z, #128+96]
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        stp     x10, x11, [z, #128+96]

        ldp     x10, x11, [z, #128+112]
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        stp     x10, x11, [z, #128+112]

// Compute M = |x_lo - x_hi| * |y_hi - y_lo| in [t+8...], size 16

        add     x0, t, #64
        mov     x1, t
        bl      bignum_ksqr_16_32_local_sqr_8_16

// Add the interlocking H' and L_bot terms, storing in registers x15..x0
// Intercept the carry at the 8 + 16 = 24 position and store it in x.
// (Note that we no longer need the input x was pointing at.)

        ldp     x0, x1, [z]
        ldp     x16, x17, [z, #128]
        adds    x0, x0, x16
        adcs    x1, x1, x17
        ldp     x2, x3, [z, #16]
        ldp     x16, x17, [z, #144]
        adcs    x2, x2, x16
        adcs    x3, x3, x17
        ldp     x4, x5, [z, #32]
        ldp     x16, x17, [z, #160]
        adcs    x4, x4, x16
        adcs    x5, x5, x17
        ldp     x6, x7, [z, #48]
        ldp     x16, x17, [z, #176]
        adcs    x6, x6, x16
        adcs    x7, x7, x17
        ldp     x8, x9, [z, #128]
        ldp     x16, x17, [z, #192]
        adcs    x8, x8, x16
        adcs    x9, x9, x17
        ldp     x10, x11, [z, #144]
        ldp     x16, x17, [z, #208]
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        ldp     x12, x13, [z, #160]
        ldp     x16, x17, [z, #224]
        adcs    x12, x12, x16
        adcs    x13, x13, x17
        ldp     x14, x15, [z, #176]
        ldp     x16, x17, [z, #240]
        adcs    x14, x14, x16
        adcs    x15, x15, x17
        cset    x, cs

// Subtract the mid-term cross product M

        ldp     x16, x17, [t, #64]
        subs    x0, x0, x16
        sbcs    x1, x1, x17
        stp     x0, x1, [z, #64]
        ldp     x16, x17, [t, #80]
        sbcs    x2, x2, x16
        sbcs    x3, x3, x17
        stp     x2, x3, [z, #80]
        ldp     x16, x17, [t, #96]
        sbcs    x4, x4, x16
        sbcs    x5, x5, x17
        stp     x4, x5, [z, #96]
        ldp     x16, x17, [t, #112]
        sbcs    x6, x6, x16
        sbcs    x7, x7, x17
        stp     x6, x7, [z, #112]
        ldp     x16, x17, [t, #128]
        sbcs    x8, x8, x16
        sbcs    x9, x9, x17
        stp     x8, x9, [z, #128]
        ldp     x16, x17, [t, #144]
        sbcs    x10, x10, x16
        sbcs    x11, x11, x17
        stp     x10, x11, [z, #144]
        ldp     x16, x17, [t, #160]
        sbcs    x12, x12, x16
        sbcs    x13, x13, x17
        stp     x12, x13, [z, #160]
        ldp     x16, x17, [t, #176]
        sbcs    x14, x14, x16
        sbcs    x15, x15, x17
        stp     x14, x15, [z, #176]

// Get the next digits effectively resulting so far starting at 24

        sbcs    x, x, xzr
        csetm   t, cc

// Now the final 8 digits of padding; the first one is special in using x
// and also in getting the carry chain started

        ldp     x10, x11, [z, #192]
        adds    x10, x10, x
        adcs    x11, x11, t
        stp     x10, x11, [z, #192]
        ldp     x10, x11, [z, #208]
        adcs    x10, x10, t
        adcs    x11, x11, t
        stp     x10, x11, [z, #208]
        ldp     x10, x11, [z, #224]
        adcs    x10, x10, t
        adcs    x11, x11, t
        stp     x10, x11, [z, #224]
        ldp     x10, x11, [z, #240]
        adcs    x10, x10, t
        adcs    x11, x11, t
        stp     x10, x11, [z, #240]

// Restore registers and return

        ldp     x25, x30, [sp], #16
        ldp     x23, x24, [sp], #16
        ldp     x21, x22, [sp], #16
        ldp     x19, x20, [sp], #16

        ret

// -----------------------------------------------------------------------------
// Local 8x8->16 squaring routine, shared to reduce code size. Effectively
// the same as bignum_sqr_8_16 without the scratch register preservation.
// -----------------------------------------------------------------------------

bignum_ksqr_16_32_local_sqr_8_16:
        ldp     x2, x3, [x1]
        ldp     x4, x5, [x1, #16]
        ldp     x6, x7, [x1, #32]
        ldp     x8, x9, [x1, #48]
        mul     x17, x2, x4
        mul     x14, x3, x5
        umulh   x20, x2, x4
        subs    x21, x2, x3
        cneg    x21, x21, cc
        csetm   x11, cc
        subs    x12, x5, x4
        cneg    x12, x12, cc
        mul     x13, x21, x12
        umulh   x12, x21, x12
        cinv    x11, x11, cc
        eor     x13, x13, x11
        eor     x12, x12, x11
        adds    x19, x17, x20
        adc     x20, x20, xzr
        umulh   x21, x3, x5
        adds    x19, x19, x14
        adcs    x20, x20, x21
        adc     x21, x21, xzr
        adds    x20, x20, x14
        adc     x21, x21, xzr
        cmn     x11, #0x1
        adcs    x19, x19, x13
        adcs    x20, x20, x12
        adc     x21, x21, x11
        adds    x17, x17, x17
        adcs    x19, x19, x19
        adcs    x20, x20, x20
        adcs    x21, x21, x21
        adc     x10, xzr, xzr
        mul     x12, x2, x2
        mul     x13, x3, x3
        mul     x15, x2, x3
        umulh   x11, x2, x2
        umulh   x14, x3, x3
        umulh   x16, x2, x3
        adds    x11, x11, x15
        adcs    x13, x13, x16
        adc     x14, x14, xzr
        adds    x11, x11, x15
        adcs    x13, x13, x16
        adc     x14, x14, xzr
        stp     x12, x11, [x0]
        adds    x17, x17, x13
        adcs    x19, x19, x14
        adcs    x20, x20, xzr
        adcs    x21, x21, xzr
        adc     x10, x10, xzr
        stp     x17, x19, [x0, #16]
        mul     x12, x4, x4
        mul     x13, x5, x5
        mul     x15, x4, x5
        umulh   x11, x4, x4
        umulh   x14, x5, x5
        umulh   x16, x4, x5
        adds    x11, x11, x15
        adcs    x13, x13, x16
        adc     x14, x14, xzr
        adds    x11, x11, x15
        adcs    x13, x13, x16
        adc     x14, x14, xzr
        adds    x12, x12, x20
        adcs    x11, x11, x21
        stp     x12, x11, [x0, #32]
        adcs    x13, x13, x10
        adc     x14, x14, xzr
        stp     x13, x14, [x0, #48]
        mul     x17, x6, x8
        mul     x14, x7, x9
        umulh   x20, x6, x8
        subs    x21, x6, x7
        cneg    x21, x21, cc
        csetm   x11, cc
        subs    x12, x9, x8
        cneg    x12, x12, cc
        mul     x13, x21, x12
        umulh   x12, x21, x12
        cinv    x11, x11, cc
        eor     x13, x13, x11
        eor     x12, x12, x11
        adds    x19, x17, x20
        adc     x20, x20, xzr
        umulh   x21, x7, x9
        adds    x19, x19, x14
        adcs    x20, x20, x21
        adc     x21, x21, xzr
        adds    x20, x20, x14
        adc     x21, x21, xzr
        cmn     x11, #0x1
        adcs    x19, x19, x13
        adcs    x20, x20, x12
        adc     x21, x21, x11
        adds    x17, x17, x17
        adcs    x19, x19, x19
        adcs    x20, x20, x20
        adcs    x21, x21, x21
        adc     x10, xzr, xzr
        mul     x12, x6, x6
        mul     x13, x7, x7
        mul     x15, x6, x7
        umulh   x11, x6, x6
        umulh   x14, x7, x7
        umulh   x16, x6, x7
        adds    x11, x11, x15
        adcs    x13, x13, x16
        adc     x14, x14, xzr
        adds    x11, x11, x15
        adcs    x13, x13, x16
        adc     x14, x14, xzr
        stp     x12, x11, [x0, #64]
        adds    x17, x17, x13
        adcs    x19, x19, x14
        adcs    x20, x20, xzr
        adcs    x21, x21, xzr
        adc     x10, x10, xzr
        stp     x17, x19, [x0, #80]
        mul     x12, x8, x8
        mul     x13, x9, x9
        mul     x15, x8, x9
        umulh   x11, x8, x8
        umulh   x14, x9, x9
        umulh   x16, x8, x9
        adds    x11, x11, x15
        adcs    x13, x13, x16
        adc     x14, x14, xzr
        adds    x11, x11, x15
        adcs    x13, x13, x16
        adc     x14, x14, xzr
        adds    x12, x12, x20
        adcs    x11, x11, x21
        stp     x12, x11, [x0, #96]
        adcs    x13, x13, x10
        adc     x14, x14, xzr
        stp     x13, x14, [x0, #112]
        mul     x10, x2, x6
        mul     x14, x3, x7
        mul     x15, x4, x8
        mul     x16, x5, x9
        umulh   x17, x2, x6
        adds    x14, x14, x17
        umulh   x17, x3, x7
        adcs    x15, x15, x17
        umulh   x17, x4, x8
        adcs    x16, x16, x17
        umulh   x17, x5, x9
        adc     x17, x17, xzr
        adds    x11, x14, x10
        adcs    x14, x15, x14
        adcs    x15, x16, x15
        adcs    x16, x17, x16
        adc     x17, xzr, x17
        adds    x12, x14, x10
        adcs    x13, x15, x11
        adcs    x14, x16, x14
        adcs    x15, x17, x15
        adcs    x16, xzr, x16
        adc     x17, xzr, x17
        subs    x22, x4, x5
        cneg    x22, x22, cc
        csetm   x19, cc
        subs    x20, x9, x8
        cneg    x20, x20, cc
        mul     x21, x22, x20
        umulh   x20, x22, x20
        cinv    x19, x19, cc
        cmn     x19, #0x1
        eor     x21, x21, x19
        adcs    x15, x15, x21
        eor     x20, x20, x19
        adcs    x16, x16, x20
        adc     x17, x17, x19
        subs    x22, x2, x3
        cneg    x22, x22, cc
        csetm   x19, cc
        subs    x20, x7, x6
        cneg    x20, x20, cc
        mul     x21, x22, x20
        umulh   x20, x22, x20
        cinv    x19, x19, cc
        cmn     x19, #0x1
        eor     x21, x21, x19
        adcs    x11, x11, x21
        eor     x20, x20, x19
        adcs    x12, x12, x20
        adcs    x13, x13, x19
        adcs    x14, x14, x19
        adcs    x15, x15, x19
        adcs    x16, x16, x19
        adc     x17, x17, x19
        subs    x22, x3, x5
        cneg    x22, x22, cc
        csetm   x19, cc
        subs    x20, x9, x7
        cneg    x20, x20, cc
        mul     x21, x22, x20
        umulh   x20, x22, x20
        cinv    x19, x19, cc
        cmn     x19, #0x1
        eor     x21, x21, x19
        adcs    x14, x14, x21
        eor     x20, x20, x19
        adcs    x15, x15, x20
        adcs    x16, x16, x19
        adc     x17, x17, x19
        subs    x22, x2, x4
        cneg    x22, x22, cc
        csetm   x19, cc
        subs    x20, x8, x6
        cneg    x20, x20, cc
        mul     x21, x22, x20
        umulh   x20, x22, x20
        cinv    x19, x19, cc
        cmn     x19, #0x1
        eor     x21, x21, x19
        adcs    x12, x12, x21
        eor     x20, x20, x19
        adcs    x13, x13, x20
        adcs    x14, x14, x19
        adcs    x15, x15, x19
        adcs    x16, x16, x19
        adc     x17, x17, x19
        subs    x22, x2, x5
        cneg    x22, x22, cc
        csetm   x19, cc
        subs    x20, x9, x6
        cneg    x20, x20, cc
        mul     x21, x22, x20
        umulh   x20, x22, x20
        cinv    x19, x19, cc
        cmn     x19, #0x1
        eor     x21, x21, x19
        adcs    x13, x13, x21
        eor     x20, x20, x19
        adcs    x14, x14, x20
        adcs    x15, x15, x19
        adcs    x16, x16, x19
        adc     x17, x17, x19
        subs    x22, x3, x4
        cneg    x22, x22, cc
        csetm   x19, cc
        subs    x20, x8, x7
        cneg    x20, x20, cc
        mul     x21, x22, x20
        umulh   x20, x22, x20
        cinv    x19, x19, cc
        cmn     x19, #0x1
        eor     x21, x21, x19
        adcs    x13, x13, x21
        eor     x20, x20, x19
        adcs    x14, x14, x20
        adcs    x15, x15, x19
        adcs    x16, x16, x19
        adc     x17, x17, x19
        adds    x10, x10, x10
        adcs    x11, x11, x11
        adcs    x12, x12, x12
        adcs    x13, x13, x13
        adcs    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adcs    x17, x17, x17
        adc     x19, xzr, xzr
        ldp     x2, x3, [x0, #32]
        adds    x10, x10, x2
        adcs    x11, x11, x3
        stp     x10, x11, [x0, #32]
        ldp     x2, x3, [x0, #48]
        adcs    x12, x12, x2
        adcs    x13, x13, x3
        stp     x12, x13, [x0, #48]
        ldp     x2, x3, [x0, #64]
        adcs    x14, x14, x2
        adcs    x15, x15, x3
        stp     x14, x15, [x0, #64]
        ldp     x2, x3, [x0, #80]
        adcs    x16, x16, x2
        adcs    x17, x17, x3
        stp     x16, x17, [x0, #80]
        ldp     x2, x3, [x0, #96]
        adcs    x2, x2, x19
        adcs    x3, x3, xzr
        stp     x2, x3, [x0, #96]
        ldp     x2, x3, [x0, #112]
        adcs    x2, x2, xzr
        adc     x3, x3, xzr
        stp     x2, x3, [x0, #112]
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
