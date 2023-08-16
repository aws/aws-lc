// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// Square, z := x^2
// Input x[32]; output z[64]; temporary buffer t[>=72]
//
//    extern void bignum_ksqr_32_64
//     (uint64_t z[static 64], uint64_t x[static 32], uint64_t t[static 72]);
//
// This is a Karatsuba-style function squaring half-sized results
// and using temporary buffer t for intermediate results.
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = t
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_ksqr_32_64)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_ksqr_32_64)
        .text
        .balign 4

#define K 16
#define L 8 // (K/2)

#define z x19
#define x x20
#define t x21

#define c x16


S2N_BN_SYMBOL(bignum_ksqr_32_64):

// Save extra registers and return address, store parameters safely

        stp     x19, x20, [sp, #-16]!
        stp     x21, x30, [sp, #-16]!

        mov     z, x0
        mov     x, x1
        mov     t, x2

// Compute L = x_lo * y_lo in bottom half of buffer (size 16 x 16 -> 32)

        bl      bignum_ksqr_32_64_local_ksqr_16_32

// Compute H = x_hi * y_hi in top half of buffer (size 16 x 16 -> 32)

        add     x0, z, #16*K
        add     x1, x, #8*K
        mov     x2, t
        bl      bignum_ksqr_32_64_local_ksqr_16_32

// Compute H' = H + L_top in place of H (it cannot overflow)

        ldp     x0, x1, [z, #16*16]
        ldp     x2, x3, [z, #16*8]
        adds    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*16]

        ldp     x0, x1, [z, #16*17]
        ldp     x2, x3, [z, #16*9]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*17]

        ldp     x0, x1, [z, #16*18]
        ldp     x2, x3, [z, #16*10]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*18]

        ldp     x0, x1, [z, #16*19]
        ldp     x2, x3, [z, #16*11]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*19]

        ldp     x0, x1, [z, #16*20]
        ldp     x2, x3, [z, #16*12]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*20]

        ldp     x0, x1, [z, #16*21]
        ldp     x2, x3, [z, #16*13]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*21]

        ldp     x0, x1, [z, #16*22]
        ldp     x2, x3, [z, #16*14]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*22]

        ldp     x0, x1, [z, #16*23]
        ldp     x2, x3, [z, #16*15]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*23]

        ldp     x0, x1, [z, #16*24]
        adcs    x0, x0, xzr
        adcs    x1, x1, xzr
        stp     x0, x1, [z, #16*24]

        ldp     x0, x1, [z, #16*25]
        adcs    x0, x0, xzr
        adcs    x1, x1, xzr
        stp     x0, x1, [z, #16*25]

        ldp     x0, x1, [z, #16*26]
        adcs    x0, x0, xzr
        adcs    x1, x1, xzr
        stp     x0, x1, [z, #16*26]

        ldp     x0, x1, [z, #16*27]
        adcs    x0, x0, xzr
        adcs    x1, x1, xzr
        stp     x0, x1, [z, #16*27]

        ldp     x0, x1, [z, #16*28]
        adcs    x0, x0, xzr
        adcs    x1, x1, xzr
        stp     x0, x1, [z, #16*28]

        ldp     x0, x1, [z, #16*29]
        adcs    x0, x0, xzr
        adcs    x1, x1, xzr
        stp     x0, x1, [z, #16*29]

        ldp     x0, x1, [z, #16*30]
        adcs    x0, x0, xzr
        adcs    x1, x1, xzr
        stp     x0, x1, [z, #16*30]

        ldp     x0, x1, [z, #16*31]
        adcs    x0, x0, xzr
        adc     x1, x1, xzr
        stp     x0, x1, [z, #16*31]

// Compute absolute difference [t..] = |x_lo - x_hi|

        ldp     x0, x1, [x, #128]
        ldp     x16, x17, [x]
        subs    x0, x0, x16
        sbcs    x1, x1, x17

        ldp     x2, x3, [x, #144]
        ldp     x16, x17, [x, #16]
        sbcs    x2, x2, x16
        sbcs    x3, x3, x17

        ldp     x4, x5, [x, #160]
        ldp     x16, x17, [x, #32]
        sbcs    x4, x4, x16
        sbcs    x5, x5, x17

        ldp     x6, x7, [x, #176]
        ldp     x16, x17, [x, #48]
        sbcs    x6, x6, x16
        sbcs    x7, x7, x17

        ldp     x8, x9, [x, #192]
        ldp     x16, x17, [x, #64]
        sbcs    x8, x8, x16
        sbcs    x9, x9, x17

        ldp     x10, x11, [x, #208]
        ldp     x16, x17, [x, #80]
        sbcs    x10, x10, x16
        sbcs    x11, x11, x17

        ldp     x12, x13, [x, #224]
        ldp     x16, x17, [x, #96]
        sbcs    x12, x12, x16
        sbcs    x13, x13, x17

        ldp     x14, x15, [x, #240]
        ldp     x16, x17, [x, #112]
        sbcs    x14, x14, x16
        sbcs    x15, x15, x17

        sbc     c, xzr, xzr

        adds    xzr, c, c

        eor     x0, x0, c
        adcs    x0, x0, xzr
        eor     x1, x1, c
        adcs    x1, x1, xzr
        stp     x0, x1, [t]

        eor     x2, x2, c
        adcs    x2, x2, xzr
        eor     x3, x3, c
        adcs    x3, x3, xzr
        stp     x2, x3, [t, #16]

        eor     x4, x4, c
        adcs    x4, x4, xzr
        eor     x5, x5, c
        adcs    x5, x5, xzr
        stp     x4, x5, [t, #32]

        eor     x6, x6, c
        adcs    x6, x6, xzr
        eor     x7, x7, c
        adcs    x7, x7, xzr
        stp     x6, x7, [t, #48]

        eor     x8, x8, c
        adcs    x8, x8, xzr
        eor     x9, x9, c
        adcs    x9, x9, xzr
        stp     x8, x9, [t, #64]

        eor     x10, x10, c
        adcs    x10, x10, xzr
        eor     x11, x11, c
        adcs    x11, x11, xzr
        stp     x10, x11, [t, #80]

        eor     x12, x12, c
        adcs    x12, x12, xzr
        eor     x13, x13, c
        adcs    x13, x13, xzr
        stp     x12, x13, [t, #96]

        eor     x14, x14, c
        adcs    x14, x14, xzr
        eor     x15, x15, c
        adc     x15, x15, xzr
        stp     x14, x15, [t, #112]

// Compute M = |x_lo - x_hi|^2, size 32

        add     x0, t, #8*K
        mov     x1, t
        add     x2, t, #24*K
        bl      bignum_ksqr_32_64_local_ksqr_16_32

// Add the interlocking H' and L_bot terms
// Intercept the carry at the 3k position and store it in x.
// (Note that we no longer need the input x was pointing at.)

        ldp     x0, x1, [z, #16*16]
        ldp     x2, x3, [z]
        adds    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*8]

        ldp     x0, x1, [z, #16*17]
        ldp     x2, x3, [z, #16*1]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*9]

        ldp     x0, x1, [z, #16*18]
        ldp     x2, x3, [z, #16*2]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*10]

        ldp     x0, x1, [z, #16*19]
        ldp     x2, x3, [z, #16*3]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*11]

        ldp     x0, x1, [z, #16*20]
        ldp     x2, x3, [z, #16*4]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*12]

        ldp     x0, x1, [z, #16*21]
        ldp     x2, x3, [z, #16*5]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*13]

        ldp     x0, x1, [z, #16*22]
        ldp     x2, x3, [z, #16*6]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*14]

        ldp     x0, x1, [z, #16*23]
        ldp     x2, x3, [z, #16*7]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*15]

        ldp     x0, x1, [z, #16*16]
        ldp     x2, x3, [z, #16*24]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*16]

        ldp     x0, x1, [z, #16*17]
        ldp     x2, x3, [z, #16*25]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*17]

        ldp     x0, x1, [z, #16*18]
        ldp     x2, x3, [z, #16*26]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*18]

        ldp     x0, x1, [z, #16*19]
        ldp     x2, x3, [z, #16*27]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*19]

        ldp     x0, x1, [z, #16*20]
        ldp     x2, x3, [z, #16*28]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*20]

        ldp     x0, x1, [z, #16*21]
        ldp     x2, x3, [z, #16*29]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*21]

        ldp     x0, x1, [z, #16*22]
        ldp     x2, x3, [z, #16*30]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*22]

        ldp     x0, x1, [z, #16*23]
        ldp     x2, x3, [z, #16*31]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*23]

        cset      x, cs

// Subtract the mid-term cross product M

        ldp     x0, x1, [z, #16*L]
        ldp     x2, x3, [t, #16*L]
        subs    x0, x0, x2
        sbcs    x1, x1, x3
        stp     x0, x1, [z, #16*L]

        ldp     x0, x1, [z, #16*9]
        ldp     x2, x3, [t, #16*9]
        sbcs    x0, x0, x2
        sbcs    x1, x1, x3
        stp     x0, x1, [z, #16*9]

        ldp     x0, x1, [z, #16*10]
        ldp     x2, x3, [t, #16*10]
        sbcs    x0, x0, x2
        sbcs    x1, x1, x3
        stp     x0, x1, [z, #16*10]

        ldp     x0, x1, [z, #16*11]
        ldp     x2, x3, [t, #16*11]
        sbcs    x0, x0, x2
        sbcs    x1, x1, x3
        stp     x0, x1, [z, #16*11]

        ldp     x0, x1, [z, #16*12]
        ldp     x2, x3, [t, #16*12]
        sbcs    x0, x0, x2
        sbcs    x1, x1, x3
        stp     x0, x1, [z, #16*12]

        ldp     x0, x1, [z, #16*13]
        ldp     x2, x3, [t, #16*13]
        sbcs    x0, x0, x2
        sbcs    x1, x1, x3
        stp     x0, x1, [z, #16*13]

        ldp     x0, x1, [z, #16*14]
        ldp     x2, x3, [t, #16*14]
        sbcs    x0, x0, x2
        sbcs    x1, x1, x3
        stp     x0, x1, [z, #16*14]

        ldp     x0, x1, [z, #16*15]
        ldp     x2, x3, [t, #16*15]
        sbcs    x0, x0, x2
        sbcs    x1, x1, x3
        stp     x0, x1, [z, #16*15]

        ldp     x0, x1, [z, #16*16]
        ldp     x2, x3, [t, #16*16]
        sbcs    x0, x0, x2
        sbcs    x1, x1, x3
        stp     x0, x1, [z, #16*16]

        ldp     x0, x1, [z, #16*17]
        ldp     x2, x3, [t, #16*17]
        sbcs    x0, x0, x2
        sbcs    x1, x1, x3
        stp     x0, x1, [z, #16*17]

        ldp     x0, x1, [z, #16*18]
        ldp     x2, x3, [t, #16*18]
        sbcs    x0, x0, x2
        sbcs    x1, x1, x3
        stp     x0, x1, [z, #16*18]

        ldp     x0, x1, [z, #16*19]
        ldp     x2, x3, [t, #16*19]
        sbcs    x0, x0, x2
        sbcs    x1, x1, x3
        stp     x0, x1, [z, #16*19]

        ldp     x0, x1, [z, #16*20]
        ldp     x2, x3, [t, #16*20]
        sbcs    x0, x0, x2
        sbcs    x1, x1, x3
        stp     x0, x1, [z, #16*20]

        ldp     x0, x1, [z, #16*21]
        ldp     x2, x3, [t, #16*21]
        sbcs    x0, x0, x2
        sbcs    x1, x1, x3
        stp     x0, x1, [z, #16*21]

        ldp     x0, x1, [z, #16*22]
        ldp     x2, x3, [t, #16*22]
        sbcs    x0, x0, x2
        sbcs    x1, x1, x3
        stp     x0, x1, [z, #16*22]

        ldp     x0, x1, [z, #16*23]
        ldp     x2, x3, [t, #16*23]
        sbcs    x0, x0, x2
        sbcs    x1, x1, x3
        stp     x0, x1, [z, #16*23]

// Get the next digits effectively resulting so far starting at 3k
// [...,c,c,c,c,x]

        sbcs    x, x, xzr
        csetm   c, cc

// Now propagate through the top quarter of the result

        ldp     x0, x1, [z, #16*24]
        adds    x0, x0, x
        adcs    x1, x1, c
        stp     x0, x1, [z, #16*24]

        ldp     x0, x1, [z, #16*25]
        adcs    x0, x0, c
        adcs    x1, x1, c
        stp     x0, x1, [z, #16*25]

        ldp     x0, x1, [z, #16*26]
        adcs    x0, x0, c
        adcs    x1, x1, c
        stp     x0, x1, [z, #16*26]

        ldp     x0, x1, [z, #16*27]
        adcs    x0, x0, c
        adcs    x1, x1, c
        stp     x0, x1, [z, #16*27]

        ldp     x0, x1, [z, #16*28]
        adcs    x0, x0, c
        adcs    x1, x1, c
        stp     x0, x1, [z, #16*28]

        ldp     x0, x1, [z, #16*29]
        adcs    x0, x0, c
        adcs    x1, x1, c
        stp     x0, x1, [z, #16*29]

        ldp     x0, x1, [z, #16*30]
        adcs    x0, x0, c
        adcs    x1, x1, c
        stp     x0, x1, [z, #16*30]

        ldp     x0, x1, [z, #16*31]
        adcs    x0, x0, c
        adc     x1, x1, c
        stp     x0, x1, [z, #16*31]

// Restore

        ldp     x21, x30, [sp], #16
        ldp     x19, x20, [sp], #16

        ret

// Local copy of bignum_ksqr_16_32, identical to main one.
// This includes in turn a copy of bignum_sqr_8_16.

bignum_ksqr_32_64_local_ksqr_16_32:
        stp     x19, x20, [sp, #-16]!
        stp     x21, x22, [sp, #-16]!
        stp     x23, x24, [sp, #-16]!
        stp     x25, x30, [sp, #-16]!
        mov     x23, x0
        mov     x24, x1
        mov     x25, x2
        bl      bignum_ksqr_32_64_local_sqr_8_16
        ldp     x10, x11, [x24]
        ldp     x8, x9, [x24, #64]
        subs    x10, x10, x8
        sbcs    x11, x11, x9
        ldp     x12, x13, [x24, #16]
        ldp     x8, x9, [x24, #80]
        sbcs    x12, x12, x8
        sbcs    x13, x13, x9
        ldp     x14, x15, [x24, #32]
        ldp     x8, x9, [x24, #96]
        sbcs    x14, x14, x8
        sbcs    x15, x15, x9
        ldp     x16, x17, [x24, #48]
        ldp     x8, x9, [x24, #112]
        sbcs    x16, x16, x8
        sbcs    x17, x17, x9
        csetm   x19, cc
        cmn     x19, x19
        eor     x10, x10, x19
        adcs    x10, x10, xzr
        eor     x11, x11, x19
        adcs    x11, x11, xzr
        stp     x10, x11, [x25]
        eor     x12, x12, x19
        adcs    x12, x12, xzr
        eor     x13, x13, x19
        adcs    x13, x13, xzr
        stp     x12, x13, [x25, #16]
        eor     x14, x14, x19
        adcs    x14, x14, xzr
        eor     x15, x15, x19
        adcs    x15, x15, xzr
        stp     x14, x15, [x25, #32]
        eor     x16, x16, x19
        adcs    x16, x16, xzr
        eor     x17, x17, x19
        adcs    x17, x17, xzr
        stp     x16, x17, [x25, #48]
        add     x0, x23, #0x80
        add     x1, x24, #0x40
        bl      bignum_ksqr_32_64_local_sqr_8_16
        ldp     x10, x11, [x23, #128]
        ldp     x12, x13, [x23, #64]
        adds    x10, x10, x12
        adcs    x11, x11, x13
        stp     x10, x11, [x23, #128]
        ldp     x10, x11, [x23, #144]
        ldp     x12, x13, [x23, #80]
        adcs    x10, x10, x12
        adcs    x11, x11, x13
        stp     x10, x11, [x23, #144]
        ldp     x10, x11, [x23, #160]
        ldp     x12, x13, [x23, #96]
        adcs    x10, x10, x12
        adcs    x11, x11, x13
        stp     x10, x11, [x23, #160]
        ldp     x10, x11, [x23, #176]
        ldp     x12, x13, [x23, #112]
        adcs    x10, x10, x12
        adcs    x11, x11, x13
        stp     x10, x11, [x23, #176]
        ldp     x10, x11, [x23, #192]
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        stp     x10, x11, [x23, #192]
        ldp     x10, x11, [x23, #208]
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        stp     x10, x11, [x23, #208]
        ldp     x10, x11, [x23, #224]
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        stp     x10, x11, [x23, #224]
        ldp     x10, x11, [x23, #240]
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        stp     x10, x11, [x23, #240]
        add     x0, x25, #0x40
        mov     x1, x25
        bl      bignum_ksqr_32_64_local_sqr_8_16
        ldp     x0, x1, [x23]
        ldp     x16, x17, [x23, #128]
        adds    x0, x0, x16
        adcs    x1, x1, x17
        ldp     x2, x3, [x23, #16]
        ldp     x16, x17, [x23, #144]
        adcs    x2, x2, x16
        adcs    x3, x3, x17
        ldp     x4, x5, [x23, #32]
        ldp     x16, x17, [x23, #160]
        adcs    x4, x4, x16
        adcs    x5, x5, x17
        ldp     x6, x7, [x23, #48]
        ldp     x16, x17, [x23, #176]
        adcs    x6, x6, x16
        adcs    x7, x7, x17
        ldp     x8, x9, [x23, #128]
        ldp     x16, x17, [x23, #192]
        adcs    x8, x8, x16
        adcs    x9, x9, x17
        ldp     x10, x11, [x23, #144]
        ldp     x16, x17, [x23, #208]
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        ldp     x12, x13, [x23, #160]
        ldp     x16, x17, [x23, #224]
        adcs    x12, x12, x16
        adcs    x13, x13, x17
        ldp     x14, x15, [x23, #176]
        ldp     x16, x17, [x23, #240]
        adcs    x14, x14, x16
        adcs    x15, x15, x17
        cset    x24, cs
        ldp     x16, x17, [x25, #64]
        subs    x0, x0, x16
        sbcs    x1, x1, x17
        stp     x0, x1, [x23, #64]
        ldp     x16, x17, [x25, #80]
        sbcs    x2, x2, x16
        sbcs    x3, x3, x17
        stp     x2, x3, [x23, #80]
        ldp     x16, x17, [x25, #96]
        sbcs    x4, x4, x16
        sbcs    x5, x5, x17
        stp     x4, x5, [x23, #96]
        ldp     x16, x17, [x25, #112]
        sbcs    x6, x6, x16
        sbcs    x7, x7, x17
        stp     x6, x7, [x23, #112]
        ldp     x16, x17, [x25, #128]
        sbcs    x8, x8, x16
        sbcs    x9, x9, x17
        stp     x8, x9, [x23, #128]
        ldp     x16, x17, [x25, #144]
        sbcs    x10, x10, x16
        sbcs    x11, x11, x17
        stp     x10, x11, [x23, #144]
        ldp     x16, x17, [x25, #160]
        sbcs    x12, x12, x16
        sbcs    x13, x13, x17
        stp     x12, x13, [x23, #160]
        ldp     x16, x17, [x25, #176]
        sbcs    x14, x14, x16
        sbcs    x15, x15, x17
        stp     x14, x15, [x23, #176]
        sbcs    x24, x24, xzr
        csetm   x25, cc
        ldp     x10, x11, [x23, #192]
        adds    x10, x10, x24
        adcs    x11, x11, x25
        stp     x10, x11, [x23, #192]
        ldp     x10, x11, [x23, #208]
        adcs    x10, x10, x25
        adcs    x11, x11, x25
        stp     x10, x11, [x23, #208]
        ldp     x10, x11, [x23, #224]
        adcs    x10, x10, x25
        adcs    x11, x11, x25
        stp     x10, x11, [x23, #224]
        ldp     x10, x11, [x23, #240]
        adcs    x10, x10, x25
        adcs    x11, x11, x25
        stp     x10, x11, [x23, #240]
        ldp     x25, x30, [sp], #16
        ldp     x23, x24, [sp], #16
        ldp     x21, x22, [sp], #16
        ldp     x19, x20, [sp], #16
        ret

bignum_ksqr_32_64_local_sqr_8_16:
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
