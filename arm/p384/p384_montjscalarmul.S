// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery-Jacobian form scalar multiplication for P-384
// Input scalar[6], point[18]; output res[18]
//
// extern void p384_montjscalarmul
//   (uint64_t res[static 18],
//    uint64_t scalar[static 6],
//    uint64_t point[static 18]);
//
// This function is a variant of its affine point version p384_scalarmul.
// Here, input and output points are assumed to be in Jacobian form with
// their coordinates in the Montgomery domain. Thus, if priming indicates
// Montgomery form, x' = (2^384 * x) mod p_384 etc., each point argument
// is a triple (x',y',z') representing the affine point (x/z^2,y/z^3) when
// z' is nonzero or the point at infinity (group identity) if z' = 0.
//
// Given scalar = n and point = P, assumed to be on the NIST elliptic
// curve P-384, returns a representation of n * P. If the result is the
// point at infinity (either because the input point was or because the
// scalar was a multiple of p_384) then the output is guaranteed to
// represent the point at infinity, i.e. to have its z coordinate zero.
//
// Standard ARM ABI: X0 = res, X1 = scalar, X2 = point
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p384_montjscalarmul)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p384_montjscalarmul)

        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 48
#define JACSIZE (3*NUMSIZE)

// Safe copies of input res and additional values in variables.

#define bf x22
#define sgn x23
#define j x24
#define res x25

// Intermediate variables on the stack.
// The table is 16 entries, each of size JACSIZE = 3 * NUMSIZE

#define scalarb sp, #(0*NUMSIZE)
#define acc sp, #(1*NUMSIZE)
#define tabent sp, #(4*NUMSIZE)

#define tab sp, #(7*NUMSIZE)

#define NSPACE #(55*NUMSIZE)

// Avoid using .rep for the sake of the BoringSSL/AWS-LC delocator,
// which doesn't accept repetitions, assembler macros etc.

#define selectblock(I)                            \
        cmp     bf, #(I);                         \
        ldp     x20, x21, [x19];                  \
        csel    x0, x20, x0, eq;                  \
        csel    x1, x21, x1, eq;                  \
        ldp     x20, x21, [x19, #16];             \
        csel    x2, x20, x2, eq;                  \
        csel    x3, x21, x3, eq;                  \
        ldp     x20, x21, [x19, #32];             \
        csel    x4, x20, x4, eq;                  \
        csel    x5, x21, x5, eq;                  \
        ldp     x20, x21, [x19, #48];             \
        csel    x6, x20, x6, eq;                  \
        csel    x7, x21, x7, eq;                  \
        ldp     x20, x21, [x19, #64];             \
        csel    x8, x20, x8, eq;                  \
        csel    x9, x21, x9, eq;                  \
        ldp     x20, x21, [x19, #80];             \
        csel    x10, x20, x10, eq;                \
        csel    x11, x21, x11, eq;                \
        ldp     x20, x21, [x19, #96];             \
        csel    x12, x20, x12, eq;                \
        csel    x13, x21, x13, eq;                \
        ldp     x20, x21, [x19, #112];            \
        csel    x14, x20, x14, eq;                \
        csel    x15, x21, x15, eq;                \
        ldp     x20, x21, [x19, #128];            \
        csel    x16, x20, x16, eq;                \
        csel    x17, x21, x17, eq;                \
        add     x19, x19, #JACSIZE

// Loading large constants

#define movbig(nn,n3,n2,n1,n0)                                      \
        movz    nn, n0;                                             \
        movk    nn, n1, lsl #16;                                    \
        movk    nn, n2, lsl #32;                                    \
        movk    nn, n3, lsl #48

S2N_BN_SYMBOL(p384_montjscalarmul):

        stp     x19, x20, [sp, #-16]!
        stp     x21, x22, [sp, #-16]!
        stp     x23, x24, [sp, #-16]!
        stp     x25, x30, [sp, #-16]!
        sub     sp, sp, NSPACE

// Preserve the "res" input argument; others get processed early.

        mov     res, x0

// Reduce the input scalar mod n_256, i.e. conditionally subtract n_256.
// Store it to "scalarb".

        ldp     x3, x4, [x1]
        movbig(x15, #0xecec, #0x196a, #0xccc5, #0x2973)
        ldp     x5, x6, [x1, #16]
        movbig(x16, #0x581a, #0x0db2, #0x48b0, #0xa77a)
        ldp     x7, x8, [x1, #32]
        movbig(x17, #0xc763, #0x4d81, #0xf437, #0x2ddf)

        subs    x9, x3, x15
        sbcs    x10, x4, x16
        sbcs    x11, x5, x17
        adcs    x12, x6, xzr
        adcs    x13, x7, xzr
        adcs    x14, x8, xzr

        csel    x3, x3, x9, cc
        csel    x4, x4, x10, cc
        csel    x5, x5, x11, cc
        csel    x6, x6, x12, cc
        csel    x7, x7, x13, cc
        csel    x8, x8, x14, cc

        stp     x3, x4, [scalarb]
        stp     x5, x6, [scalarb+16]
        stp     x7, x8, [scalarb+32]

// Set the tab[0] table entry to the input point = 1 * P

        ldp     x10, x11, [x2]
        stp     x10, x11, [tab]
        ldp     x12, x13, [x2, #16]
        stp     x12, x13, [tab+16]
        ldp     x14, x15, [x2, #32]
        stp     x14, x15, [tab+32]

        ldp     x10, x11, [x2, #48]
        stp     x10, x11, [tab+48]
        ldp     x12, x13, [x2, #64]
        stp     x12, x13, [tab+64]
        ldp     x14, x15, [x2, #80]
        stp     x14, x15, [tab+80]

        ldp     x10, x11, [x2, #96]
        stp     x10, x11, [tab+96]
        ldp     x12, x13, [x2, #112]
        stp     x12, x13, [tab+112]
        ldp     x14, x15, [x2, #128]
        stp     x14, x15, [tab+128]

// Compute and record tab[1] = 2 * p, ..., tab[15] = 16 * P

        add     x0, tab+JACSIZE*1
        add     x1, tab
        bl      p384_montjscalarmul_p384_montjdouble

        add     x0, tab+JACSIZE*2
        add     x1, tab+JACSIZE*1
        add     x2, tab
        bl      p384_montjscalarmul_p384_montjadd

        add     x0, tab+JACSIZE*3
        add     x1, tab+JACSIZE*1
        bl      p384_montjscalarmul_p384_montjdouble

        add     x0, tab+JACSIZE*4
        add     x1, tab+JACSIZE*3
        add     x2, tab
        bl      p384_montjscalarmul_p384_montjadd

        add     x0, tab+JACSIZE*5
        add     x1, tab+JACSIZE*2
        bl      p384_montjscalarmul_p384_montjdouble

        add     x0, tab+JACSIZE*6
        add     x1, tab+JACSIZE*5
        add     x2, tab
        bl      p384_montjscalarmul_p384_montjadd

        add     x0, tab+JACSIZE*7
        add     x1, tab+JACSIZE*3
        bl      p384_montjscalarmul_p384_montjdouble

        add     x0, tab+JACSIZE*8
        add     x1, tab+JACSIZE*7
        add     x2, tab
        bl      p384_montjscalarmul_p384_montjadd

        add     x0, tab+JACSIZE*9
        add     x1, tab+JACSIZE*4
        bl      p384_montjscalarmul_p384_montjdouble

        add     x0, tab+JACSIZE*10
        add     x1, tab+JACSIZE*9
        add     x2, tab
        bl      p384_montjscalarmul_p384_montjadd

        add     x0, tab+JACSIZE*11
        add     x1, tab+JACSIZE*5
        bl      p384_montjscalarmul_p384_montjdouble

        add     x0, tab+JACSIZE*12
        add     x1, tab+JACSIZE*11
        add     x2, tab
        bl      p384_montjscalarmul_p384_montjadd

        add     x0, tab+JACSIZE*13
        add     x1, tab+JACSIZE*6
        bl      p384_montjscalarmul_p384_montjdouble

        add     x0, tab+JACSIZE*14
        add     x1, tab+JACSIZE*13
        add     x2, tab
        bl      p384_montjscalarmul_p384_montjadd

        add     x0, tab+JACSIZE*15
        add     x1, tab+JACSIZE*7
        bl      p384_montjscalarmul_p384_montjdouble

// Add the recoding constant sum_i(16 * 32^i) to the scalar to allow signed
// digits. The digits of the constant, in lowest-to-highest order, are as
// follows; they are generated dynamically since none is a simple ARM load.
//
// 0x0842108421084210
// 0x1084210842108421
// 0x2108421084210842
// 0x4210842108421084
// 0x8421084210842108
// 0x0842108421084210

        ldp     x0, x1, [scalarb]
        ldp     x2, x3, [scalarb+16]
        ldp     x4, x5, [scalarb+32]
        movbig(x8, #0x1084, #0x2108, #0x4210, #0x8421)
        adds    x0, x0, x8, lsr #1
        adcs    x1, x1, x8
        lsl     x8, x8, #1
        adcs    x2, x2, x8
        lsl     x8, x8, #1
        adcs    x3, x3, x8
        lsl     x8, x8, #1
        adcs    x4, x4, x8
        lsr     x8, x8, #4
        adcs    x5, x5, x8
        cset    x6, cs

// Record the top bitfield then shift the whole scalar left 4 bits
// to align the top of the next bitfield with the MSB (bits 379..383).

        extr    bf, x6, x5, #60
        extr    x5, x5, x4, #60
        extr    x4, x4, x3, #60
        extr    x3, x3, x2, #60
        extr    x2, x2, x1, #60
        extr    x1, x1, x0, #60
        lsl     x0, x0, #4
        stp     x0, x1, [scalarb]
        stp     x2, x3, [scalarb+16]
        stp     x4, x5, [scalarb+32]

// Initialize the accumulator to the corresponding entry using constant-time
// lookup in the table. This top digit, uniquely, is not recoded so there is
// no sign adjustment to make.

        mov     x0, xzr
        mov     x1, xzr
        mov     x2, xzr
        mov     x3, xzr
        mov     x4, xzr
        mov     x5, xzr
        mov     x6, xzr
        mov     x7, xzr
        mov     x8, xzr
        mov     x9, xzr
        mov     x10, xzr
        mov     x11, xzr
        mov     x12, xzr
        mov     x13, xzr
        mov     x14, xzr
        mov     x15, xzr
        mov     x16, xzr
        mov     x17, xzr

        add     x19, tab

        selectblock(1)
        selectblock(2)
        selectblock(3)
        selectblock(4)
        selectblock(5)
        selectblock(6)
        selectblock(7)
        selectblock(8)
        selectblock(9)
        selectblock(10)
        selectblock(11)
        selectblock(12)
        selectblock(13)
        selectblock(14)
        selectblock(15)
        selectblock(16)

        stp     x0, x1, [acc]
        stp     x2, x3, [acc+16]
        stp     x4, x5, [acc+32]
        stp     x6, x7, [acc+48]
        stp     x8, x9, [acc+64]
        stp     x10, x11, [acc+80]
        stp     x12, x13, [acc+96]
        stp     x14, x15, [acc+112]
        stp     x16, x17, [acc+128]

        mov     j, #380

// Main loop over size-5 bitfields: double 5 times then add signed digit
// At each stage we shift the scalar left by 5 bits so we can simply pick
// the top 5 bits as the bitfield, saving some fiddle over indexing.

p384_montjscalarmul_mainloop:
        sub     j, j, #5

        add     x0, acc
        add     x1, acc
        bl      p384_montjscalarmul_p384_montjdouble

        add     x0, acc
        add     x1, acc
        bl      p384_montjscalarmul_p384_montjdouble

        add     x0, acc
        add     x1, acc
        bl      p384_montjscalarmul_p384_montjdouble

        add     x0, acc
        add     x1, acc
        bl      p384_montjscalarmul_p384_montjdouble

        add     x0, acc
        add     x1, acc
        bl      p384_montjscalarmul_p384_montjdouble

// Choose the bitfield and adjust it to sign and magnitude

        ldp     x0, x1, [scalarb]
        ldp     x2, x3, [scalarb+16]
        ldp     x4, x5, [scalarb+32]
        lsr     bf, x5, #59
        extr    x5, x5, x4, #59
        extr    x4, x4, x3, #59
        extr    x3, x3, x2, #59
        extr    x2, x2, x1, #59
        extr    x1, x1, x0, #59
        lsl     x0, x0, #5
        stp     x0, x1, [scalarb]
        stp     x2, x3, [scalarb+16]
        stp     x4, x5, [scalarb+32]

        subs    bf, bf, #16
        cset    sgn, lo                 // sgn = sign of digit (1 = negative)
        cneg    bf, bf, lo              // bf = absolute value of digit

// Conditionally select the table entry tab[i-1] = i * P in constant time

        mov     x0, xzr
        mov     x1, xzr
        mov     x2, xzr
        mov     x3, xzr
        mov     x4, xzr
        mov     x5, xzr
        mov     x6, xzr
        mov     x7, xzr
        mov     x8, xzr
        mov     x9, xzr
        mov     x10, xzr
        mov     x11, xzr
        mov     x12, xzr
        mov     x13, xzr
        mov     x14, xzr
        mov     x15, xzr
        mov     x16, xzr
        mov     x17, xzr

        add     x19, tab

        selectblock(1)
        selectblock(2)
        selectblock(3)
        selectblock(4)
        selectblock(5)
        selectblock(6)
        selectblock(7)
        selectblock(8)
        selectblock(9)
        selectblock(10)
        selectblock(11)
        selectblock(12)
        selectblock(13)
        selectblock(14)
        selectblock(15)
        selectblock(16)

// Store it to "tabent" with the y coordinate optionally negated.
// This is done carefully to give coordinates < p_384 even in
// the degenerate case y = 0 (when z = 0 for points on the curve).

        stp     x0, x1, [tabent]
        stp     x2, x3, [tabent+16]
        stp     x4, x5, [tabent+32]

        stp     x12, x13, [tabent+96]
        stp     x14, x15, [tabent+112]
        stp     x16, x17, [tabent+128]

        mov     x0, #0x00000000ffffffff
        subs    x0, x0, x6
        orr     x12, x6, x7
        mov     x1, #0xffffffff00000000
        sbcs    x1, x1, x7
        orr     x13, x8, x9
        mov     x2, #0xfffffffffffffffe
        sbcs    x2, x2, x8
        orr     x14, x10, x11
        mov     x5, #0xffffffffffffffff
        sbcs    x3, x5, x9
        orr     x12, x12, x13
        sbcs    x4, x5, x10
        orr     x12, x12, x14
        sbcs    x5, x5, x11

        cmp     sgn, xzr
        ccmp    x12, xzr, #4, ne

        csel    x6, x0, x6, ne
        csel    x7, x1, x7, ne
        csel    x8, x2, x8, ne
        csel    x9, x3, x9, ne
        csel    x10, x4, x10, ne
        csel    x11, x5, x11, ne

        stp     x6, x7, [tabent+48]
        stp     x8, x9, [tabent+64]
        stp     x10, x11, [tabent+80]

// Add to the accumulator

        add     x0, acc
        add     x1, acc
        add     x2, tabent
        bl      p384_montjscalarmul_p384_montjadd

        cbnz    j, p384_montjscalarmul_mainloop

// That's the end of the main loop, and we just need to copy the
// result in "acc" to the output.

        ldp     x0, x1, [acc]
        stp     x0, x1, [res]
        ldp     x0, x1, [acc+16]
        stp     x0, x1, [res, #16]
        ldp     x0, x1, [acc+32]
        stp     x0, x1, [res, #32]
        ldp     x0, x1, [acc+48]
        stp     x0, x1, [res, #48]
        ldp     x0, x1, [acc+64]
        stp     x0, x1, [res, #64]
        ldp     x0, x1, [acc+80]
        stp     x0, x1, [res, #80]
        ldp     x0, x1, [acc+96]
        stp     x0, x1, [res, #96]
        ldp     x0, x1, [acc+112]
        stp     x0, x1, [res, #112]
        ldp     x0, x1, [acc+128]
        stp     x0, x1, [res, #128]

// Restore stack and registers and return

        add     sp, sp, NSPACE
        ldp     x25, x30, [sp], 16
        ldp     x23, x24, [sp], 16
        ldp     x21, x22, [sp], 16
        ldp     x19, x20, [sp], 16
        ret

// Local copies of subroutines, complete clones at the moment

p384_montjscalarmul_p384_montjadd:
        stp     x19, x20, [sp, #-16]!
        stp     x21, x22, [sp, #-16]!
        stp     x23, x24, [sp, #-16]!
        stp     x25, x26, [sp, #-16]!
        sub     sp, sp, #336
        mov     x24, x0
        mov     x25, x1
        mov     x26, x2
        ldp     x2, x3, [x25, #96]
        ldp     x4, x5, [x25, #112]
        ldp     x6, x7, [x25, #128]
        mul     x14, x2, x3
        mul     x15, x2, x4
        mul     x16, x3, x4
        mul     x8, x2, x2
        mul     x10, x3, x3
        mul     x12, x4, x4
        umulh   x17, x2, x3
        adds    x15, x15, x17
        umulh   x17, x2, x4
        adcs    x16, x16, x17
        umulh   x17, x3, x4
        adcs    x17, x17, xzr
        umulh   x9, x2, x2
        umulh   x11, x3, x3
        umulh   x13, x4, x4
        adds    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adcs    x17, x17, x17
        adc     x13, x13, xzr
        adds    x9, x9, x14
        adcs    x10, x10, x15
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x13, xzr
        lsl     x16, x8, #32
        add     x8, x16, x8
        lsr     x16, x8, #32
        subs    x16, x16, x8
        sbc     x15, x8, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x8
        adc     x14, xzr, xzr
        subs    x9, x9, x16
        sbcs    x10, x10, x15
        sbcs    x11, x11, x14
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x16, x9, #32
        add     x9, x16, x9
        lsr     x16, x9, #32
        subs    x16, x16, x9
        sbc     x15, x9, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x9
        adc     x14, xzr, xzr
        subs    x10, x10, x16
        sbcs    x11, x11, x15
        sbcs    x12, x12, x14
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x16, x10, #32
        add     x10, x16, x10
        lsr     x16, x10, #32
        subs    x16, x16, x10
        sbc     x15, x10, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x10
        adc     x14, xzr, xzr
        subs    x11, x11, x16
        sbcs    x12, x12, x15
        sbcs    x13, x13, x14
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        stp     x11, x12, [sp]
        stp     x13, x8, [sp, #16]
        stp     x9, x10, [sp, #32]
        mul     x8, x2, x5
        mul     x14, x3, x6
        mul     x15, x4, x7
        umulh   x16, x2, x5
        umulh   x17, x3, x6
        umulh   x1, x4, x7
        adds    x16, x16, x14
        adcs    x17, x17, x15
        adc     x1, x1, xzr
        adds    x9, x16, x8
        adcs    x10, x17, x16
        adcs    x11, x1, x17
        adc     x12, x1, xzr
        adds    x10, x10, x8
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x1, xzr
        subs    x17, x2, x3
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x6, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x9, x9, x16
        adcs    x10, x10, x15
        adcs    x11, x11, x14
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x2, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x10, x10, x16
        adcs    x11, x11, x15
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x3, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x6
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x11, x11, x16
        adcs    x12, x12, x15
        adc     x13, x13, x14
        adds    x8, x8, x8
        adcs    x9, x9, x9
        adcs    x10, x10, x10
        adcs    x11, x11, x11
        adcs    x12, x12, x12
        adcs    x13, x13, x13
        adc     x17, xzr, xzr
        ldp     x2, x3, [sp]
        adds    x8, x8, x2
        adcs    x9, x9, x3
        ldp     x2, x3, [sp, #16]
        adcs    x10, x10, x2
        adcs    x11, x11, x3
        ldp     x2, x3, [sp, #32]
        adcs    x12, x12, x2
        adcs    x13, x13, x3
        adc     x17, x17, xzr
        lsl     x4, x8, #32
        add     x8, x4, x8
        lsr     x4, x8, #32
        subs    x4, x4, x8
        sbc     x3, x8, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x8
        adc     x2, xzr, xzr
        subs    x9, x9, x4
        sbcs    x10, x10, x3
        sbcs    x11, x11, x2
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x4, x9, #32
        add     x9, x4, x9
        lsr     x4, x9, #32
        subs    x4, x4, x9
        sbc     x3, x9, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x9
        adc     x2, xzr, xzr
        subs    x10, x10, x4
        sbcs    x11, x11, x3
        sbcs    x12, x12, x2
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x4, x10, #32
        add     x10, x4, x10
        lsr     x4, x10, #32
        subs    x4, x4, x10
        sbc     x3, x10, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x10
        adc     x2, xzr, xzr
        subs    x11, x11, x4
        sbcs    x12, x12, x3
        sbcs    x13, x13, x2
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        adds    x17, x17, x8
        adcs    x8, x9, xzr
        adcs    x9, x10, xzr
        adcs    x10, xzr, xzr
        mul     x1, x5, x5
        adds    x11, x11, x1
        mul     x14, x6, x6
        mul     x15, x7, x7
        umulh   x1, x5, x5
        adcs    x12, x12, x1
        umulh   x1, x6, x6
        adcs    x13, x13, x14
        adcs    x17, x17, x1
        umulh   x1, x7, x7
        adcs    x8, x8, x15
        adcs    x9, x9, x1
        adc     x10, x10, xzr
        mul     x1, x5, x6
        mul     x14, x5, x7
        mul     x15, x6, x7
        umulh   x16, x5, x6
        adds    x14, x14, x16
        umulh   x16, x5, x7
        adcs    x15, x15, x16
        umulh   x16, x6, x7
        adc     x16, x16, xzr
        adds    x1, x1, x1
        adcs    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adc     x5, xzr, xzr
        adds    x12, x12, x1
        adcs    x13, x13, x14
        adcs    x17, x17, x15
        adcs    x8, x8, x16
        adcs    x9, x9, x5
        adc     x10, x10, xzr
        mov     x1, #-4294967295
        mov     x14, #4294967295
        mov     x15, #1
        cmn     x11, x1
        adcs    xzr, x12, x14
        adcs    xzr, x13, x15
        adcs    xzr, x17, xzr
        adcs    xzr, x8, xzr
        adcs    xzr, x9, xzr
        adc     x10, x10, xzr
        neg     x10, x10
        and     x1, x1, x10
        adds    x11, x11, x1
        and     x14, x14, x10
        adcs    x12, x12, x14
        and     x15, x15, x10
        adcs    x13, x13, x15
        adcs    x17, x17, xzr
        adcs    x8, x8, xzr
        adc     x9, x9, xzr
        stp     x11, x12, [sp]
        stp     x13, x17, [sp, #16]
        stp     x8, x9, [sp, #32]
        ldp     x2, x3, [x26, #96]
        ldp     x4, x5, [x26, #112]
        ldp     x6, x7, [x26, #128]
        mul     x14, x2, x3
        mul     x15, x2, x4
        mul     x16, x3, x4
        mul     x8, x2, x2
        mul     x10, x3, x3
        mul     x12, x4, x4
        umulh   x17, x2, x3
        adds    x15, x15, x17
        umulh   x17, x2, x4
        adcs    x16, x16, x17
        umulh   x17, x3, x4
        adcs    x17, x17, xzr
        umulh   x9, x2, x2
        umulh   x11, x3, x3
        umulh   x13, x4, x4
        adds    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adcs    x17, x17, x17
        adc     x13, x13, xzr
        adds    x9, x9, x14
        adcs    x10, x10, x15
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x13, xzr
        lsl     x16, x8, #32
        add     x8, x16, x8
        lsr     x16, x8, #32
        subs    x16, x16, x8
        sbc     x15, x8, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x8
        adc     x14, xzr, xzr
        subs    x9, x9, x16
        sbcs    x10, x10, x15
        sbcs    x11, x11, x14
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x16, x9, #32
        add     x9, x16, x9
        lsr     x16, x9, #32
        subs    x16, x16, x9
        sbc     x15, x9, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x9
        adc     x14, xzr, xzr
        subs    x10, x10, x16
        sbcs    x11, x11, x15
        sbcs    x12, x12, x14
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x16, x10, #32
        add     x10, x16, x10
        lsr     x16, x10, #32
        subs    x16, x16, x10
        sbc     x15, x10, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x10
        adc     x14, xzr, xzr
        subs    x11, x11, x16
        sbcs    x12, x12, x15
        sbcs    x13, x13, x14
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        stp     x11, x12, [sp, #240]
        stp     x13, x8, [sp, #256]
        stp     x9, x10, [sp, #272]
        mul     x8, x2, x5
        mul     x14, x3, x6
        mul     x15, x4, x7
        umulh   x16, x2, x5
        umulh   x17, x3, x6
        umulh   x1, x4, x7
        adds    x16, x16, x14
        adcs    x17, x17, x15
        adc     x1, x1, xzr
        adds    x9, x16, x8
        adcs    x10, x17, x16
        adcs    x11, x1, x17
        adc     x12, x1, xzr
        adds    x10, x10, x8
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x1, xzr
        subs    x17, x2, x3
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x6, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x9, x9, x16
        adcs    x10, x10, x15
        adcs    x11, x11, x14
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x2, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x10, x10, x16
        adcs    x11, x11, x15
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x3, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x6
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x11, x11, x16
        adcs    x12, x12, x15
        adc     x13, x13, x14
        adds    x8, x8, x8
        adcs    x9, x9, x9
        adcs    x10, x10, x10
        adcs    x11, x11, x11
        adcs    x12, x12, x12
        adcs    x13, x13, x13
        adc     x17, xzr, xzr
        ldp     x2, x3, [sp, #240]
        adds    x8, x8, x2
        adcs    x9, x9, x3
        ldp     x2, x3, [sp, #256]
        adcs    x10, x10, x2
        adcs    x11, x11, x3
        ldp     x2, x3, [sp, #272]
        adcs    x12, x12, x2
        adcs    x13, x13, x3
        adc     x17, x17, xzr
        lsl     x4, x8, #32
        add     x8, x4, x8
        lsr     x4, x8, #32
        subs    x4, x4, x8
        sbc     x3, x8, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x8
        adc     x2, xzr, xzr
        subs    x9, x9, x4
        sbcs    x10, x10, x3
        sbcs    x11, x11, x2
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x4, x9, #32
        add     x9, x4, x9
        lsr     x4, x9, #32
        subs    x4, x4, x9
        sbc     x3, x9, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x9
        adc     x2, xzr, xzr
        subs    x10, x10, x4
        sbcs    x11, x11, x3
        sbcs    x12, x12, x2
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x4, x10, #32
        add     x10, x4, x10
        lsr     x4, x10, #32
        subs    x4, x4, x10
        sbc     x3, x10, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x10
        adc     x2, xzr, xzr
        subs    x11, x11, x4
        sbcs    x12, x12, x3
        sbcs    x13, x13, x2
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        adds    x17, x17, x8
        adcs    x8, x9, xzr
        adcs    x9, x10, xzr
        adcs    x10, xzr, xzr
        mul     x1, x5, x5
        adds    x11, x11, x1
        mul     x14, x6, x6
        mul     x15, x7, x7
        umulh   x1, x5, x5
        adcs    x12, x12, x1
        umulh   x1, x6, x6
        adcs    x13, x13, x14
        adcs    x17, x17, x1
        umulh   x1, x7, x7
        adcs    x8, x8, x15
        adcs    x9, x9, x1
        adc     x10, x10, xzr
        mul     x1, x5, x6
        mul     x14, x5, x7
        mul     x15, x6, x7
        umulh   x16, x5, x6
        adds    x14, x14, x16
        umulh   x16, x5, x7
        adcs    x15, x15, x16
        umulh   x16, x6, x7
        adc     x16, x16, xzr
        adds    x1, x1, x1
        adcs    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adc     x5, xzr, xzr
        adds    x12, x12, x1
        adcs    x13, x13, x14
        adcs    x17, x17, x15
        adcs    x8, x8, x16
        adcs    x9, x9, x5
        adc     x10, x10, xzr
        mov     x1, #-4294967295
        mov     x14, #4294967295
        mov     x15, #1
        cmn     x11, x1
        adcs    xzr, x12, x14
        adcs    xzr, x13, x15
        adcs    xzr, x17, xzr
        adcs    xzr, x8, xzr
        adcs    xzr, x9, xzr
        adc     x10, x10, xzr
        neg     x10, x10
        and     x1, x1, x10
        adds    x11, x11, x1
        and     x14, x14, x10
        adcs    x12, x12, x14
        and     x15, x15, x10
        adcs    x13, x13, x15
        adcs    x17, x17, xzr
        adcs    x8, x8, xzr
        adc     x9, x9, xzr
        stp     x11, x12, [sp, #240]
        stp     x13, x17, [sp, #256]
        stp     x8, x9, [sp, #272]
        ldp     x3, x4, [x26, #96]
        ldp     x5, x6, [x26, #112]
        ldp     x7, x8, [x26, #128]
        ldp     x9, x10, [x25, #48]
        ldp     x11, x12, [x25, #64]
        ldp     x13, x14, [x25, #80]
        mul     x15, x3, x9
        mul     x21, x4, x10
        mul     x22, x5, x11
        umulh   x23, x3, x9
        umulh   x0, x4, x10
        umulh   x1, x5, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x3, x4
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x3, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x4, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        stp     x19, x20, [sp, #288]
        stp     x1, x15, [sp, #304]
        stp     x16, x17, [sp, #320]
        mul     x15, x6, x12
        mul     x21, x7, x13
        mul     x22, x8, x14
        umulh   x23, x6, x12
        umulh   x0, x7, x13
        umulh   x1, x8, x14
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x13, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x13
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        subs    x6, x6, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x5
        ngc     x3, xzr
        cmn     x3, #1
        eor     x6, x6, x3
        adcs    x6, x6, xzr
        eor     x7, x7, x3
        adcs    x7, x7, xzr
        eor     x8, x8, x3
        adc     x8, x8, xzr
        subs    x9, x9, x12
        sbcs    x10, x10, x13
        sbcs    x11, x11, x14
        ngc     x14, xzr
        cmn     x14, #1
        eor     x9, x9, x14
        adcs    x9, x9, xzr
        eor     x10, x10, x14
        adcs    x10, x10, xzr
        eor     x11, x11, x14
        adc     x11, x11, xzr
        eor     x14, x3, x14
        ldp     x21, x22, [sp, #288]
        adds    x15, x15, x21
        adcs    x16, x16, x22
        ldp     x21, x22, [sp, #304]
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        ldp     x21, x22, [sp, #320]
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adc     x2, xzr, xzr
        stp     x15, x16, [sp, #288]
        stp     x17, x19, [sp, #304]
        stp     x20, x1, [sp, #320]
        mul     x15, x6, x9
        mul     x21, x7, x10
        mul     x22, x8, x11
        umulh   x23, x6, x9
        umulh   x0, x7, x10
        umulh   x1, x8, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        ldp     x3, x4, [sp, #288]
        ldp     x5, x6, [sp, #304]
        ldp     x7, x8, [sp, #320]
        cmn     x14, #1
        eor     x15, x15, x14
        adcs    x15, x15, x3
        eor     x16, x16, x14
        adcs    x16, x16, x4
        eor     x17, x17, x14
        adcs    x17, x17, x5
        eor     x19, x19, x14
        adcs    x19, x19, x6
        eor     x20, x20, x14
        adcs    x20, x20, x7
        eor     x1, x1, x14
        adcs    x1, x1, x8
        adcs    x9, x14, x2
        adcs    x10, x14, xzr
        adcs    x11, x14, xzr
        adc     x12, x14, xzr
        adds    x19, x19, x3
        adcs    x20, x20, x4
        adcs    x1, x1, x5
        adcs    x9, x9, x6
        adcs    x10, x10, x7
        adcs    x11, x11, x8
        adc     x12, x12, x2
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        adds    x9, x9, x15
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        adc     x12, x12, xzr
        add     x22, x12, #1
        lsl     x21, x22, #32
        subs    x0, x22, x21
        sbc     x21, x21, xzr
        adds    x19, x19, x0
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adcs    x9, x9, xzr
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        csetm   x22, lo
        mov     x23, #4294967295
        and     x23, x23, x22
        adds    x19, x19, x23
        eor     x23, x23, x22
        adcs    x20, x20, x23
        mov     x23, #-2
        and     x23, x23, x22
        adcs    x1, x1, x23
        adcs    x9, x9, x22
        adcs    x10, x10, x22
        adc     x11, x11, x22
        stp     x19, x20, [sp, #288]
        stp     x1, x9, [sp, #304]
        stp     x10, x11, [sp, #320]
        ldp     x3, x4, [x25, #96]
        ldp     x5, x6, [x25, #112]
        ldp     x7, x8, [x25, #128]
        ldp     x9, x10, [x26, #48]
        ldp     x11, x12, [x26, #64]
        ldp     x13, x14, [x26, #80]
        mul     x15, x3, x9
        mul     x21, x4, x10
        mul     x22, x5, x11
        umulh   x23, x3, x9
        umulh   x0, x4, x10
        umulh   x1, x5, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x3, x4
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x3, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x4, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        stp     x19, x20, [sp, #48]
        stp     x1, x15, [sp, #64]
        stp     x16, x17, [sp, #80]
        mul     x15, x6, x12
        mul     x21, x7, x13
        mul     x22, x8, x14
        umulh   x23, x6, x12
        umulh   x0, x7, x13
        umulh   x1, x8, x14
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x13, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x13
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        subs    x6, x6, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x5
        ngc     x3, xzr
        cmn     x3, #1
        eor     x6, x6, x3
        adcs    x6, x6, xzr
        eor     x7, x7, x3
        adcs    x7, x7, xzr
        eor     x8, x8, x3
        adc     x8, x8, xzr
        subs    x9, x9, x12
        sbcs    x10, x10, x13
        sbcs    x11, x11, x14
        ngc     x14, xzr
        cmn     x14, #1
        eor     x9, x9, x14
        adcs    x9, x9, xzr
        eor     x10, x10, x14
        adcs    x10, x10, xzr
        eor     x11, x11, x14
        adc     x11, x11, xzr
        eor     x14, x3, x14
        ldp     x21, x22, [sp, #48]
        adds    x15, x15, x21
        adcs    x16, x16, x22
        ldp     x21, x22, [sp, #64]
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        ldp     x21, x22, [sp, #80]
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adc     x2, xzr, xzr
        stp     x15, x16, [sp, #48]
        stp     x17, x19, [sp, #64]
        stp     x20, x1, [sp, #80]
        mul     x15, x6, x9
        mul     x21, x7, x10
        mul     x22, x8, x11
        umulh   x23, x6, x9
        umulh   x0, x7, x10
        umulh   x1, x8, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        ldp     x3, x4, [sp, #48]
        ldp     x5, x6, [sp, #64]
        ldp     x7, x8, [sp, #80]
        cmn     x14, #1
        eor     x15, x15, x14
        adcs    x15, x15, x3
        eor     x16, x16, x14
        adcs    x16, x16, x4
        eor     x17, x17, x14
        adcs    x17, x17, x5
        eor     x19, x19, x14
        adcs    x19, x19, x6
        eor     x20, x20, x14
        adcs    x20, x20, x7
        eor     x1, x1, x14
        adcs    x1, x1, x8
        adcs    x9, x14, x2
        adcs    x10, x14, xzr
        adcs    x11, x14, xzr
        adc     x12, x14, xzr
        adds    x19, x19, x3
        adcs    x20, x20, x4
        adcs    x1, x1, x5
        adcs    x9, x9, x6
        adcs    x10, x10, x7
        adcs    x11, x11, x8
        adc     x12, x12, x2
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        adds    x9, x9, x15
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        adc     x12, x12, xzr
        add     x22, x12, #1
        lsl     x21, x22, #32
        subs    x0, x22, x21
        sbc     x21, x21, xzr
        adds    x19, x19, x0
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adcs    x9, x9, xzr
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        csetm   x22, lo
        mov     x23, #4294967295
        and     x23, x23, x22
        adds    x19, x19, x23
        eor     x23, x23, x22
        adcs    x20, x20, x23
        mov     x23, #-2
        and     x23, x23, x22
        adcs    x1, x1, x23
        adcs    x9, x9, x22
        adcs    x10, x10, x22
        adc     x11, x11, x22
        stp     x19, x20, [sp, #48]
        stp     x1, x9, [sp, #64]
        stp     x10, x11, [sp, #80]
        ldp     x3, x4, [sp]
        ldp     x5, x6, [sp, #16]
        ldp     x7, x8, [sp, #32]
        ldp     x9, x10, [x26]
        ldp     x11, x12, [x26, #16]
        ldp     x13, x14, [x26, #32]
        mul     x15, x3, x9
        mul     x21, x4, x10
        mul     x22, x5, x11
        umulh   x23, x3, x9
        umulh   x0, x4, x10
        umulh   x1, x5, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x3, x4
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x3, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x4, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        stp     x19, x20, [sp, #96]
        stp     x1, x15, [sp, #112]
        stp     x16, x17, [sp, #128]
        mul     x15, x6, x12
        mul     x21, x7, x13
        mul     x22, x8, x14
        umulh   x23, x6, x12
        umulh   x0, x7, x13
        umulh   x1, x8, x14
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x13, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x13
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        subs    x6, x6, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x5
        ngc     x3, xzr
        cmn     x3, #1
        eor     x6, x6, x3
        adcs    x6, x6, xzr
        eor     x7, x7, x3
        adcs    x7, x7, xzr
        eor     x8, x8, x3
        adc     x8, x8, xzr
        subs    x9, x9, x12
        sbcs    x10, x10, x13
        sbcs    x11, x11, x14
        ngc     x14, xzr
        cmn     x14, #1
        eor     x9, x9, x14
        adcs    x9, x9, xzr
        eor     x10, x10, x14
        adcs    x10, x10, xzr
        eor     x11, x11, x14
        adc     x11, x11, xzr
        eor     x14, x3, x14
        ldp     x21, x22, [sp, #96]
        adds    x15, x15, x21
        adcs    x16, x16, x22
        ldp     x21, x22, [sp, #112]
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        ldp     x21, x22, [sp, #128]
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adc     x2, xzr, xzr
        stp     x15, x16, [sp, #96]
        stp     x17, x19, [sp, #112]
        stp     x20, x1, [sp, #128]
        mul     x15, x6, x9
        mul     x21, x7, x10
        mul     x22, x8, x11
        umulh   x23, x6, x9
        umulh   x0, x7, x10
        umulh   x1, x8, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        ldp     x3, x4, [sp, #96]
        ldp     x5, x6, [sp, #112]
        ldp     x7, x8, [sp, #128]
        cmn     x14, #1
        eor     x15, x15, x14
        adcs    x15, x15, x3
        eor     x16, x16, x14
        adcs    x16, x16, x4
        eor     x17, x17, x14
        adcs    x17, x17, x5
        eor     x19, x19, x14
        adcs    x19, x19, x6
        eor     x20, x20, x14
        adcs    x20, x20, x7
        eor     x1, x1, x14
        adcs    x1, x1, x8
        adcs    x9, x14, x2
        adcs    x10, x14, xzr
        adcs    x11, x14, xzr
        adc     x12, x14, xzr
        adds    x19, x19, x3
        adcs    x20, x20, x4
        adcs    x1, x1, x5
        adcs    x9, x9, x6
        adcs    x10, x10, x7
        adcs    x11, x11, x8
        adc     x12, x12, x2
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        adds    x9, x9, x15
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        adc     x12, x12, xzr
        add     x22, x12, #1
        lsl     x21, x22, #32
        subs    x0, x22, x21
        sbc     x21, x21, xzr
        adds    x19, x19, x0
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adcs    x9, x9, xzr
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        csetm   x22, lo
        mov     x23, #4294967295
        and     x23, x23, x22
        adds    x19, x19, x23
        eor     x23, x23, x22
        adcs    x20, x20, x23
        mov     x23, #-2
        and     x23, x23, x22
        adcs    x1, x1, x23
        adcs    x9, x9, x22
        adcs    x10, x10, x22
        adc     x11, x11, x22
        stp     x19, x20, [sp, #96]
        stp     x1, x9, [sp, #112]
        stp     x10, x11, [sp, #128]
        ldp     x3, x4, [sp, #240]
        ldp     x5, x6, [sp, #256]
        ldp     x7, x8, [sp, #272]
        ldp     x9, x10, [x25]
        ldp     x11, x12, [x25, #16]
        ldp     x13, x14, [x25, #32]
        mul     x15, x3, x9
        mul     x21, x4, x10
        mul     x22, x5, x11
        umulh   x23, x3, x9
        umulh   x0, x4, x10
        umulh   x1, x5, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x3, x4
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x3, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x4, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        stp     x19, x20, [sp, #192]
        stp     x1, x15, [sp, #208]
        stp     x16, x17, [sp, #224]
        mul     x15, x6, x12
        mul     x21, x7, x13
        mul     x22, x8, x14
        umulh   x23, x6, x12
        umulh   x0, x7, x13
        umulh   x1, x8, x14
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x13, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x13
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        subs    x6, x6, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x5
        ngc     x3, xzr
        cmn     x3, #1
        eor     x6, x6, x3
        adcs    x6, x6, xzr
        eor     x7, x7, x3
        adcs    x7, x7, xzr
        eor     x8, x8, x3
        adc     x8, x8, xzr
        subs    x9, x9, x12
        sbcs    x10, x10, x13
        sbcs    x11, x11, x14
        ngc     x14, xzr
        cmn     x14, #1
        eor     x9, x9, x14
        adcs    x9, x9, xzr
        eor     x10, x10, x14
        adcs    x10, x10, xzr
        eor     x11, x11, x14
        adc     x11, x11, xzr
        eor     x14, x3, x14
        ldp     x21, x22, [sp, #192]
        adds    x15, x15, x21
        adcs    x16, x16, x22
        ldp     x21, x22, [sp, #208]
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        ldp     x21, x22, [sp, #224]
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adc     x2, xzr, xzr
        stp     x15, x16, [sp, #192]
        stp     x17, x19, [sp, #208]
        stp     x20, x1, [sp, #224]
        mul     x15, x6, x9
        mul     x21, x7, x10
        mul     x22, x8, x11
        umulh   x23, x6, x9
        umulh   x0, x7, x10
        umulh   x1, x8, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        ldp     x3, x4, [sp, #192]
        ldp     x5, x6, [sp, #208]
        ldp     x7, x8, [sp, #224]
        cmn     x14, #1
        eor     x15, x15, x14
        adcs    x15, x15, x3
        eor     x16, x16, x14
        adcs    x16, x16, x4
        eor     x17, x17, x14
        adcs    x17, x17, x5
        eor     x19, x19, x14
        adcs    x19, x19, x6
        eor     x20, x20, x14
        adcs    x20, x20, x7
        eor     x1, x1, x14
        adcs    x1, x1, x8
        adcs    x9, x14, x2
        adcs    x10, x14, xzr
        adcs    x11, x14, xzr
        adc     x12, x14, xzr
        adds    x19, x19, x3
        adcs    x20, x20, x4
        adcs    x1, x1, x5
        adcs    x9, x9, x6
        adcs    x10, x10, x7
        adcs    x11, x11, x8
        adc     x12, x12, x2
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        adds    x9, x9, x15
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        adc     x12, x12, xzr
        add     x22, x12, #1
        lsl     x21, x22, #32
        subs    x0, x22, x21
        sbc     x21, x21, xzr
        adds    x19, x19, x0
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adcs    x9, x9, xzr
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        csetm   x22, lo
        mov     x23, #4294967295
        and     x23, x23, x22
        adds    x19, x19, x23
        eor     x23, x23, x22
        adcs    x20, x20, x23
        mov     x23, #-2
        and     x23, x23, x22
        adcs    x1, x1, x23
        adcs    x9, x9, x22
        adcs    x10, x10, x22
        adc     x11, x11, x22
        stp     x19, x20, [sp, #192]
        stp     x1, x9, [sp, #208]
        stp     x10, x11, [sp, #224]
        ldp     x3, x4, [sp]
        ldp     x5, x6, [sp, #16]
        ldp     x7, x8, [sp, #32]
        ldp     x9, x10, [sp, #48]
        ldp     x11, x12, [sp, #64]
        ldp     x13, x14, [sp, #80]
        mul     x15, x3, x9
        mul     x21, x4, x10
        mul     x22, x5, x11
        umulh   x23, x3, x9
        umulh   x0, x4, x10
        umulh   x1, x5, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x3, x4
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x3, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x4, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        stp     x19, x20, [sp, #48]
        stp     x1, x15, [sp, #64]
        stp     x16, x17, [sp, #80]
        mul     x15, x6, x12
        mul     x21, x7, x13
        mul     x22, x8, x14
        umulh   x23, x6, x12
        umulh   x0, x7, x13
        umulh   x1, x8, x14
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x13, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x13
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        subs    x6, x6, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x5
        ngc     x3, xzr
        cmn     x3, #1
        eor     x6, x6, x3
        adcs    x6, x6, xzr
        eor     x7, x7, x3
        adcs    x7, x7, xzr
        eor     x8, x8, x3
        adc     x8, x8, xzr
        subs    x9, x9, x12
        sbcs    x10, x10, x13
        sbcs    x11, x11, x14
        ngc     x14, xzr
        cmn     x14, #1
        eor     x9, x9, x14
        adcs    x9, x9, xzr
        eor     x10, x10, x14
        adcs    x10, x10, xzr
        eor     x11, x11, x14
        adc     x11, x11, xzr
        eor     x14, x3, x14
        ldp     x21, x22, [sp, #48]
        adds    x15, x15, x21
        adcs    x16, x16, x22
        ldp     x21, x22, [sp, #64]
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        ldp     x21, x22, [sp, #80]
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adc     x2, xzr, xzr
        stp     x15, x16, [sp, #48]
        stp     x17, x19, [sp, #64]
        stp     x20, x1, [sp, #80]
        mul     x15, x6, x9
        mul     x21, x7, x10
        mul     x22, x8, x11
        umulh   x23, x6, x9
        umulh   x0, x7, x10
        umulh   x1, x8, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        ldp     x3, x4, [sp, #48]
        ldp     x5, x6, [sp, #64]
        ldp     x7, x8, [sp, #80]
        cmn     x14, #1
        eor     x15, x15, x14
        adcs    x15, x15, x3
        eor     x16, x16, x14
        adcs    x16, x16, x4
        eor     x17, x17, x14
        adcs    x17, x17, x5
        eor     x19, x19, x14
        adcs    x19, x19, x6
        eor     x20, x20, x14
        adcs    x20, x20, x7
        eor     x1, x1, x14
        adcs    x1, x1, x8
        adcs    x9, x14, x2
        adcs    x10, x14, xzr
        adcs    x11, x14, xzr
        adc     x12, x14, xzr
        adds    x19, x19, x3
        adcs    x20, x20, x4
        adcs    x1, x1, x5
        adcs    x9, x9, x6
        adcs    x10, x10, x7
        adcs    x11, x11, x8
        adc     x12, x12, x2
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        adds    x9, x9, x15
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        adc     x12, x12, xzr
        add     x22, x12, #1
        lsl     x21, x22, #32
        subs    x0, x22, x21
        sbc     x21, x21, xzr
        adds    x19, x19, x0
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adcs    x9, x9, xzr
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        csetm   x22, lo
        mov     x23, #4294967295
        and     x23, x23, x22
        adds    x19, x19, x23
        eor     x23, x23, x22
        adcs    x20, x20, x23
        mov     x23, #-2
        and     x23, x23, x22
        adcs    x1, x1, x23
        adcs    x9, x9, x22
        adcs    x10, x10, x22
        adc     x11, x11, x22
        stp     x19, x20, [sp, #48]
        stp     x1, x9, [sp, #64]
        stp     x10, x11, [sp, #80]
        ldp     x3, x4, [sp, #240]
        ldp     x5, x6, [sp, #256]
        ldp     x7, x8, [sp, #272]
        ldp     x9, x10, [sp, #288]
        ldp     x11, x12, [sp, #304]
        ldp     x13, x14, [sp, #320]
        mul     x15, x3, x9
        mul     x21, x4, x10
        mul     x22, x5, x11
        umulh   x23, x3, x9
        umulh   x0, x4, x10
        umulh   x1, x5, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x3, x4
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x3, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x4, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        stp     x19, x20, [sp, #288]
        stp     x1, x15, [sp, #304]
        stp     x16, x17, [sp, #320]
        mul     x15, x6, x12
        mul     x21, x7, x13
        mul     x22, x8, x14
        umulh   x23, x6, x12
        umulh   x0, x7, x13
        umulh   x1, x8, x14
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x13, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x13
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        subs    x6, x6, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x5
        ngc     x3, xzr
        cmn     x3, #1
        eor     x6, x6, x3
        adcs    x6, x6, xzr
        eor     x7, x7, x3
        adcs    x7, x7, xzr
        eor     x8, x8, x3
        adc     x8, x8, xzr
        subs    x9, x9, x12
        sbcs    x10, x10, x13
        sbcs    x11, x11, x14
        ngc     x14, xzr
        cmn     x14, #1
        eor     x9, x9, x14
        adcs    x9, x9, xzr
        eor     x10, x10, x14
        adcs    x10, x10, xzr
        eor     x11, x11, x14
        adc     x11, x11, xzr
        eor     x14, x3, x14
        ldp     x21, x22, [sp, #288]
        adds    x15, x15, x21
        adcs    x16, x16, x22
        ldp     x21, x22, [sp, #304]
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        ldp     x21, x22, [sp, #320]
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adc     x2, xzr, xzr
        stp     x15, x16, [sp, #288]
        stp     x17, x19, [sp, #304]
        stp     x20, x1, [sp, #320]
        mul     x15, x6, x9
        mul     x21, x7, x10
        mul     x22, x8, x11
        umulh   x23, x6, x9
        umulh   x0, x7, x10
        umulh   x1, x8, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        ldp     x3, x4, [sp, #288]
        ldp     x5, x6, [sp, #304]
        ldp     x7, x8, [sp, #320]
        cmn     x14, #1
        eor     x15, x15, x14
        adcs    x15, x15, x3
        eor     x16, x16, x14
        adcs    x16, x16, x4
        eor     x17, x17, x14
        adcs    x17, x17, x5
        eor     x19, x19, x14
        adcs    x19, x19, x6
        eor     x20, x20, x14
        adcs    x20, x20, x7
        eor     x1, x1, x14
        adcs    x1, x1, x8
        adcs    x9, x14, x2
        adcs    x10, x14, xzr
        adcs    x11, x14, xzr
        adc     x12, x14, xzr
        adds    x19, x19, x3
        adcs    x20, x20, x4
        adcs    x1, x1, x5
        adcs    x9, x9, x6
        adcs    x10, x10, x7
        adcs    x11, x11, x8
        adc     x12, x12, x2
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        adds    x9, x9, x15
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        adc     x12, x12, xzr
        add     x22, x12, #1
        lsl     x21, x22, #32
        subs    x0, x22, x21
        sbc     x21, x21, xzr
        adds    x19, x19, x0
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adcs    x9, x9, xzr
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        csetm   x22, lo
        mov     x23, #4294967295
        and     x23, x23, x22
        adds    x19, x19, x23
        eor     x23, x23, x22
        adcs    x20, x20, x23
        mov     x23, #-2
        and     x23, x23, x22
        adcs    x1, x1, x23
        adcs    x9, x9, x22
        adcs    x10, x10, x22
        adc     x11, x11, x22
        stp     x19, x20, [sp, #288]
        stp     x1, x9, [sp, #304]
        stp     x10, x11, [sp, #320]
        ldp     x5, x6, [sp, #96]
        ldp     x4, x3, [sp, #192]
        subs    x5, x5, x4
        sbcs    x6, x6, x3
        ldp     x7, x8, [sp, #112]
        ldp     x4, x3, [sp, #208]
        sbcs    x7, x7, x4
        sbcs    x8, x8, x3
        ldp     x9, x10, [sp, #128]
        ldp     x4, x3, [sp, #224]
        sbcs    x9, x9, x4
        sbcs    x10, x10, x3
        csetm   x3, lo
        mov     x4, #4294967295
        and     x4, x4, x3
        adds    x5, x5, x4
        eor     x4, x4, x3
        adcs    x6, x6, x4
        mov     x4, #-2
        and     x4, x4, x3
        adcs    x7, x7, x4
        adcs    x8, x8, x3
        adcs    x9, x9, x3
        adc     x10, x10, x3
        stp     x5, x6, [sp, #240]
        stp     x7, x8, [sp, #256]
        stp     x9, x10, [sp, #272]
        ldp     x5, x6, [sp, #48]
        ldp     x4, x3, [sp, #288]
        subs    x5, x5, x4
        sbcs    x6, x6, x3
        ldp     x7, x8, [sp, #64]
        ldp     x4, x3, [sp, #304]
        sbcs    x7, x7, x4
        sbcs    x8, x8, x3
        ldp     x9, x10, [sp, #80]
        ldp     x4, x3, [sp, #320]
        sbcs    x9, x9, x4
        sbcs    x10, x10, x3
        csetm   x3, lo
        mov     x4, #4294967295
        and     x4, x4, x3
        adds    x5, x5, x4
        eor     x4, x4, x3
        adcs    x6, x6, x4
        mov     x4, #-2
        and     x4, x4, x3
        adcs    x7, x7, x4
        adcs    x8, x8, x3
        adcs    x9, x9, x3
        adc     x10, x10, x3
        stp     x5, x6, [sp, #48]
        stp     x7, x8, [sp, #64]
        stp     x9, x10, [sp, #80]
        ldp     x2, x3, [sp, #240]
        ldp     x4, x5, [sp, #256]
        ldp     x6, x7, [sp, #272]
        mul     x14, x2, x3
        mul     x15, x2, x4
        mul     x16, x3, x4
        mul     x8, x2, x2
        mul     x10, x3, x3
        mul     x12, x4, x4
        umulh   x17, x2, x3
        adds    x15, x15, x17
        umulh   x17, x2, x4
        adcs    x16, x16, x17
        umulh   x17, x3, x4
        adcs    x17, x17, xzr
        umulh   x9, x2, x2
        umulh   x11, x3, x3
        umulh   x13, x4, x4
        adds    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adcs    x17, x17, x17
        adc     x13, x13, xzr
        adds    x9, x9, x14
        adcs    x10, x10, x15
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x13, xzr
        lsl     x16, x8, #32
        add     x8, x16, x8
        lsr     x16, x8, #32
        subs    x16, x16, x8
        sbc     x15, x8, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x8
        adc     x14, xzr, xzr
        subs    x9, x9, x16
        sbcs    x10, x10, x15
        sbcs    x11, x11, x14
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x16, x9, #32
        add     x9, x16, x9
        lsr     x16, x9, #32
        subs    x16, x16, x9
        sbc     x15, x9, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x9
        adc     x14, xzr, xzr
        subs    x10, x10, x16
        sbcs    x11, x11, x15
        sbcs    x12, x12, x14
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x16, x10, #32
        add     x10, x16, x10
        lsr     x16, x10, #32
        subs    x16, x16, x10
        sbc     x15, x10, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x10
        adc     x14, xzr, xzr
        subs    x11, x11, x16
        sbcs    x12, x12, x15
        sbcs    x13, x13, x14
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        stp     x11, x12, [sp, #144]
        stp     x13, x8, [sp, #160]
        stp     x9, x10, [sp, #176]
        mul     x8, x2, x5
        mul     x14, x3, x6
        mul     x15, x4, x7
        umulh   x16, x2, x5
        umulh   x17, x3, x6
        umulh   x1, x4, x7
        adds    x16, x16, x14
        adcs    x17, x17, x15
        adc     x1, x1, xzr
        adds    x9, x16, x8
        adcs    x10, x17, x16
        adcs    x11, x1, x17
        adc     x12, x1, xzr
        adds    x10, x10, x8
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x1, xzr
        subs    x17, x2, x3
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x6, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x9, x9, x16
        adcs    x10, x10, x15
        adcs    x11, x11, x14
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x2, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x10, x10, x16
        adcs    x11, x11, x15
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x3, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x6
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x11, x11, x16
        adcs    x12, x12, x15
        adc     x13, x13, x14
        adds    x8, x8, x8
        adcs    x9, x9, x9
        adcs    x10, x10, x10
        adcs    x11, x11, x11
        adcs    x12, x12, x12
        adcs    x13, x13, x13
        adc     x17, xzr, xzr
        ldp     x2, x3, [sp, #144]
        adds    x8, x8, x2
        adcs    x9, x9, x3
        ldp     x2, x3, [sp, #160]
        adcs    x10, x10, x2
        adcs    x11, x11, x3
        ldp     x2, x3, [sp, #176]
        adcs    x12, x12, x2
        adcs    x13, x13, x3
        adc     x17, x17, xzr
        lsl     x4, x8, #32
        add     x8, x4, x8
        lsr     x4, x8, #32
        subs    x4, x4, x8
        sbc     x3, x8, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x8
        adc     x2, xzr, xzr
        subs    x9, x9, x4
        sbcs    x10, x10, x3
        sbcs    x11, x11, x2
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x4, x9, #32
        add     x9, x4, x9
        lsr     x4, x9, #32
        subs    x4, x4, x9
        sbc     x3, x9, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x9
        adc     x2, xzr, xzr
        subs    x10, x10, x4
        sbcs    x11, x11, x3
        sbcs    x12, x12, x2
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x4, x10, #32
        add     x10, x4, x10
        lsr     x4, x10, #32
        subs    x4, x4, x10
        sbc     x3, x10, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x10
        adc     x2, xzr, xzr
        subs    x11, x11, x4
        sbcs    x12, x12, x3
        sbcs    x13, x13, x2
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        adds    x17, x17, x8
        adcs    x8, x9, xzr
        adcs    x9, x10, xzr
        adcs    x10, xzr, xzr
        mul     x1, x5, x5
        adds    x11, x11, x1
        mul     x14, x6, x6
        mul     x15, x7, x7
        umulh   x1, x5, x5
        adcs    x12, x12, x1
        umulh   x1, x6, x6
        adcs    x13, x13, x14
        adcs    x17, x17, x1
        umulh   x1, x7, x7
        adcs    x8, x8, x15
        adcs    x9, x9, x1
        adc     x10, x10, xzr
        mul     x1, x5, x6
        mul     x14, x5, x7
        mul     x15, x6, x7
        umulh   x16, x5, x6
        adds    x14, x14, x16
        umulh   x16, x5, x7
        adcs    x15, x15, x16
        umulh   x16, x6, x7
        adc     x16, x16, xzr
        adds    x1, x1, x1
        adcs    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adc     x5, xzr, xzr
        adds    x12, x12, x1
        adcs    x13, x13, x14
        adcs    x17, x17, x15
        adcs    x8, x8, x16
        adcs    x9, x9, x5
        adc     x10, x10, xzr
        mov     x1, #-4294967295
        mov     x14, #4294967295
        mov     x15, #1
        cmn     x11, x1
        adcs    xzr, x12, x14
        adcs    xzr, x13, x15
        adcs    xzr, x17, xzr
        adcs    xzr, x8, xzr
        adcs    xzr, x9, xzr
        adc     x10, x10, xzr
        neg     x10, x10
        and     x1, x1, x10
        adds    x11, x11, x1
        and     x14, x14, x10
        adcs    x12, x12, x14
        and     x15, x15, x10
        adcs    x13, x13, x15
        adcs    x17, x17, xzr
        adcs    x8, x8, xzr
        adc     x9, x9, xzr
        stp     x11, x12, [sp, #144]
        stp     x13, x17, [sp, #160]
        stp     x8, x9, [sp, #176]
        ldp     x2, x3, [sp, #48]
        ldp     x4, x5, [sp, #64]
        ldp     x6, x7, [sp, #80]
        mul     x14, x2, x3
        mul     x15, x2, x4
        mul     x16, x3, x4
        mul     x8, x2, x2
        mul     x10, x3, x3
        mul     x12, x4, x4
        umulh   x17, x2, x3
        adds    x15, x15, x17
        umulh   x17, x2, x4
        adcs    x16, x16, x17
        umulh   x17, x3, x4
        adcs    x17, x17, xzr
        umulh   x9, x2, x2
        umulh   x11, x3, x3
        umulh   x13, x4, x4
        adds    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adcs    x17, x17, x17
        adc     x13, x13, xzr
        adds    x9, x9, x14
        adcs    x10, x10, x15
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x13, xzr
        lsl     x16, x8, #32
        add     x8, x16, x8
        lsr     x16, x8, #32
        subs    x16, x16, x8
        sbc     x15, x8, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x8
        adc     x14, xzr, xzr
        subs    x9, x9, x16
        sbcs    x10, x10, x15
        sbcs    x11, x11, x14
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x16, x9, #32
        add     x9, x16, x9
        lsr     x16, x9, #32
        subs    x16, x16, x9
        sbc     x15, x9, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x9
        adc     x14, xzr, xzr
        subs    x10, x10, x16
        sbcs    x11, x11, x15
        sbcs    x12, x12, x14
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x16, x10, #32
        add     x10, x16, x10
        lsr     x16, x10, #32
        subs    x16, x16, x10
        sbc     x15, x10, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x10
        adc     x14, xzr, xzr
        subs    x11, x11, x16
        sbcs    x12, x12, x15
        sbcs    x13, x13, x14
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        stp     x11, x12, [sp]
        stp     x13, x8, [sp, #16]
        stp     x9, x10, [sp, #32]
        mul     x8, x2, x5
        mul     x14, x3, x6
        mul     x15, x4, x7
        umulh   x16, x2, x5
        umulh   x17, x3, x6
        umulh   x1, x4, x7
        adds    x16, x16, x14
        adcs    x17, x17, x15
        adc     x1, x1, xzr
        adds    x9, x16, x8
        adcs    x10, x17, x16
        adcs    x11, x1, x17
        adc     x12, x1, xzr
        adds    x10, x10, x8
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x1, xzr
        subs    x17, x2, x3
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x6, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x9, x9, x16
        adcs    x10, x10, x15
        adcs    x11, x11, x14
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x2, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x10, x10, x16
        adcs    x11, x11, x15
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x3, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x6
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x11, x11, x16
        adcs    x12, x12, x15
        adc     x13, x13, x14
        adds    x8, x8, x8
        adcs    x9, x9, x9
        adcs    x10, x10, x10
        adcs    x11, x11, x11
        adcs    x12, x12, x12
        adcs    x13, x13, x13
        adc     x17, xzr, xzr
        ldp     x2, x3, [sp]
        adds    x8, x8, x2
        adcs    x9, x9, x3
        ldp     x2, x3, [sp, #16]
        adcs    x10, x10, x2
        adcs    x11, x11, x3
        ldp     x2, x3, [sp, #32]
        adcs    x12, x12, x2
        adcs    x13, x13, x3
        adc     x17, x17, xzr
        lsl     x4, x8, #32
        add     x8, x4, x8
        lsr     x4, x8, #32
        subs    x4, x4, x8
        sbc     x3, x8, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x8
        adc     x2, xzr, xzr
        subs    x9, x9, x4
        sbcs    x10, x10, x3
        sbcs    x11, x11, x2
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x4, x9, #32
        add     x9, x4, x9
        lsr     x4, x9, #32
        subs    x4, x4, x9
        sbc     x3, x9, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x9
        adc     x2, xzr, xzr
        subs    x10, x10, x4
        sbcs    x11, x11, x3
        sbcs    x12, x12, x2
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x4, x10, #32
        add     x10, x4, x10
        lsr     x4, x10, #32
        subs    x4, x4, x10
        sbc     x3, x10, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x10
        adc     x2, xzr, xzr
        subs    x11, x11, x4
        sbcs    x12, x12, x3
        sbcs    x13, x13, x2
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        adds    x17, x17, x8
        adcs    x8, x9, xzr
        adcs    x9, x10, xzr
        adcs    x10, xzr, xzr
        mul     x1, x5, x5
        adds    x11, x11, x1
        mul     x14, x6, x6
        mul     x15, x7, x7
        umulh   x1, x5, x5
        adcs    x12, x12, x1
        umulh   x1, x6, x6
        adcs    x13, x13, x14
        adcs    x17, x17, x1
        umulh   x1, x7, x7
        adcs    x8, x8, x15
        adcs    x9, x9, x1
        adc     x10, x10, xzr
        mul     x1, x5, x6
        mul     x14, x5, x7
        mul     x15, x6, x7
        umulh   x16, x5, x6
        adds    x14, x14, x16
        umulh   x16, x5, x7
        adcs    x15, x15, x16
        umulh   x16, x6, x7
        adc     x16, x16, xzr
        adds    x1, x1, x1
        adcs    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adc     x5, xzr, xzr
        adds    x12, x12, x1
        adcs    x13, x13, x14
        adcs    x17, x17, x15
        adcs    x8, x8, x16
        adcs    x9, x9, x5
        adc     x10, x10, xzr
        mov     x1, #-4294967295
        mov     x14, #4294967295
        mov     x15, #1
        cmn     x11, x1
        adcs    xzr, x12, x14
        adcs    xzr, x13, x15
        adcs    xzr, x17, xzr
        adcs    xzr, x8, xzr
        adcs    xzr, x9, xzr
        adc     x10, x10, xzr
        neg     x10, x10
        and     x1, x1, x10
        adds    x11, x11, x1
        and     x14, x14, x10
        adcs    x12, x12, x14
        and     x15, x15, x10
        adcs    x13, x13, x15
        adcs    x17, x17, xzr
        adcs    x8, x8, xzr
        adc     x9, x9, xzr
        stp     x11, x12, [sp]
        stp     x13, x17, [sp, #16]
        stp     x8, x9, [sp, #32]
        ldp     x3, x4, [sp, #144]
        ldp     x5, x6, [sp, #160]
        ldp     x7, x8, [sp, #176]
        ldp     x9, x10, [sp, #192]
        ldp     x11, x12, [sp, #208]
        ldp     x13, x14, [sp, #224]
        mul     x15, x3, x9
        mul     x21, x4, x10
        mul     x22, x5, x11
        umulh   x23, x3, x9
        umulh   x0, x4, x10
        umulh   x1, x5, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x3, x4
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x3, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x4, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        stp     x19, x20, [sp, #192]
        stp     x1, x15, [sp, #208]
        stp     x16, x17, [sp, #224]
        mul     x15, x6, x12
        mul     x21, x7, x13
        mul     x22, x8, x14
        umulh   x23, x6, x12
        umulh   x0, x7, x13
        umulh   x1, x8, x14
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x13, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x13
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        subs    x6, x6, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x5
        ngc     x3, xzr
        cmn     x3, #1
        eor     x6, x6, x3
        adcs    x6, x6, xzr
        eor     x7, x7, x3
        adcs    x7, x7, xzr
        eor     x8, x8, x3
        adc     x8, x8, xzr
        subs    x9, x9, x12
        sbcs    x10, x10, x13
        sbcs    x11, x11, x14
        ngc     x14, xzr
        cmn     x14, #1
        eor     x9, x9, x14
        adcs    x9, x9, xzr
        eor     x10, x10, x14
        adcs    x10, x10, xzr
        eor     x11, x11, x14
        adc     x11, x11, xzr
        eor     x14, x3, x14
        ldp     x21, x22, [sp, #192]
        adds    x15, x15, x21
        adcs    x16, x16, x22
        ldp     x21, x22, [sp, #208]
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        ldp     x21, x22, [sp, #224]
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adc     x2, xzr, xzr
        stp     x15, x16, [sp, #192]
        stp     x17, x19, [sp, #208]
        stp     x20, x1, [sp, #224]
        mul     x15, x6, x9
        mul     x21, x7, x10
        mul     x22, x8, x11
        umulh   x23, x6, x9
        umulh   x0, x7, x10
        umulh   x1, x8, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        ldp     x3, x4, [sp, #192]
        ldp     x5, x6, [sp, #208]
        ldp     x7, x8, [sp, #224]
        cmn     x14, #1
        eor     x15, x15, x14
        adcs    x15, x15, x3
        eor     x16, x16, x14
        adcs    x16, x16, x4
        eor     x17, x17, x14
        adcs    x17, x17, x5
        eor     x19, x19, x14
        adcs    x19, x19, x6
        eor     x20, x20, x14
        adcs    x20, x20, x7
        eor     x1, x1, x14
        adcs    x1, x1, x8
        adcs    x9, x14, x2
        adcs    x10, x14, xzr
        adcs    x11, x14, xzr
        adc     x12, x14, xzr
        adds    x19, x19, x3
        adcs    x20, x20, x4
        adcs    x1, x1, x5
        adcs    x9, x9, x6
        adcs    x10, x10, x7
        adcs    x11, x11, x8
        adc     x12, x12, x2
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        adds    x9, x9, x15
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        adc     x12, x12, xzr
        add     x22, x12, #1
        lsl     x21, x22, #32
        subs    x0, x22, x21
        sbc     x21, x21, xzr
        adds    x19, x19, x0
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adcs    x9, x9, xzr
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        csetm   x22, lo
        mov     x23, #4294967295
        and     x23, x23, x22
        adds    x19, x19, x23
        eor     x23, x23, x22
        adcs    x20, x20, x23
        mov     x23, #-2
        and     x23, x23, x22
        adcs    x1, x1, x23
        adcs    x9, x9, x22
        adcs    x10, x10, x22
        adc     x11, x11, x22
        stp     x19, x20, [sp, #192]
        stp     x1, x9, [sp, #208]
        stp     x10, x11, [sp, #224]
        ldp     x3, x4, [sp, #144]
        ldp     x5, x6, [sp, #160]
        ldp     x7, x8, [sp, #176]
        ldp     x9, x10, [sp, #96]
        ldp     x11, x12, [sp, #112]
        ldp     x13, x14, [sp, #128]
        mul     x15, x3, x9
        mul     x21, x4, x10
        mul     x22, x5, x11
        umulh   x23, x3, x9
        umulh   x0, x4, x10
        umulh   x1, x5, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x3, x4
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x3, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x4, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        stp     x19, x20, [sp, #96]
        stp     x1, x15, [sp, #112]
        stp     x16, x17, [sp, #128]
        mul     x15, x6, x12
        mul     x21, x7, x13
        mul     x22, x8, x14
        umulh   x23, x6, x12
        umulh   x0, x7, x13
        umulh   x1, x8, x14
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x13, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x13
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        subs    x6, x6, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x5
        ngc     x3, xzr
        cmn     x3, #1
        eor     x6, x6, x3
        adcs    x6, x6, xzr
        eor     x7, x7, x3
        adcs    x7, x7, xzr
        eor     x8, x8, x3
        adc     x8, x8, xzr
        subs    x9, x9, x12
        sbcs    x10, x10, x13
        sbcs    x11, x11, x14
        ngc     x14, xzr
        cmn     x14, #1
        eor     x9, x9, x14
        adcs    x9, x9, xzr
        eor     x10, x10, x14
        adcs    x10, x10, xzr
        eor     x11, x11, x14
        adc     x11, x11, xzr
        eor     x14, x3, x14
        ldp     x21, x22, [sp, #96]
        adds    x15, x15, x21
        adcs    x16, x16, x22
        ldp     x21, x22, [sp, #112]
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        ldp     x21, x22, [sp, #128]
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adc     x2, xzr, xzr
        stp     x15, x16, [sp, #96]
        stp     x17, x19, [sp, #112]
        stp     x20, x1, [sp, #128]
        mul     x15, x6, x9
        mul     x21, x7, x10
        mul     x22, x8, x11
        umulh   x23, x6, x9
        umulh   x0, x7, x10
        umulh   x1, x8, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        ldp     x3, x4, [sp, #96]
        ldp     x5, x6, [sp, #112]
        ldp     x7, x8, [sp, #128]
        cmn     x14, #1
        eor     x15, x15, x14
        adcs    x15, x15, x3
        eor     x16, x16, x14
        adcs    x16, x16, x4
        eor     x17, x17, x14
        adcs    x17, x17, x5
        eor     x19, x19, x14
        adcs    x19, x19, x6
        eor     x20, x20, x14
        adcs    x20, x20, x7
        eor     x1, x1, x14
        adcs    x1, x1, x8
        adcs    x9, x14, x2
        adcs    x10, x14, xzr
        adcs    x11, x14, xzr
        adc     x12, x14, xzr
        adds    x19, x19, x3
        adcs    x20, x20, x4
        adcs    x1, x1, x5
        adcs    x9, x9, x6
        adcs    x10, x10, x7
        adcs    x11, x11, x8
        adc     x12, x12, x2
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        adds    x9, x9, x15
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        adc     x12, x12, xzr
        add     x22, x12, #1
        lsl     x21, x22, #32
        subs    x0, x22, x21
        sbc     x21, x21, xzr
        adds    x19, x19, x0
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adcs    x9, x9, xzr
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        csetm   x22, lo
        mov     x23, #4294967295
        and     x23, x23, x22
        adds    x19, x19, x23
        eor     x23, x23, x22
        adcs    x20, x20, x23
        mov     x23, #-2
        and     x23, x23, x22
        adcs    x1, x1, x23
        adcs    x9, x9, x22
        adcs    x10, x10, x22
        adc     x11, x11, x22
        stp     x19, x20, [sp, #96]
        stp     x1, x9, [sp, #112]
        stp     x10, x11, [sp, #128]
        ldp     x5, x6, [sp]
        ldp     x4, x3, [sp, #192]
        subs    x5, x5, x4
        sbcs    x6, x6, x3
        ldp     x7, x8, [sp, #16]
        ldp     x4, x3, [sp, #208]
        sbcs    x7, x7, x4
        sbcs    x8, x8, x3
        ldp     x9, x10, [sp, #32]
        ldp     x4, x3, [sp, #224]
        sbcs    x9, x9, x4
        sbcs    x10, x10, x3
        csetm   x3, lo
        mov     x4, #4294967295
        and     x4, x4, x3
        adds    x5, x5, x4
        eor     x4, x4, x3
        adcs    x6, x6, x4
        mov     x4, #-2
        and     x4, x4, x3
        adcs    x7, x7, x4
        adcs    x8, x8, x3
        adcs    x9, x9, x3
        adc     x10, x10, x3
        stp     x5, x6, [sp]
        stp     x7, x8, [sp, #16]
        stp     x9, x10, [sp, #32]
        ldp     x5, x6, [sp, #96]
        ldp     x4, x3, [sp, #192]
        subs    x5, x5, x4
        sbcs    x6, x6, x3
        ldp     x7, x8, [sp, #112]
        ldp     x4, x3, [sp, #208]
        sbcs    x7, x7, x4
        sbcs    x8, x8, x3
        ldp     x9, x10, [sp, #128]
        ldp     x4, x3, [sp, #224]
        sbcs    x9, x9, x4
        sbcs    x10, x10, x3
        csetm   x3, lo
        mov     x4, #4294967295
        and     x4, x4, x3
        adds    x5, x5, x4
        eor     x4, x4, x3
        adcs    x6, x6, x4
        mov     x4, #-2
        and     x4, x4, x3
        adcs    x7, x7, x4
        adcs    x8, x8, x3
        adcs    x9, x9, x3
        adc     x10, x10, x3
        stp     x5, x6, [sp, #144]
        stp     x7, x8, [sp, #160]
        stp     x9, x10, [sp, #176]
        ldp     x3, x4, [sp, #240]
        ldp     x5, x6, [sp, #256]
        ldp     x7, x8, [sp, #272]
        ldp     x9, x10, [x25, #96]
        ldp     x11, x12, [x25, #112]
        ldp     x13, x14, [x25, #128]
        mul     x15, x3, x9
        mul     x21, x4, x10
        mul     x22, x5, x11
        umulh   x23, x3, x9
        umulh   x0, x4, x10
        umulh   x1, x5, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x3, x4
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x3, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x4, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        stp     x19, x20, [sp, #240]
        stp     x1, x15, [sp, #256]
        stp     x16, x17, [sp, #272]
        mul     x15, x6, x12
        mul     x21, x7, x13
        mul     x22, x8, x14
        umulh   x23, x6, x12
        umulh   x0, x7, x13
        umulh   x1, x8, x14
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x13, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x13
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        subs    x6, x6, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x5
        ngc     x3, xzr
        cmn     x3, #1
        eor     x6, x6, x3
        adcs    x6, x6, xzr
        eor     x7, x7, x3
        adcs    x7, x7, xzr
        eor     x8, x8, x3
        adc     x8, x8, xzr
        subs    x9, x9, x12
        sbcs    x10, x10, x13
        sbcs    x11, x11, x14
        ngc     x14, xzr
        cmn     x14, #1
        eor     x9, x9, x14
        adcs    x9, x9, xzr
        eor     x10, x10, x14
        adcs    x10, x10, xzr
        eor     x11, x11, x14
        adc     x11, x11, xzr
        eor     x14, x3, x14
        ldp     x21, x22, [sp, #240]
        adds    x15, x15, x21
        adcs    x16, x16, x22
        ldp     x21, x22, [sp, #256]
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        ldp     x21, x22, [sp, #272]
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adc     x2, xzr, xzr
        stp     x15, x16, [sp, #240]
        stp     x17, x19, [sp, #256]
        stp     x20, x1, [sp, #272]
        mul     x15, x6, x9
        mul     x21, x7, x10
        mul     x22, x8, x11
        umulh   x23, x6, x9
        umulh   x0, x7, x10
        umulh   x1, x8, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        ldp     x3, x4, [sp, #240]
        ldp     x5, x6, [sp, #256]
        ldp     x7, x8, [sp, #272]
        cmn     x14, #1
        eor     x15, x15, x14
        adcs    x15, x15, x3
        eor     x16, x16, x14
        adcs    x16, x16, x4
        eor     x17, x17, x14
        adcs    x17, x17, x5
        eor     x19, x19, x14
        adcs    x19, x19, x6
        eor     x20, x20, x14
        adcs    x20, x20, x7
        eor     x1, x1, x14
        adcs    x1, x1, x8
        adcs    x9, x14, x2
        adcs    x10, x14, xzr
        adcs    x11, x14, xzr
        adc     x12, x14, xzr
        adds    x19, x19, x3
        adcs    x20, x20, x4
        adcs    x1, x1, x5
        adcs    x9, x9, x6
        adcs    x10, x10, x7
        adcs    x11, x11, x8
        adc     x12, x12, x2
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        adds    x9, x9, x15
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        adc     x12, x12, xzr
        add     x22, x12, #1
        lsl     x21, x22, #32
        subs    x0, x22, x21
        sbc     x21, x21, xzr
        adds    x19, x19, x0
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adcs    x9, x9, xzr
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        csetm   x22, lo
        mov     x23, #4294967295
        and     x23, x23, x22
        adds    x19, x19, x23
        eor     x23, x23, x22
        adcs    x20, x20, x23
        mov     x23, #-2
        and     x23, x23, x22
        adcs    x1, x1, x23
        adcs    x9, x9, x22
        adcs    x10, x10, x22
        adc     x11, x11, x22
        stp     x19, x20, [sp, #240]
        stp     x1, x9, [sp, #256]
        stp     x10, x11, [sp, #272]
        ldp     x5, x6, [sp]
        ldp     x4, x3, [sp, #96]
        subs    x5, x5, x4
        sbcs    x6, x6, x3
        ldp     x7, x8, [sp, #16]
        ldp     x4, x3, [sp, #112]
        sbcs    x7, x7, x4
        sbcs    x8, x8, x3
        ldp     x9, x10, [sp, #32]
        ldp     x4, x3, [sp, #128]
        sbcs    x9, x9, x4
        sbcs    x10, x10, x3
        csetm   x3, lo
        mov     x4, #4294967295
        and     x4, x4, x3
        adds    x5, x5, x4
        eor     x4, x4, x3
        adcs    x6, x6, x4
        mov     x4, #-2
        and     x4, x4, x3
        adcs    x7, x7, x4
        adcs    x8, x8, x3
        adcs    x9, x9, x3
        adc     x10, x10, x3
        stp     x5, x6, [sp]
        stp     x7, x8, [sp, #16]
        stp     x9, x10, [sp, #32]
        ldp     x5, x6, [sp, #192]
        ldp     x4, x3, [sp]
        subs    x5, x5, x4
        sbcs    x6, x6, x3
        ldp     x7, x8, [sp, #208]
        ldp     x4, x3, [sp, #16]
        sbcs    x7, x7, x4
        sbcs    x8, x8, x3
        ldp     x9, x10, [sp, #224]
        ldp     x4, x3, [sp, #32]
        sbcs    x9, x9, x4
        sbcs    x10, x10, x3
        csetm   x3, lo
        mov     x4, #4294967295
        and     x4, x4, x3
        adds    x5, x5, x4
        eor     x4, x4, x3
        adcs    x6, x6, x4
        mov     x4, #-2
        and     x4, x4, x3
        adcs    x7, x7, x4
        adcs    x8, x8, x3
        adcs    x9, x9, x3
        adc     x10, x10, x3
        stp     x5, x6, [sp, #192]
        stp     x7, x8, [sp, #208]
        stp     x9, x10, [sp, #224]
        ldp     x3, x4, [sp, #144]
        ldp     x5, x6, [sp, #160]
        ldp     x7, x8, [sp, #176]
        ldp     x9, x10, [sp, #288]
        ldp     x11, x12, [sp, #304]
        ldp     x13, x14, [sp, #320]
        mul     x15, x3, x9
        mul     x21, x4, x10
        mul     x22, x5, x11
        umulh   x23, x3, x9
        umulh   x0, x4, x10
        umulh   x1, x5, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x3, x4
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x3, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x4, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        stp     x19, x20, [sp, #144]
        stp     x1, x15, [sp, #160]
        stp     x16, x17, [sp, #176]
        mul     x15, x6, x12
        mul     x21, x7, x13
        mul     x22, x8, x14
        umulh   x23, x6, x12
        umulh   x0, x7, x13
        umulh   x1, x8, x14
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x13, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x13
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        subs    x6, x6, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x5
        ngc     x3, xzr
        cmn     x3, #1
        eor     x6, x6, x3
        adcs    x6, x6, xzr
        eor     x7, x7, x3
        adcs    x7, x7, xzr
        eor     x8, x8, x3
        adc     x8, x8, xzr
        subs    x9, x9, x12
        sbcs    x10, x10, x13
        sbcs    x11, x11, x14
        ngc     x14, xzr
        cmn     x14, #1
        eor     x9, x9, x14
        adcs    x9, x9, xzr
        eor     x10, x10, x14
        adcs    x10, x10, xzr
        eor     x11, x11, x14
        adc     x11, x11, xzr
        eor     x14, x3, x14
        ldp     x21, x22, [sp, #144]
        adds    x15, x15, x21
        adcs    x16, x16, x22
        ldp     x21, x22, [sp, #160]
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        ldp     x21, x22, [sp, #176]
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adc     x2, xzr, xzr
        stp     x15, x16, [sp, #144]
        stp     x17, x19, [sp, #160]
        stp     x20, x1, [sp, #176]
        mul     x15, x6, x9
        mul     x21, x7, x10
        mul     x22, x8, x11
        umulh   x23, x6, x9
        umulh   x0, x7, x10
        umulh   x1, x8, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        ldp     x3, x4, [sp, #144]
        ldp     x5, x6, [sp, #160]
        ldp     x7, x8, [sp, #176]
        cmn     x14, #1
        eor     x15, x15, x14
        adcs    x15, x15, x3
        eor     x16, x16, x14
        adcs    x16, x16, x4
        eor     x17, x17, x14
        adcs    x17, x17, x5
        eor     x19, x19, x14
        adcs    x19, x19, x6
        eor     x20, x20, x14
        adcs    x20, x20, x7
        eor     x1, x1, x14
        adcs    x1, x1, x8
        adcs    x9, x14, x2
        adcs    x10, x14, xzr
        adcs    x11, x14, xzr
        adc     x12, x14, xzr
        adds    x19, x19, x3
        adcs    x20, x20, x4
        adcs    x1, x1, x5
        adcs    x9, x9, x6
        adcs    x10, x10, x7
        adcs    x11, x11, x8
        adc     x12, x12, x2
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        adds    x9, x9, x15
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        adc     x12, x12, xzr
        add     x22, x12, #1
        lsl     x21, x22, #32
        subs    x0, x22, x21
        sbc     x21, x21, xzr
        adds    x19, x19, x0
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adcs    x9, x9, xzr
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        csetm   x22, lo
        mov     x23, #4294967295
        and     x23, x23, x22
        adds    x19, x19, x23
        eor     x23, x23, x22
        adcs    x20, x20, x23
        mov     x23, #-2
        and     x23, x23, x22
        adcs    x1, x1, x23
        adcs    x9, x9, x22
        adcs    x10, x10, x22
        adc     x11, x11, x22
        stp     x19, x20, [sp, #144]
        stp     x1, x9, [sp, #160]
        stp     x10, x11, [sp, #176]
        ldp     x3, x4, [sp, #240]
        ldp     x5, x6, [sp, #256]
        ldp     x7, x8, [sp, #272]
        ldp     x9, x10, [x26, #96]
        ldp     x11, x12, [x26, #112]
        ldp     x13, x14, [x26, #128]
        mul     x15, x3, x9
        mul     x21, x4, x10
        mul     x22, x5, x11
        umulh   x23, x3, x9
        umulh   x0, x4, x10
        umulh   x1, x5, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x3, x4
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x3, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x4, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        stp     x19, x20, [sp, #240]
        stp     x1, x15, [sp, #256]
        stp     x16, x17, [sp, #272]
        mul     x15, x6, x12
        mul     x21, x7, x13
        mul     x22, x8, x14
        umulh   x23, x6, x12
        umulh   x0, x7, x13
        umulh   x1, x8, x14
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x13, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x13
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        subs    x6, x6, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x5
        ngc     x3, xzr
        cmn     x3, #1
        eor     x6, x6, x3
        adcs    x6, x6, xzr
        eor     x7, x7, x3
        adcs    x7, x7, xzr
        eor     x8, x8, x3
        adc     x8, x8, xzr
        subs    x9, x9, x12
        sbcs    x10, x10, x13
        sbcs    x11, x11, x14
        ngc     x14, xzr
        cmn     x14, #1
        eor     x9, x9, x14
        adcs    x9, x9, xzr
        eor     x10, x10, x14
        adcs    x10, x10, xzr
        eor     x11, x11, x14
        adc     x11, x11, xzr
        eor     x14, x3, x14
        ldp     x21, x22, [sp, #240]
        adds    x15, x15, x21
        adcs    x16, x16, x22
        ldp     x21, x22, [sp, #256]
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        ldp     x21, x22, [sp, #272]
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adc     x2, xzr, xzr
        stp     x15, x16, [sp, #240]
        stp     x17, x19, [sp, #256]
        stp     x20, x1, [sp, #272]
        mul     x15, x6, x9
        mul     x21, x7, x10
        mul     x22, x8, x11
        umulh   x23, x6, x9
        umulh   x0, x7, x10
        umulh   x1, x8, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        ldp     x3, x4, [sp, #240]
        ldp     x5, x6, [sp, #256]
        ldp     x7, x8, [sp, #272]
        cmn     x14, #1
        eor     x15, x15, x14
        adcs    x15, x15, x3
        eor     x16, x16, x14
        adcs    x16, x16, x4
        eor     x17, x17, x14
        adcs    x17, x17, x5
        eor     x19, x19, x14
        adcs    x19, x19, x6
        eor     x20, x20, x14
        adcs    x20, x20, x7
        eor     x1, x1, x14
        adcs    x1, x1, x8
        adcs    x9, x14, x2
        adcs    x10, x14, xzr
        adcs    x11, x14, xzr
        adc     x12, x14, xzr
        adds    x19, x19, x3
        adcs    x20, x20, x4
        adcs    x1, x1, x5
        adcs    x9, x9, x6
        adcs    x10, x10, x7
        adcs    x11, x11, x8
        adc     x12, x12, x2
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        adds    x9, x9, x15
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        adc     x12, x12, xzr
        add     x22, x12, #1
        lsl     x21, x22, #32
        subs    x0, x22, x21
        sbc     x21, x21, xzr
        adds    x19, x19, x0
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adcs    x9, x9, xzr
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        csetm   x22, lo
        mov     x23, #4294967295
        and     x23, x23, x22
        adds    x19, x19, x23
        eor     x23, x23, x22
        adcs    x20, x20, x23
        mov     x23, #-2
        and     x23, x23, x22
        adcs    x1, x1, x23
        adcs    x9, x9, x22
        adcs    x10, x10, x22
        adc     x11, x11, x22
        stp     x19, x20, [sp, #240]
        stp     x1, x9, [sp, #256]
        stp     x10, x11, [sp, #272]
        ldp     x3, x4, [sp, #48]
        ldp     x5, x6, [sp, #64]
        ldp     x7, x8, [sp, #80]
        ldp     x9, x10, [sp, #192]
        ldp     x11, x12, [sp, #208]
        ldp     x13, x14, [sp, #224]
        mul     x15, x3, x9
        mul     x21, x4, x10
        mul     x22, x5, x11
        umulh   x23, x3, x9
        umulh   x0, x4, x10
        umulh   x1, x5, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x3, x4
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x3, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x4, x5
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        stp     x19, x20, [sp, #192]
        stp     x1, x15, [sp, #208]
        stp     x16, x17, [sp, #224]
        mul     x15, x6, x12
        mul     x21, x7, x13
        mul     x22, x8, x14
        umulh   x23, x6, x12
        umulh   x0, x7, x13
        umulh   x1, x8, x14
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x13, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x12
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x14, x13
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        subs    x6, x6, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x5
        ngc     x3, xzr
        cmn     x3, #1
        eor     x6, x6, x3
        adcs    x6, x6, xzr
        eor     x7, x7, x3
        adcs    x7, x7, xzr
        eor     x8, x8, x3
        adc     x8, x8, xzr
        subs    x9, x9, x12
        sbcs    x10, x10, x13
        sbcs    x11, x11, x14
        ngc     x14, xzr
        cmn     x14, #1
        eor     x9, x9, x14
        adcs    x9, x9, xzr
        eor     x10, x10, x14
        adcs    x10, x10, xzr
        eor     x11, x11, x14
        adc     x11, x11, xzr
        eor     x14, x3, x14
        ldp     x21, x22, [sp, #192]
        adds    x15, x15, x21
        adcs    x16, x16, x22
        ldp     x21, x22, [sp, #208]
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        ldp     x21, x22, [sp, #224]
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adc     x2, xzr, xzr
        stp     x15, x16, [sp, #192]
        stp     x17, x19, [sp, #208]
        stp     x20, x1, [sp, #224]
        mul     x15, x6, x9
        mul     x21, x7, x10
        mul     x22, x8, x11
        umulh   x23, x6, x9
        umulh   x0, x7, x10
        umulh   x1, x8, x11
        adds    x23, x23, x21
        adcs    x0, x0, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x0, x23
        adcs    x19, x1, x0
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x0
        adc     x1, x1, xzr
        subs    x0, x6, x7
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x6, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x0, x7, x8
        cneg    x0, x0, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x0, x22
        umulh   x22, x0, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        ldp     x3, x4, [sp, #192]
        ldp     x5, x6, [sp, #208]
        ldp     x7, x8, [sp, #224]
        cmn     x14, #1
        eor     x15, x15, x14
        adcs    x15, x15, x3
        eor     x16, x16, x14
        adcs    x16, x16, x4
        eor     x17, x17, x14
        adcs    x17, x17, x5
        eor     x19, x19, x14
        adcs    x19, x19, x6
        eor     x20, x20, x14
        adcs    x20, x20, x7
        eor     x1, x1, x14
        adcs    x1, x1, x8
        adcs    x9, x14, x2
        adcs    x10, x14, xzr
        adcs    x11, x14, xzr
        adc     x12, x14, xzr
        adds    x19, x19, x3
        adcs    x20, x20, x4
        adcs    x1, x1, x5
        adcs    x9, x9, x6
        adcs    x10, x10, x7
        adcs    x11, x11, x8
        adc     x12, x12, x2
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        adds    x9, x9, x15
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        adc     x12, x12, xzr
        add     x22, x12, #1
        lsl     x21, x22, #32
        subs    x0, x22, x21
        sbc     x21, x21, xzr
        adds    x19, x19, x0
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adcs    x9, x9, xzr
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        csetm   x22, lo
        mov     x23, #4294967295
        and     x23, x23, x22
        adds    x19, x19, x23
        eor     x23, x23, x22
        adcs    x20, x20, x23
        mov     x23, #-2
        and     x23, x23, x22
        adcs    x1, x1, x23
        adcs    x9, x9, x22
        adcs    x10, x10, x22
        adc     x11, x11, x22
        stp     x19, x20, [sp, #192]
        stp     x1, x9, [sp, #208]
        stp     x10, x11, [sp, #224]
        ldp     x5, x6, [sp, #192]
        ldp     x4, x3, [sp, #144]
        subs    x5, x5, x4
        sbcs    x6, x6, x3
        ldp     x7, x8, [sp, #208]
        ldp     x4, x3, [sp, #160]
        sbcs    x7, x7, x4
        sbcs    x8, x8, x3
        ldp     x9, x10, [sp, #224]
        ldp     x4, x3, [sp, #176]
        sbcs    x9, x9, x4
        sbcs    x10, x10, x3
        csetm   x3, lo
        mov     x4, #4294967295
        and     x4, x4, x3
        adds    x5, x5, x4
        eor     x4, x4, x3
        adcs    x6, x6, x4
        mov     x4, #-2
        and     x4, x4, x3
        adcs    x7, x7, x4
        adcs    x8, x8, x3
        adcs    x9, x9, x3
        adc     x10, x10, x3
        stp     x5, x6, [sp, #192]
        stp     x7, x8, [sp, #208]
        stp     x9, x10, [sp, #224]
        ldp     x0, x1, [x25, #96]
        ldp     x2, x3, [x25, #112]
        ldp     x4, x5, [x25, #128]
        orr     x20, x0, x1
        orr     x21, x2, x3
        orr     x22, x4, x5
        orr     x20, x20, x21
        orr     x20, x20, x22
        cmp     x20, xzr
        cset    x20, ne
        ldp     x6, x7, [x26, #96]
        ldp     x8, x9, [x26, #112]
        ldp     x10, x11, [x26, #128]
        orr     x21, x6, x7
        orr     x22, x8, x9
        orr     x23, x10, x11
        orr     x21, x21, x22
        orr     x21, x21, x23
        cmp     x21, xzr
        cset    x21, ne
        cmp     x21, x20
        ldp     x12, x13, [sp, #240]
        csel    x12, x0, x12, lo
        csel    x13, x1, x13, lo
        csel    x12, x6, x12, hi
        csel    x13, x7, x13, hi
        ldp     x14, x15, [sp, #256]
        csel    x14, x2, x14, lo
        csel    x15, x3, x15, lo
        csel    x14, x8, x14, hi
        csel    x15, x9, x15, hi
        ldp     x16, x17, [sp, #272]
        csel    x16, x4, x16, lo
        csel    x17, x5, x17, lo
        csel    x16, x10, x16, hi
        csel    x17, x11, x17, hi
        ldp     x20, x21, [x25]
        ldp     x0, x1, [sp]
        csel    x0, x20, x0, lo
        csel    x1, x21, x1, lo
        ldp     x20, x21, [x26]
        csel    x0, x20, x0, hi
        csel    x1, x21, x1, hi
        ldp     x20, x21, [x25, #16]
        ldp     x2, x3, [sp, #16]
        csel    x2, x20, x2, lo
        csel    x3, x21, x3, lo
        ldp     x20, x21, [x26, #16]
        csel    x2, x20, x2, hi
        csel    x3, x21, x3, hi
        ldp     x20, x21, [x25, #32]
        ldp     x4, x5, [sp, #32]
        csel    x4, x20, x4, lo
        csel    x5, x21, x5, lo
        ldp     x20, x21, [x26, #32]
        csel    x4, x20, x4, hi
        csel    x5, x21, x5, hi
        ldp     x20, x21, [x25, #48]
        ldp     x6, x7, [sp, #192]
        csel    x6, x20, x6, lo
        csel    x7, x21, x7, lo
        ldp     x20, x21, [x26, #48]
        csel    x6, x20, x6, hi
        csel    x7, x21, x7, hi
        ldp     x20, x21, [x25, #64]
        ldp     x8, x9, [sp, #208]
        csel    x8, x20, x8, lo
        csel    x9, x21, x9, lo
        ldp     x20, x21, [x26, #64]
        csel    x8, x20, x8, hi
        csel    x9, x21, x9, hi
        ldp     x20, x21, [x25, #80]
        ldp     x10, x11, [sp, #224]
        csel    x10, x20, x10, lo
        csel    x11, x21, x11, lo
        ldp     x20, x21, [x26, #80]
        csel    x10, x20, x10, hi
        csel    x11, x21, x11, hi
        stp     x0, x1, [x24]
        stp     x2, x3, [x24, #16]
        stp     x4, x5, [x24, #32]
        stp     x6, x7, [x24, #48]
        stp     x8, x9, [x24, #64]
        stp     x10, x11, [x24, #80]
        stp     x12, x13, [x24, #96]
        stp     x14, x15, [x24, #112]
        stp     x16, x17, [x24, #128]
        add     sp, sp, #336
        ldp     x25, x26, [sp], #16
        ldp     x23, x24, [sp], #16
        ldp     x21, x22, [sp], #16
        ldp     x19, x20, [sp], #16
        ret

p384_montjscalarmul_p384_montjdouble:
        sub     sp, sp, #400
        stp     x19, x20, [sp, #336]
        stp     x21, x22, [sp, #352]
        stp     x23, x24, [sp, #368]
        stp     x25, x26, [sp, #384]
        mov     x25, x0
        mov     x26, x1
        ldp     x2, x3, [x26, #96]
        ldp     x4, x5, [x26, #112]
        ldp     x6, x7, [x26, #128]
        mul     x14, x2, x3
        mul     x15, x2, x4
        mul     x16, x3, x4
        mul     x8, x2, x2
        mul     x10, x3, x3
        mul     x12, x4, x4
        umulh   x17, x2, x3
        adds    x15, x15, x17
        umulh   x17, x2, x4
        adcs    x16, x16, x17
        umulh   x17, x3, x4
        adcs    x17, x17, xzr
        umulh   x9, x2, x2
        umulh   x11, x3, x3
        umulh   x13, x4, x4
        adds    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adcs    x17, x17, x17
        adc     x13, x13, xzr
        adds    x9, x9, x14
        adcs    x10, x10, x15
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x13, xzr
        lsl     x16, x8, #32
        add     x8, x16, x8
        lsr     x16, x8, #32
        subs    x16, x16, x8
        sbc     x15, x8, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x8
        adc     x14, xzr, xzr
        subs    x9, x9, x16
        sbcs    x10, x10, x15
        sbcs    x11, x11, x14
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x16, x9, #32
        add     x9, x16, x9
        lsr     x16, x9, #32
        subs    x16, x16, x9
        sbc     x15, x9, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x9
        adc     x14, xzr, xzr
        subs    x10, x10, x16
        sbcs    x11, x11, x15
        sbcs    x12, x12, x14
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x16, x10, #32
        add     x10, x16, x10
        lsr     x16, x10, #32
        subs    x16, x16, x10
        sbc     x15, x10, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x10
        adc     x14, xzr, xzr
        subs    x11, x11, x16
        sbcs    x12, x12, x15
        sbcs    x13, x13, x14
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        stp     x11, x12, [sp]
        stp     x13, x8, [sp, #16]
        stp     x9, x10, [sp, #32]
        mul     x8, x2, x5
        mul     x14, x3, x6
        mul     x15, x4, x7
        umulh   x16, x2, x5
        umulh   x17, x3, x6
        umulh   x1, x4, x7
        adds    x16, x16, x14
        adcs    x17, x17, x15
        adc     x1, x1, xzr
        adds    x9, x16, x8
        adcs    x10, x17, x16
        adcs    x11, x1, x17
        adc     x12, x1, xzr
        adds    x10, x10, x8
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x1, xzr
        subs    x17, x2, x3
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x6, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x9, x9, x16
        adcs    x10, x10, x15
        adcs    x11, x11, x14
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x2, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x10, x10, x16
        adcs    x11, x11, x15
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x3, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x6
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x11, x11, x16
        adcs    x12, x12, x15
        adc     x13, x13, x14
        adds    x8, x8, x8
        adcs    x9, x9, x9
        adcs    x10, x10, x10
        adcs    x11, x11, x11
        adcs    x12, x12, x12
        adcs    x13, x13, x13
        adc     x17, xzr, xzr
        ldp     x2, x3, [sp]
        adds    x8, x8, x2
        adcs    x9, x9, x3
        ldp     x2, x3, [sp, #16]
        adcs    x10, x10, x2
        adcs    x11, x11, x3
        ldp     x2, x3, [sp, #32]
        adcs    x12, x12, x2
        adcs    x13, x13, x3
        adc     x17, x17, xzr
        lsl     x4, x8, #32
        add     x8, x4, x8
        lsr     x4, x8, #32
        subs    x4, x4, x8
        sbc     x3, x8, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x8
        adc     x2, xzr, xzr
        subs    x9, x9, x4
        sbcs    x10, x10, x3
        sbcs    x11, x11, x2
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x4, x9, #32
        add     x9, x4, x9
        lsr     x4, x9, #32
        subs    x4, x4, x9
        sbc     x3, x9, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x9
        adc     x2, xzr, xzr
        subs    x10, x10, x4
        sbcs    x11, x11, x3
        sbcs    x12, x12, x2
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x4, x10, #32
        add     x10, x4, x10
        lsr     x4, x10, #32
        subs    x4, x4, x10
        sbc     x3, x10, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x10
        adc     x2, xzr, xzr
        subs    x11, x11, x4
        sbcs    x12, x12, x3
        sbcs    x13, x13, x2
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        adds    x17, x17, x8
        adcs    x8, x9, xzr
        adcs    x9, x10, xzr
        adcs    x10, xzr, xzr
        mul     x1, x5, x5
        adds    x11, x11, x1
        mul     x14, x6, x6
        mul     x15, x7, x7
        umulh   x1, x5, x5
        adcs    x12, x12, x1
        umulh   x1, x6, x6
        adcs    x13, x13, x14
        adcs    x17, x17, x1
        umulh   x1, x7, x7
        adcs    x8, x8, x15
        adcs    x9, x9, x1
        adc     x10, x10, xzr
        mul     x1, x5, x6
        mul     x14, x5, x7
        mul     x15, x6, x7
        umulh   x16, x5, x6
        adds    x14, x14, x16
        umulh   x16, x5, x7
        adcs    x15, x15, x16
        umulh   x16, x6, x7
        adc     x16, x16, xzr
        adds    x1, x1, x1
        adcs    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adc     x5, xzr, xzr
        adds    x12, x12, x1
        adcs    x13, x13, x14
        adcs    x17, x17, x15
        adcs    x8, x8, x16
        adcs    x9, x9, x5
        adc     x10, x10, xzr
        mov     x1, #-4294967295
        mov     x14, #4294967295
        mov     x15, #1
        cmn     x11, x1
        adcs    xzr, x12, x14
        adcs    xzr, x13, x15
        adcs    xzr, x17, xzr
        adcs    xzr, x8, xzr
        adcs    xzr, x9, xzr
        adc     x10, x10, xzr
        neg     x10, x10
        and     x1, x1, x10
        adds    x11, x11, x1
        and     x14, x14, x10
        adcs    x12, x12, x14
        and     x15, x15, x10
        adcs    x13, x13, x15
        adcs    x17, x17, xzr
        adcs    x8, x8, xzr
        adc     x9, x9, xzr
        stp     x11, x12, [sp]
        stp     x13, x17, [sp, #16]
        stp     x8, x9, [sp, #32]
        ldp     x2, x3, [x26, #48]
        ldp     x4, x5, [x26, #64]
        ldp     x6, x7, [x26, #80]
        mul     x14, x2, x3
        mul     x15, x2, x4
        mul     x16, x3, x4
        mul     x8, x2, x2
        mul     x10, x3, x3
        mul     x12, x4, x4
        umulh   x17, x2, x3
        adds    x15, x15, x17
        umulh   x17, x2, x4
        adcs    x16, x16, x17
        umulh   x17, x3, x4
        adcs    x17, x17, xzr
        umulh   x9, x2, x2
        umulh   x11, x3, x3
        umulh   x13, x4, x4
        adds    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adcs    x17, x17, x17
        adc     x13, x13, xzr
        adds    x9, x9, x14
        adcs    x10, x10, x15
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x13, xzr
        lsl     x16, x8, #32
        add     x8, x16, x8
        lsr     x16, x8, #32
        subs    x16, x16, x8
        sbc     x15, x8, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x8
        adc     x14, xzr, xzr
        subs    x9, x9, x16
        sbcs    x10, x10, x15
        sbcs    x11, x11, x14
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x16, x9, #32
        add     x9, x16, x9
        lsr     x16, x9, #32
        subs    x16, x16, x9
        sbc     x15, x9, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x9
        adc     x14, xzr, xzr
        subs    x10, x10, x16
        sbcs    x11, x11, x15
        sbcs    x12, x12, x14
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x16, x10, #32
        add     x10, x16, x10
        lsr     x16, x10, #32
        subs    x16, x16, x10
        sbc     x15, x10, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x10
        adc     x14, xzr, xzr
        subs    x11, x11, x16
        sbcs    x12, x12, x15
        sbcs    x13, x13, x14
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        stp     x11, x12, [sp, #48]
        stp     x13, x8, [sp, #64]
        stp     x9, x10, [sp, #80]
        mul     x8, x2, x5
        mul     x14, x3, x6
        mul     x15, x4, x7
        umulh   x16, x2, x5
        umulh   x17, x3, x6
        umulh   x1, x4, x7
        adds    x16, x16, x14
        adcs    x17, x17, x15
        adc     x1, x1, xzr
        adds    x9, x16, x8
        adcs    x10, x17, x16
        adcs    x11, x1, x17
        adc     x12, x1, xzr
        adds    x10, x10, x8
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x1, xzr
        subs    x17, x2, x3
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x6, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x9, x9, x16
        adcs    x10, x10, x15
        adcs    x11, x11, x14
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x2, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x10, x10, x16
        adcs    x11, x11, x15
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x3, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x6
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x11, x11, x16
        adcs    x12, x12, x15
        adc     x13, x13, x14
        adds    x8, x8, x8
        adcs    x9, x9, x9
        adcs    x10, x10, x10
        adcs    x11, x11, x11
        adcs    x12, x12, x12
        adcs    x13, x13, x13
        adc     x17, xzr, xzr
        ldp     x2, x3, [sp, #48]
        adds    x8, x8, x2
        adcs    x9, x9, x3
        ldp     x2, x3, [sp, #64]
        adcs    x10, x10, x2
        adcs    x11, x11, x3
        ldp     x2, x3, [sp, #80]
        adcs    x12, x12, x2
        adcs    x13, x13, x3
        adc     x17, x17, xzr
        lsl     x4, x8, #32
        add     x8, x4, x8
        lsr     x4, x8, #32
        subs    x4, x4, x8
        sbc     x3, x8, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x8
        adc     x2, xzr, xzr
        subs    x9, x9, x4
        sbcs    x10, x10, x3
        sbcs    x11, x11, x2
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x4, x9, #32
        add     x9, x4, x9
        lsr     x4, x9, #32
        subs    x4, x4, x9
        sbc     x3, x9, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x9
        adc     x2, xzr, xzr
        subs    x10, x10, x4
        sbcs    x11, x11, x3
        sbcs    x12, x12, x2
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x4, x10, #32
        add     x10, x4, x10
        lsr     x4, x10, #32
        subs    x4, x4, x10
        sbc     x3, x10, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x10
        adc     x2, xzr, xzr
        subs    x11, x11, x4
        sbcs    x12, x12, x3
        sbcs    x13, x13, x2
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        adds    x17, x17, x8
        adcs    x8, x9, xzr
        adcs    x9, x10, xzr
        adcs    x10, xzr, xzr
        mul     x1, x5, x5
        adds    x11, x11, x1
        mul     x14, x6, x6
        mul     x15, x7, x7
        umulh   x1, x5, x5
        adcs    x12, x12, x1
        umulh   x1, x6, x6
        adcs    x13, x13, x14
        adcs    x17, x17, x1
        umulh   x1, x7, x7
        adcs    x8, x8, x15
        adcs    x9, x9, x1
        adc     x10, x10, xzr
        mul     x1, x5, x6
        mul     x14, x5, x7
        mul     x15, x6, x7
        umulh   x16, x5, x6
        adds    x14, x14, x16
        umulh   x16, x5, x7
        adcs    x15, x15, x16
        umulh   x16, x6, x7
        adc     x16, x16, xzr
        adds    x1, x1, x1
        adcs    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adc     x5, xzr, xzr
        adds    x12, x12, x1
        adcs    x13, x13, x14
        adcs    x17, x17, x15
        adcs    x8, x8, x16
        adcs    x9, x9, x5
        adc     x10, x10, xzr
        mov     x1, #-4294967295
        mov     x14, #4294967295
        mov     x15, #1
        cmn     x11, x1
        adcs    xzr, x12, x14
        adcs    xzr, x13, x15
        adcs    xzr, x17, xzr
        adcs    xzr, x8, xzr
        adcs    xzr, x9, xzr
        adc     x10, x10, xzr
        neg     x10, x10
        and     x1, x1, x10
        adds    x11, x11, x1
        and     x14, x14, x10
        adcs    x12, x12, x14
        and     x15, x15, x10
        adcs    x13, x13, x15
        adcs    x17, x17, xzr
        adcs    x8, x8, xzr
        adc     x9, x9, xzr
        stp     x11, x12, [sp, #48]
        stp     x13, x17, [sp, #64]
        stp     x8, x9, [sp, #80]
        ldp     x5, x6, [x26]
        ldp     x4, x3, [sp]
        adds    x5, x5, x4
        adcs    x6, x6, x3
        ldp     x7, x8, [x26, #16]
        ldp     x4, x3, [sp, #16]
        adcs    x7, x7, x4
        adcs    x8, x8, x3
        ldp     x9, x10, [x26, #32]
        ldp     x4, x3, [sp, #32]
        adcs    x9, x9, x4
        adcs    x10, x10, x3
        csetm   x3, hs
        mov     x4, #4294967295
        and     x4, x4, x3
        subs    x5, x5, x4
        eor     x4, x4, x3
        sbcs    x6, x6, x4
        mov     x4, #-2
        and     x4, x4, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x3
        sbcs    x9, x9, x3
        sbc     x10, x10, x3
        stp     x5, x6, [sp, #240]
        stp     x7, x8, [sp, #256]
        stp     x9, x10, [sp, #272]
        ldp     x5, x6, [x26]
        ldp     x4, x3, [sp]
        subs    x5, x5, x4
        sbcs    x6, x6, x3
        ldp     x7, x8, [x26, #16]
        ldp     x4, x3, [sp, #16]
        sbcs    x7, x7, x4
        sbcs    x8, x8, x3
        ldp     x9, x10, [x26, #32]
        ldp     x4, x3, [sp, #32]
        sbcs    x9, x9, x4
        sbcs    x10, x10, x3
        csetm   x3, lo
        mov     x4, #4294967295
        and     x4, x4, x3
        adds    x5, x5, x4
        eor     x4, x4, x3
        adcs    x6, x6, x4
        mov     x4, #-2
        and     x4, x4, x3
        adcs    x7, x7, x4
        adcs    x8, x8, x3
        adcs    x9, x9, x3
        adc     x10, x10, x3
        stp     x5, x6, [sp, #192]
        stp     x7, x8, [sp, #208]
        stp     x9, x10, [sp, #224]
        ldp     x3, x4, [sp, #240]
        ldp     x5, x6, [sp, #256]
        ldp     x7, x8, [sp, #272]
        ldp     x9, x10, [sp, #192]
        ldp     x11, x12, [sp, #208]
        ldp     x13, x14, [sp, #224]
        mul     x15, x3, x9
        mul     x21, x4, x10
        mul     x22, x5, x11
        umulh   x23, x3, x9
        umulh   x24, x4, x10
        umulh   x1, x5, x11
        adds    x23, x23, x21
        adcs    x24, x24, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x24, x23
        adcs    x19, x1, x24
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x24
        adc     x1, x1, xzr
        subs    x24, x3, x4
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x3, x5
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x4, x5
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        stp     x19, x20, [sp, #96]
        stp     x1, x15, [sp, #112]
        stp     x16, x17, [sp, #128]
        mul     x15, x6, x12
        mul     x21, x7, x13
        mul     x22, x8, x14
        umulh   x23, x6, x12
        umulh   x24, x7, x13
        umulh   x1, x8, x14
        adds    x23, x23, x21
        adcs    x24, x24, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x24, x23
        adcs    x19, x1, x24
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x24
        adc     x1, x1, xzr
        subs    x24, x6, x7
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x13, x12
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x6, x8
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x14, x12
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x7, x8
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x14, x13
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        subs    x6, x6, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x5
        ngc     x3, xzr
        cmn     x3, #1
        eor     x6, x6, x3
        adcs    x6, x6, xzr
        eor     x7, x7, x3
        adcs    x7, x7, xzr
        eor     x8, x8, x3
        adc     x8, x8, xzr
        subs    x9, x9, x12
        sbcs    x10, x10, x13
        sbcs    x11, x11, x14
        ngc     x14, xzr
        cmn     x14, #1
        eor     x9, x9, x14
        adcs    x9, x9, xzr
        eor     x10, x10, x14
        adcs    x10, x10, xzr
        eor     x11, x11, x14
        adc     x11, x11, xzr
        eor     x14, x3, x14
        ldp     x21, x22, [sp, #96]
        adds    x15, x15, x21
        adcs    x16, x16, x22
        ldp     x21, x22, [sp, #112]
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        ldp     x21, x22, [sp, #128]
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adc     x2, xzr, xzr
        stp     x15, x16, [sp, #96]
        stp     x17, x19, [sp, #112]
        stp     x20, x1, [sp, #128]
        mul     x15, x6, x9
        mul     x21, x7, x10
        mul     x22, x8, x11
        umulh   x23, x6, x9
        umulh   x24, x7, x10
        umulh   x1, x8, x11
        adds    x23, x23, x21
        adcs    x24, x24, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x24, x23
        adcs    x19, x1, x24
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x24
        adc     x1, x1, xzr
        subs    x24, x6, x7
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x6, x8
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x7, x8
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        ldp     x3, x4, [sp, #96]
        ldp     x5, x6, [sp, #112]
        ldp     x7, x8, [sp, #128]
        cmn     x14, #1
        eor     x15, x15, x14
        adcs    x15, x15, x3
        eor     x16, x16, x14
        adcs    x16, x16, x4
        eor     x17, x17, x14
        adcs    x17, x17, x5
        eor     x19, x19, x14
        adcs    x19, x19, x6
        eor     x20, x20, x14
        adcs    x20, x20, x7
        eor     x1, x1, x14
        adcs    x1, x1, x8
        adcs    x9, x14, x2
        adcs    x10, x14, xzr
        adcs    x11, x14, xzr
        adc     x12, x14, xzr
        adds    x19, x19, x3
        adcs    x20, x20, x4
        adcs    x1, x1, x5
        adcs    x9, x9, x6
        adcs    x10, x10, x7
        adcs    x11, x11, x8
        adc     x12, x12, x2
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        adds    x9, x9, x15
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        adc     x12, x12, xzr
        add     x22, x12, #1
        lsl     x21, x22, #32
        subs    x24, x22, x21
        sbc     x21, x21, xzr
        adds    x19, x19, x24
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adcs    x9, x9, xzr
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        csetm   x22, lo
        mov     x23, #4294967295
        and     x23, x23, x22
        adds    x19, x19, x23
        eor     x23, x23, x22
        adcs    x20, x20, x23
        mov     x23, #-2
        and     x23, x23, x22
        adcs    x1, x1, x23
        adcs    x9, x9, x22
        adcs    x10, x10, x22
        adc     x11, x11, x22
        stp     x19, x20, [sp, #96]
        stp     x1, x9, [sp, #112]
        stp     x10, x11, [sp, #128]
        ldp     x5, x6, [x26, #48]
        ldp     x4, x3, [x26, #96]
        adds    x5, x5, x4
        adcs    x6, x6, x3
        ldp     x7, x8, [x26, #64]
        ldp     x4, x3, [x26, #112]
        adcs    x7, x7, x4
        adcs    x8, x8, x3
        ldp     x9, x10, [x26, #80]
        ldp     x4, x3, [x26, #128]
        adcs    x9, x9, x4
        adcs    x10, x10, x3
        adc     x3, xzr, xzr
        mov     x4, #4294967295
        cmp     x5, x4
        mov     x4, #-4294967296
        sbcs    xzr, x6, x4
        mov     x4, #-2
        sbcs    xzr, x7, x4
        adcs    xzr, x8, xzr
        adcs    xzr, x9, xzr
        adcs    xzr, x10, xzr
        adcs    x3, x3, xzr
        csetm   x3, ne
        mov     x4, #4294967295
        and     x4, x4, x3
        subs    x5, x5, x4
        eor     x4, x4, x3
        sbcs    x6, x6, x4
        mov     x4, #-2
        and     x4, x4, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x3
        sbcs    x9, x9, x3
        sbc     x10, x10, x3
        stp     x5, x6, [sp, #240]
        stp     x7, x8, [sp, #256]
        stp     x9, x10, [sp, #272]
        ldp     x2, x3, [sp, #96]
        ldp     x4, x5, [sp, #112]
        ldp     x6, x7, [sp, #128]
        mul     x14, x2, x3
        mul     x15, x2, x4
        mul     x16, x3, x4
        mul     x8, x2, x2
        mul     x10, x3, x3
        mul     x12, x4, x4
        umulh   x17, x2, x3
        adds    x15, x15, x17
        umulh   x17, x2, x4
        adcs    x16, x16, x17
        umulh   x17, x3, x4
        adcs    x17, x17, xzr
        umulh   x9, x2, x2
        umulh   x11, x3, x3
        umulh   x13, x4, x4
        adds    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adcs    x17, x17, x17
        adc     x13, x13, xzr
        adds    x9, x9, x14
        adcs    x10, x10, x15
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x13, xzr
        lsl     x16, x8, #32
        add     x8, x16, x8
        lsr     x16, x8, #32
        subs    x16, x16, x8
        sbc     x15, x8, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x8
        adc     x14, xzr, xzr
        subs    x9, x9, x16
        sbcs    x10, x10, x15
        sbcs    x11, x11, x14
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x16, x9, #32
        add     x9, x16, x9
        lsr     x16, x9, #32
        subs    x16, x16, x9
        sbc     x15, x9, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x9
        adc     x14, xzr, xzr
        subs    x10, x10, x16
        sbcs    x11, x11, x15
        sbcs    x12, x12, x14
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x16, x10, #32
        add     x10, x16, x10
        lsr     x16, x10, #32
        subs    x16, x16, x10
        sbc     x15, x10, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x10
        adc     x14, xzr, xzr
        subs    x11, x11, x16
        sbcs    x12, x12, x15
        sbcs    x13, x13, x14
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        stp     x11, x12, [sp, #288]
        stp     x13, x8, [sp, #304]
        stp     x9, x10, [sp, #320]
        mul     x8, x2, x5
        mul     x14, x3, x6
        mul     x15, x4, x7
        umulh   x16, x2, x5
        umulh   x17, x3, x6
        umulh   x1, x4, x7
        adds    x16, x16, x14
        adcs    x17, x17, x15
        adc     x1, x1, xzr
        adds    x9, x16, x8
        adcs    x10, x17, x16
        adcs    x11, x1, x17
        adc     x12, x1, xzr
        adds    x10, x10, x8
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x1, xzr
        subs    x17, x2, x3
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x6, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x9, x9, x16
        adcs    x10, x10, x15
        adcs    x11, x11, x14
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x2, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x10, x10, x16
        adcs    x11, x11, x15
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x3, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x6
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x11, x11, x16
        adcs    x12, x12, x15
        adc     x13, x13, x14
        adds    x8, x8, x8
        adcs    x9, x9, x9
        adcs    x10, x10, x10
        adcs    x11, x11, x11
        adcs    x12, x12, x12
        adcs    x13, x13, x13
        adc     x17, xzr, xzr
        ldp     x2, x3, [sp, #288]
        adds    x8, x8, x2
        adcs    x9, x9, x3
        ldp     x2, x3, [sp, #304]
        adcs    x10, x10, x2
        adcs    x11, x11, x3
        ldp     x2, x3, [sp, #320]
        adcs    x12, x12, x2
        adcs    x13, x13, x3
        adc     x17, x17, xzr
        lsl     x4, x8, #32
        add     x8, x4, x8
        lsr     x4, x8, #32
        subs    x4, x4, x8
        sbc     x3, x8, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x8
        adc     x2, xzr, xzr
        subs    x9, x9, x4
        sbcs    x10, x10, x3
        sbcs    x11, x11, x2
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x4, x9, #32
        add     x9, x4, x9
        lsr     x4, x9, #32
        subs    x4, x4, x9
        sbc     x3, x9, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x9
        adc     x2, xzr, xzr
        subs    x10, x10, x4
        sbcs    x11, x11, x3
        sbcs    x12, x12, x2
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x4, x10, #32
        add     x10, x4, x10
        lsr     x4, x10, #32
        subs    x4, x4, x10
        sbc     x3, x10, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x10
        adc     x2, xzr, xzr
        subs    x11, x11, x4
        sbcs    x12, x12, x3
        sbcs    x13, x13, x2
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        adds    x17, x17, x8
        adcs    x8, x9, xzr
        adcs    x9, x10, xzr
        adcs    x10, xzr, xzr
        mul     x1, x5, x5
        adds    x11, x11, x1
        mul     x14, x6, x6
        mul     x15, x7, x7
        umulh   x1, x5, x5
        adcs    x12, x12, x1
        umulh   x1, x6, x6
        adcs    x13, x13, x14
        adcs    x17, x17, x1
        umulh   x1, x7, x7
        adcs    x8, x8, x15
        adcs    x9, x9, x1
        adc     x10, x10, xzr
        mul     x1, x5, x6
        mul     x14, x5, x7
        mul     x15, x6, x7
        umulh   x16, x5, x6
        adds    x14, x14, x16
        umulh   x16, x5, x7
        adcs    x15, x15, x16
        umulh   x16, x6, x7
        adc     x16, x16, xzr
        adds    x1, x1, x1
        adcs    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adc     x5, xzr, xzr
        adds    x12, x12, x1
        adcs    x13, x13, x14
        adcs    x17, x17, x15
        adcs    x8, x8, x16
        adcs    x9, x9, x5
        adc     x10, x10, xzr
        mov     x1, #-4294967295
        mov     x14, #4294967295
        mov     x15, #1
        cmn     x11, x1
        adcs    xzr, x12, x14
        adcs    xzr, x13, x15
        adcs    xzr, x17, xzr
        adcs    xzr, x8, xzr
        adcs    xzr, x9, xzr
        adc     x10, x10, xzr
        neg     x10, x10
        and     x1, x1, x10
        adds    x11, x11, x1
        and     x14, x14, x10
        adcs    x12, x12, x14
        and     x15, x15, x10
        adcs    x13, x13, x15
        adcs    x17, x17, xzr
        adcs    x8, x8, xzr
        adc     x9, x9, xzr
        stp     x11, x12, [sp, #288]
        stp     x13, x17, [sp, #304]
        stp     x8, x9, [sp, #320]
        ldp     x3, x4, [x26]
        ldp     x5, x6, [x26, #16]
        ldp     x7, x8, [x26, #32]
        ldp     x9, x10, [sp, #48]
        ldp     x11, x12, [sp, #64]
        ldp     x13, x14, [sp, #80]
        mul     x15, x3, x9
        mul     x21, x4, x10
        mul     x22, x5, x11
        umulh   x23, x3, x9
        umulh   x24, x4, x10
        umulh   x1, x5, x11
        adds    x23, x23, x21
        adcs    x24, x24, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x24, x23
        adcs    x19, x1, x24
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x24
        adc     x1, x1, xzr
        subs    x24, x3, x4
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x3, x5
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x4, x5
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        stp     x19, x20, [sp, #144]
        stp     x1, x15, [sp, #160]
        stp     x16, x17, [sp, #176]
        mul     x15, x6, x12
        mul     x21, x7, x13
        mul     x22, x8, x14
        umulh   x23, x6, x12
        umulh   x24, x7, x13
        umulh   x1, x8, x14
        adds    x23, x23, x21
        adcs    x24, x24, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x24, x23
        adcs    x19, x1, x24
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x24
        adc     x1, x1, xzr
        subs    x24, x6, x7
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x13, x12
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x6, x8
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x14, x12
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x7, x8
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x14, x13
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        subs    x6, x6, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x5
        ngc     x3, xzr
        cmn     x3, #1
        eor     x6, x6, x3
        adcs    x6, x6, xzr
        eor     x7, x7, x3
        adcs    x7, x7, xzr
        eor     x8, x8, x3
        adc     x8, x8, xzr
        subs    x9, x9, x12
        sbcs    x10, x10, x13
        sbcs    x11, x11, x14
        ngc     x14, xzr
        cmn     x14, #1
        eor     x9, x9, x14
        adcs    x9, x9, xzr
        eor     x10, x10, x14
        adcs    x10, x10, xzr
        eor     x11, x11, x14
        adc     x11, x11, xzr
        eor     x14, x3, x14
        ldp     x21, x22, [sp, #144]
        adds    x15, x15, x21
        adcs    x16, x16, x22
        ldp     x21, x22, [sp, #160]
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        ldp     x21, x22, [sp, #176]
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adc     x2, xzr, xzr
        stp     x15, x16, [sp, #144]
        stp     x17, x19, [sp, #160]
        stp     x20, x1, [sp, #176]
        mul     x15, x6, x9
        mul     x21, x7, x10
        mul     x22, x8, x11
        umulh   x23, x6, x9
        umulh   x24, x7, x10
        umulh   x1, x8, x11
        adds    x23, x23, x21
        adcs    x24, x24, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x24, x23
        adcs    x19, x1, x24
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x24
        adc     x1, x1, xzr
        subs    x24, x6, x7
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x6, x8
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x7, x8
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        ldp     x3, x4, [sp, #144]
        ldp     x5, x6, [sp, #160]
        ldp     x7, x8, [sp, #176]
        cmn     x14, #1
        eor     x15, x15, x14
        adcs    x15, x15, x3
        eor     x16, x16, x14
        adcs    x16, x16, x4
        eor     x17, x17, x14
        adcs    x17, x17, x5
        eor     x19, x19, x14
        adcs    x19, x19, x6
        eor     x20, x20, x14
        adcs    x20, x20, x7
        eor     x1, x1, x14
        adcs    x1, x1, x8
        adcs    x9, x14, x2
        adcs    x10, x14, xzr
        adcs    x11, x14, xzr
        adc     x12, x14, xzr
        adds    x19, x19, x3
        adcs    x20, x20, x4
        adcs    x1, x1, x5
        adcs    x9, x9, x6
        adcs    x10, x10, x7
        adcs    x11, x11, x8
        adc     x12, x12, x2
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        adds    x9, x9, x15
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        adc     x12, x12, xzr
        add     x22, x12, #1
        lsl     x21, x22, #32
        subs    x24, x22, x21
        sbc     x21, x21, xzr
        adds    x19, x19, x24
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adcs    x9, x9, xzr
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        csetm   x22, lo
        mov     x23, #4294967295
        and     x23, x23, x22
        adds    x19, x19, x23
        eor     x23, x23, x22
        adcs    x20, x20, x23
        mov     x23, #-2
        and     x23, x23, x22
        adcs    x1, x1, x23
        adcs    x9, x9, x22
        adcs    x10, x10, x22
        adc     x11, x11, x22
        stp     x19, x20, [sp, #144]
        stp     x1, x9, [sp, #160]
        stp     x10, x11, [sp, #176]
        ldp     x2, x3, [sp, #240]
        ldp     x4, x5, [sp, #256]
        ldp     x6, x7, [sp, #272]
        mul     x14, x2, x3
        mul     x15, x2, x4
        mul     x16, x3, x4
        mul     x8, x2, x2
        mul     x10, x3, x3
        mul     x12, x4, x4
        umulh   x17, x2, x3
        adds    x15, x15, x17
        umulh   x17, x2, x4
        adcs    x16, x16, x17
        umulh   x17, x3, x4
        adcs    x17, x17, xzr
        umulh   x9, x2, x2
        umulh   x11, x3, x3
        umulh   x13, x4, x4
        adds    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adcs    x17, x17, x17
        adc     x13, x13, xzr
        adds    x9, x9, x14
        adcs    x10, x10, x15
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x13, xzr
        lsl     x16, x8, #32
        add     x8, x16, x8
        lsr     x16, x8, #32
        subs    x16, x16, x8
        sbc     x15, x8, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x8
        adc     x14, xzr, xzr
        subs    x9, x9, x16
        sbcs    x10, x10, x15
        sbcs    x11, x11, x14
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x16, x9, #32
        add     x9, x16, x9
        lsr     x16, x9, #32
        subs    x16, x16, x9
        sbc     x15, x9, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x9
        adc     x14, xzr, xzr
        subs    x10, x10, x16
        sbcs    x11, x11, x15
        sbcs    x12, x12, x14
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x16, x10, #32
        add     x10, x16, x10
        lsr     x16, x10, #32
        subs    x16, x16, x10
        sbc     x15, x10, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x10
        adc     x14, xzr, xzr
        subs    x11, x11, x16
        sbcs    x12, x12, x15
        sbcs    x13, x13, x14
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        stp     x11, x12, [sp, #192]
        stp     x13, x8, [sp, #208]
        stp     x9, x10, [sp, #224]
        mul     x8, x2, x5
        mul     x14, x3, x6
        mul     x15, x4, x7
        umulh   x16, x2, x5
        umulh   x17, x3, x6
        umulh   x1, x4, x7
        adds    x16, x16, x14
        adcs    x17, x17, x15
        adc     x1, x1, xzr
        adds    x9, x16, x8
        adcs    x10, x17, x16
        adcs    x11, x1, x17
        adc     x12, x1, xzr
        adds    x10, x10, x8
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x1, xzr
        subs    x17, x2, x3
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x6, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x9, x9, x16
        adcs    x10, x10, x15
        adcs    x11, x11, x14
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x2, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x10, x10, x16
        adcs    x11, x11, x15
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x3, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x6
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x11, x11, x16
        adcs    x12, x12, x15
        adc     x13, x13, x14
        adds    x8, x8, x8
        adcs    x9, x9, x9
        adcs    x10, x10, x10
        adcs    x11, x11, x11
        adcs    x12, x12, x12
        adcs    x13, x13, x13
        adc     x17, xzr, xzr
        ldp     x2, x3, [sp, #192]
        adds    x8, x8, x2
        adcs    x9, x9, x3
        ldp     x2, x3, [sp, #208]
        adcs    x10, x10, x2
        adcs    x11, x11, x3
        ldp     x2, x3, [sp, #224]
        adcs    x12, x12, x2
        adcs    x13, x13, x3
        adc     x17, x17, xzr
        lsl     x4, x8, #32
        add     x8, x4, x8
        lsr     x4, x8, #32
        subs    x4, x4, x8
        sbc     x3, x8, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x8
        adc     x2, xzr, xzr
        subs    x9, x9, x4
        sbcs    x10, x10, x3
        sbcs    x11, x11, x2
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x4, x9, #32
        add     x9, x4, x9
        lsr     x4, x9, #32
        subs    x4, x4, x9
        sbc     x3, x9, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x9
        adc     x2, xzr, xzr
        subs    x10, x10, x4
        sbcs    x11, x11, x3
        sbcs    x12, x12, x2
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x4, x10, #32
        add     x10, x4, x10
        lsr     x4, x10, #32
        subs    x4, x4, x10
        sbc     x3, x10, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x10
        adc     x2, xzr, xzr
        subs    x11, x11, x4
        sbcs    x12, x12, x3
        sbcs    x13, x13, x2
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        adds    x17, x17, x8
        adcs    x8, x9, xzr
        adcs    x9, x10, xzr
        adcs    x10, xzr, xzr
        mul     x1, x5, x5
        adds    x11, x11, x1
        mul     x14, x6, x6
        mul     x15, x7, x7
        umulh   x1, x5, x5
        adcs    x12, x12, x1
        umulh   x1, x6, x6
        adcs    x13, x13, x14
        adcs    x17, x17, x1
        umulh   x1, x7, x7
        adcs    x8, x8, x15
        adcs    x9, x9, x1
        adc     x10, x10, xzr
        mul     x1, x5, x6
        mul     x14, x5, x7
        mul     x15, x6, x7
        umulh   x16, x5, x6
        adds    x14, x14, x16
        umulh   x16, x5, x7
        adcs    x15, x15, x16
        umulh   x16, x6, x7
        adc     x16, x16, xzr
        adds    x1, x1, x1
        adcs    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adc     x5, xzr, xzr
        adds    x12, x12, x1
        adcs    x13, x13, x14
        adcs    x17, x17, x15
        adcs    x8, x8, x16
        adcs    x9, x9, x5
        adc     x10, x10, xzr
        mov     x1, #-4294967295
        mov     x14, #4294967295
        mov     x15, #1
        cmn     x11, x1
        adcs    xzr, x12, x14
        adcs    xzr, x13, x15
        adcs    xzr, x17, xzr
        adcs    xzr, x8, xzr
        adcs    xzr, x9, xzr
        adc     x10, x10, xzr
        neg     x10, x10
        and     x1, x1, x10
        adds    x11, x11, x1
        and     x14, x14, x10
        adcs    x12, x12, x14
        and     x15, x15, x10
        adcs    x13, x13, x15
        adcs    x17, x17, xzr
        adcs    x8, x8, xzr
        adc     x9, x9, xzr
        stp     x11, x12, [sp, #192]
        stp     x13, x17, [sp, #208]
        stp     x8, x9, [sp, #224]
        ldp     x0, x1, [sp, #288]
        mov     x6, #4294967295
        subs    x6, x6, x0
        mov     x7, #-4294967296
        sbcs    x7, x7, x1
        ldp     x0, x1, [sp, #304]
        mov     x8, #-2
        sbcs    x8, x8, x0
        mov     x13, #-1
        sbcs    x9, x13, x1
        ldp     x0, x1, [sp, #320]
        sbcs    x10, x13, x0
        sbc     x11, x13, x1
        mov     x12, #9
        mul     x0, x12, x6
        mul     x1, x12, x7
        mul     x2, x12, x8
        mul     x3, x12, x9
        mul     x4, x12, x10
        mul     x5, x12, x11
        umulh   x6, x12, x6
        umulh   x7, x12, x7
        umulh   x8, x12, x8
        umulh   x9, x12, x9
        umulh   x10, x12, x10
        umulh   x12, x12, x11
        adds    x1, x1, x6
        adcs    x2, x2, x7
        adcs    x3, x3, x8
        adcs    x4, x4, x9
        adcs    x5, x5, x10
        mov     x6, #1
        adc     x6, x12, x6
        ldp     x8, x9, [sp, #144]
        ldp     x10, x11, [sp, #160]
        ldp     x12, x13, [sp, #176]
        mov     x14, #12
        mul     x15, x14, x8
        umulh   x8, x14, x8
        adds    x0, x0, x15
        mul     x15, x14, x9
        umulh   x9, x14, x9
        adcs    x1, x1, x15
        mul     x15, x14, x10
        umulh   x10, x14, x10
        adcs    x2, x2, x15
        mul     x15, x14, x11
        umulh   x11, x14, x11
        adcs    x3, x3, x15
        mul     x15, x14, x12
        umulh   x12, x14, x12
        adcs    x4, x4, x15
        mul     x15, x14, x13
        umulh   x13, x14, x13
        adcs    x5, x5, x15
        adc     x6, x6, xzr
        adds    x1, x1, x8
        adcs    x2, x2, x9
        adcs    x3, x3, x10
        adcs    x4, x4, x11
        adcs    x5, x5, x12
        adcs    x6, x6, x13
        lsl     x7, x6, #32
        subs    x8, x6, x7
        sbc     x7, x7, xzr
        adds    x0, x0, x8
        adcs    x1, x1, x7
        adcs    x2, x2, x6
        adcs    x3, x3, xzr
        adcs    x4, x4, xzr
        adcs    x5, x5, xzr
        csetm   x6, lo
        mov     x7, #4294967295
        and     x7, x7, x6
        adds    x0, x0, x7
        eor     x7, x7, x6
        adcs    x1, x1, x7
        mov     x7, #-2
        and     x7, x7, x6
        adcs    x2, x2, x7
        adcs    x3, x3, x6
        adcs    x4, x4, x6
        adc     x5, x5, x6
        stp     x0, x1, [sp, #288]
        stp     x2, x3, [sp, #304]
        stp     x4, x5, [sp, #320]
        ldp     x5, x6, [sp, #192]
        ldp     x4, x3, [sp]
        subs    x5, x5, x4
        sbcs    x6, x6, x3
        ldp     x7, x8, [sp, #208]
        ldp     x4, x3, [sp, #16]
        sbcs    x7, x7, x4
        sbcs    x8, x8, x3
        ldp     x9, x10, [sp, #224]
        ldp     x4, x3, [sp, #32]
        sbcs    x9, x9, x4
        sbcs    x10, x10, x3
        csetm   x3, lo
        mov     x4, #4294967295
        and     x4, x4, x3
        adds    x5, x5, x4
        eor     x4, x4, x3
        adcs    x6, x6, x4
        mov     x4, #-2
        and     x4, x4, x3
        adcs    x7, x7, x4
        adcs    x8, x8, x3
        adcs    x9, x9, x3
        adc     x10, x10, x3
        stp     x5, x6, [sp, #240]
        stp     x7, x8, [sp, #256]
        stp     x9, x10, [sp, #272]
        ldp     x2, x3, [sp, #48]
        ldp     x4, x5, [sp, #64]
        ldp     x6, x7, [sp, #80]
        mul     x14, x2, x3
        mul     x15, x2, x4
        mul     x16, x3, x4
        mul     x8, x2, x2
        mul     x10, x3, x3
        mul     x12, x4, x4
        umulh   x17, x2, x3
        adds    x15, x15, x17
        umulh   x17, x2, x4
        adcs    x16, x16, x17
        umulh   x17, x3, x4
        adcs    x17, x17, xzr
        umulh   x9, x2, x2
        umulh   x11, x3, x3
        umulh   x13, x4, x4
        adds    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adcs    x17, x17, x17
        adc     x13, x13, xzr
        adds    x9, x9, x14
        adcs    x10, x10, x15
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x13, xzr
        lsl     x16, x8, #32
        add     x8, x16, x8
        lsr     x16, x8, #32
        subs    x16, x16, x8
        sbc     x15, x8, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x8
        adc     x14, xzr, xzr
        subs    x9, x9, x16
        sbcs    x10, x10, x15
        sbcs    x11, x11, x14
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x16, x9, #32
        add     x9, x16, x9
        lsr     x16, x9, #32
        subs    x16, x16, x9
        sbc     x15, x9, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x9
        adc     x14, xzr, xzr
        subs    x10, x10, x16
        sbcs    x11, x11, x15
        sbcs    x12, x12, x14
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x16, x10, #32
        add     x10, x16, x10
        lsr     x16, x10, #32
        subs    x16, x16, x10
        sbc     x15, x10, xzr
        extr    x16, x15, x16, #32
        lsr     x15, x15, #32
        adds    x15, x15, x10
        adc     x14, xzr, xzr
        subs    x11, x11, x16
        sbcs    x12, x12, x15
        sbcs    x13, x13, x14
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        stp     x11, x12, [sp, #192]
        stp     x13, x8, [sp, #208]
        stp     x9, x10, [sp, #224]
        mul     x8, x2, x5
        mul     x14, x3, x6
        mul     x15, x4, x7
        umulh   x16, x2, x5
        umulh   x17, x3, x6
        umulh   x1, x4, x7
        adds    x16, x16, x14
        adcs    x17, x17, x15
        adc     x1, x1, xzr
        adds    x9, x16, x8
        adcs    x10, x17, x16
        adcs    x11, x1, x17
        adc     x12, x1, xzr
        adds    x10, x10, x8
        adcs    x11, x11, x16
        adcs    x12, x12, x17
        adc     x13, x1, xzr
        subs    x17, x2, x3
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x6, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x9, x9, x16
        adcs    x10, x10, x15
        adcs    x11, x11, x14
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x2, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x5
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x10, x10, x16
        adcs    x11, x11, x15
        adcs    x12, x12, x14
        adc     x13, x13, x14
        subs    x17, x3, x4
        cneg    x17, x17, lo
        csetm   x14, lo
        subs    x15, x7, x6
        cneg    x15, x15, lo
        mul     x16, x17, x15
        umulh   x15, x17, x15
        cinv    x14, x14, lo
        eor     x16, x16, x14
        eor     x15, x15, x14
        cmn     x14, #1
        adcs    x11, x11, x16
        adcs    x12, x12, x15
        adc     x13, x13, x14
        adds    x8, x8, x8
        adcs    x9, x9, x9
        adcs    x10, x10, x10
        adcs    x11, x11, x11
        adcs    x12, x12, x12
        adcs    x13, x13, x13
        adc     x17, xzr, xzr
        ldp     x2, x3, [sp, #192]
        adds    x8, x8, x2
        adcs    x9, x9, x3
        ldp     x2, x3, [sp, #208]
        adcs    x10, x10, x2
        adcs    x11, x11, x3
        ldp     x2, x3, [sp, #224]
        adcs    x12, x12, x2
        adcs    x13, x13, x3
        adc     x17, x17, xzr
        lsl     x4, x8, #32
        add     x8, x4, x8
        lsr     x4, x8, #32
        subs    x4, x4, x8
        sbc     x3, x8, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x8
        adc     x2, xzr, xzr
        subs    x9, x9, x4
        sbcs    x10, x10, x3
        sbcs    x11, x11, x2
        sbcs    x12, x12, xzr
        sbcs    x13, x13, xzr
        sbc     x8, x8, xzr
        lsl     x4, x9, #32
        add     x9, x4, x9
        lsr     x4, x9, #32
        subs    x4, x4, x9
        sbc     x3, x9, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x9
        adc     x2, xzr, xzr
        subs    x10, x10, x4
        sbcs    x11, x11, x3
        sbcs    x12, x12, x2
        sbcs    x13, x13, xzr
        sbcs    x8, x8, xzr
        sbc     x9, x9, xzr
        lsl     x4, x10, #32
        add     x10, x4, x10
        lsr     x4, x10, #32
        subs    x4, x4, x10
        sbc     x3, x10, xzr
        extr    x4, x3, x4, #32
        lsr     x3, x3, #32
        adds    x3, x3, x10
        adc     x2, xzr, xzr
        subs    x11, x11, x4
        sbcs    x12, x12, x3
        sbcs    x13, x13, x2
        sbcs    x8, x8, xzr
        sbcs    x9, x9, xzr
        sbc     x10, x10, xzr
        adds    x17, x17, x8
        adcs    x8, x9, xzr
        adcs    x9, x10, xzr
        adcs    x10, xzr, xzr
        mul     x1, x5, x5
        adds    x11, x11, x1
        mul     x14, x6, x6
        mul     x15, x7, x7
        umulh   x1, x5, x5
        adcs    x12, x12, x1
        umulh   x1, x6, x6
        adcs    x13, x13, x14
        adcs    x17, x17, x1
        umulh   x1, x7, x7
        adcs    x8, x8, x15
        adcs    x9, x9, x1
        adc     x10, x10, xzr
        mul     x1, x5, x6
        mul     x14, x5, x7
        mul     x15, x6, x7
        umulh   x16, x5, x6
        adds    x14, x14, x16
        umulh   x16, x5, x7
        adcs    x15, x15, x16
        umulh   x16, x6, x7
        adc     x16, x16, xzr
        adds    x1, x1, x1
        adcs    x14, x14, x14
        adcs    x15, x15, x15
        adcs    x16, x16, x16
        adc     x5, xzr, xzr
        adds    x12, x12, x1
        adcs    x13, x13, x14
        adcs    x17, x17, x15
        adcs    x8, x8, x16
        adcs    x9, x9, x5
        adc     x10, x10, xzr
        mov     x1, #-4294967295
        mov     x14, #4294967295
        mov     x15, #1
        cmn     x11, x1
        adcs    xzr, x12, x14
        adcs    xzr, x13, x15
        adcs    xzr, x17, xzr
        adcs    xzr, x8, xzr
        adcs    xzr, x9, xzr
        adc     x10, x10, xzr
        neg     x10, x10
        and     x1, x1, x10
        adds    x11, x11, x1
        and     x14, x14, x10
        adcs    x12, x12, x14
        and     x15, x15, x10
        adcs    x13, x13, x15
        adcs    x17, x17, xzr
        adcs    x8, x8, xzr
        adc     x9, x9, xzr
        stp     x11, x12, [sp, #192]
        stp     x13, x17, [sp, #208]
        stp     x8, x9, [sp, #224]
        ldp     x5, x6, [sp, #240]
        ldp     x4, x3, [sp, #48]
        subs    x5, x5, x4
        sbcs    x6, x6, x3
        ldp     x7, x8, [sp, #256]
        ldp     x4, x3, [sp, #64]
        sbcs    x7, x7, x4
        sbcs    x8, x8, x3
        ldp     x9, x10, [sp, #272]
        ldp     x4, x3, [sp, #80]
        sbcs    x9, x9, x4
        sbcs    x10, x10, x3
        csetm   x3, lo
        mov     x4, #4294967295
        and     x4, x4, x3
        adds    x5, x5, x4
        eor     x4, x4, x3
        adcs    x6, x6, x4
        mov     x4, #-2
        and     x4, x4, x3
        adcs    x7, x7, x4
        adcs    x8, x8, x3
        adcs    x9, x9, x3
        adc     x10, x10, x3
        stp     x5, x6, [x25, #96]
        stp     x7, x8, [x25, #112]
        stp     x9, x10, [x25, #128]
        ldp     x3, x4, [sp, #288]
        ldp     x5, x6, [sp, #304]
        ldp     x7, x8, [sp, #320]
        ldp     x9, x10, [sp, #96]
        ldp     x11, x12, [sp, #112]
        ldp     x13, x14, [sp, #128]
        mul     x15, x3, x9
        mul     x21, x4, x10
        mul     x22, x5, x11
        umulh   x23, x3, x9
        umulh   x24, x4, x10
        umulh   x1, x5, x11
        adds    x23, x23, x21
        adcs    x24, x24, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x24, x23
        adcs    x19, x1, x24
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x24
        adc     x1, x1, xzr
        subs    x24, x3, x4
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x3, x5
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x4, x5
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        stp     x19, x20, [sp, #240]
        stp     x1, x15, [sp, #256]
        stp     x16, x17, [sp, #272]
        mul     x15, x6, x12
        mul     x21, x7, x13
        mul     x22, x8, x14
        umulh   x23, x6, x12
        umulh   x24, x7, x13
        umulh   x1, x8, x14
        adds    x23, x23, x21
        adcs    x24, x24, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x24, x23
        adcs    x19, x1, x24
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x24
        adc     x1, x1, xzr
        subs    x24, x6, x7
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x13, x12
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x6, x8
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x14, x12
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x7, x8
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x14, x13
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        subs    x6, x6, x3
        sbcs    x7, x7, x4
        sbcs    x8, x8, x5
        ngc     x3, xzr
        cmn     x3, #1
        eor     x6, x6, x3
        adcs    x6, x6, xzr
        eor     x7, x7, x3
        adcs    x7, x7, xzr
        eor     x8, x8, x3
        adc     x8, x8, xzr
        subs    x9, x9, x12
        sbcs    x10, x10, x13
        sbcs    x11, x11, x14
        ngc     x14, xzr
        cmn     x14, #1
        eor     x9, x9, x14
        adcs    x9, x9, xzr
        eor     x10, x10, x14
        adcs    x10, x10, xzr
        eor     x11, x11, x14
        adc     x11, x11, xzr
        eor     x14, x3, x14
        ldp     x21, x22, [sp, #240]
        adds    x15, x15, x21
        adcs    x16, x16, x22
        ldp     x21, x22, [sp, #256]
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        ldp     x21, x22, [sp, #272]
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adc     x2, xzr, xzr
        stp     x15, x16, [sp, #240]
        stp     x17, x19, [sp, #256]
        stp     x20, x1, [sp, #272]
        mul     x15, x6, x9
        mul     x21, x7, x10
        mul     x22, x8, x11
        umulh   x23, x6, x9
        umulh   x24, x7, x10
        umulh   x1, x8, x11
        adds    x23, x23, x21
        adcs    x24, x24, x22
        adc     x1, x1, xzr
        adds    x16, x23, x15
        adcs    x17, x24, x23
        adcs    x19, x1, x24
        adc     x20, x1, xzr
        adds    x17, x17, x15
        adcs    x19, x19, x23
        adcs    x20, x20, x24
        adc     x1, x1, xzr
        subs    x24, x6, x7
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x10, x9
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x16, x16, x21
        adcs    x17, x17, x22
        adcs    x19, x19, x23
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x6, x8
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x11, x9
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x17, x17, x21
        adcs    x19, x19, x22
        adcs    x20, x20, x23
        adc     x1, x1, x23
        subs    x24, x7, x8
        cneg    x24, x24, lo
        csetm   x23, lo
        subs    x22, x11, x10
        cneg    x22, x22, lo
        mul     x21, x24, x22
        umulh   x22, x24, x22
        cinv    x23, x23, lo
        eor     x21, x21, x23
        eor     x22, x22, x23
        cmn     x23, #1
        adcs    x19, x19, x21
        adcs    x20, x20, x22
        adc     x1, x1, x23
        ldp     x3, x4, [sp, #240]
        ldp     x5, x6, [sp, #256]
        ldp     x7, x8, [sp, #272]
        cmn     x14, #1
        eor     x15, x15, x14
        adcs    x15, x15, x3
        eor     x16, x16, x14
        adcs    x16, x16, x4
        eor     x17, x17, x14
        adcs    x17, x17, x5
        eor     x19, x19, x14
        adcs    x19, x19, x6
        eor     x20, x20, x14
        adcs    x20, x20, x7
        eor     x1, x1, x14
        adcs    x1, x1, x8
        adcs    x9, x14, x2
        adcs    x10, x14, xzr
        adcs    x11, x14, xzr
        adc     x12, x14, xzr
        adds    x19, x19, x3
        adcs    x20, x20, x4
        adcs    x1, x1, x5
        adcs    x9, x9, x6
        adcs    x10, x10, x7
        adcs    x11, x11, x8
        adc     x12, x12, x2
        lsl     x23, x15, #32
        add     x15, x23, x15
        lsr     x23, x15, #32
        subs    x23, x23, x15
        sbc     x22, x15, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x15
        adc     x21, xzr, xzr
        subs    x16, x16, x23
        sbcs    x17, x17, x22
        sbcs    x19, x19, x21
        sbcs    x20, x20, xzr
        sbcs    x1, x1, xzr
        sbc     x15, x15, xzr
        lsl     x23, x16, #32
        add     x16, x23, x16
        lsr     x23, x16, #32
        subs    x23, x23, x16
        sbc     x22, x16, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x16
        adc     x21, xzr, xzr
        subs    x17, x17, x23
        sbcs    x19, x19, x22
        sbcs    x20, x20, x21
        sbcs    x1, x1, xzr
        sbcs    x15, x15, xzr
        sbc     x16, x16, xzr
        lsl     x23, x17, #32
        add     x17, x23, x17
        lsr     x23, x17, #32
        subs    x23, x23, x17
        sbc     x22, x17, xzr
        extr    x23, x22, x23, #32
        lsr     x22, x22, #32
        adds    x22, x22, x17
        adc     x21, xzr, xzr
        subs    x19, x19, x23
        sbcs    x20, x20, x22
        sbcs    x1, x1, x21
        sbcs    x15, x15, xzr
        sbcs    x16, x16, xzr
        sbc     x17, x17, xzr
        adds    x9, x9, x15
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        adc     x12, x12, xzr
        add     x22, x12, #1
        lsl     x21, x22, #32
        subs    x24, x22, x21
        sbc     x21, x21, xzr
        adds    x19, x19, x24
        adcs    x20, x20, x21
        adcs    x1, x1, x22
        adcs    x9, x9, xzr
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        csetm   x22, lo
        mov     x23, #4294967295
        and     x23, x23, x22
        adds    x19, x19, x23
        eor     x23, x23, x22
        adcs    x20, x20, x23
        mov     x23, #-2
        and     x23, x23, x22
        adcs    x1, x1, x23
        adcs    x9, x9, x22
        adcs    x10, x10, x22
        adc     x11, x11, x22
        stp     x19, x20, [sp, #240]
        stp     x1, x9, [sp, #256]
        stp     x10, x11, [sp, #272]
        ldp     x1, x2, [sp, #144]
        ldp     x3, x4, [sp, #160]
        ldp     x5, x6, [sp, #176]
        lsl     x0, x1, #2
        ldp     x7, x8, [sp, #288]
        subs    x0, x0, x7
        extr    x1, x2, x1, #62
        sbcs    x1, x1, x8
        ldp     x7, x8, [sp, #304]
        extr    x2, x3, x2, #62
        sbcs    x2, x2, x7
        extr    x3, x4, x3, #62
        sbcs    x3, x3, x8
        extr    x4, x5, x4, #62
        ldp     x7, x8, [sp, #320]
        sbcs    x4, x4, x7
        extr    x5, x6, x5, #62
        sbcs    x5, x5, x8
        lsr     x6, x6, #62
        adc     x6, x6, xzr
        lsl     x7, x6, #32
        subs    x8, x6, x7
        sbc     x7, x7, xzr
        adds    x0, x0, x8
        adcs    x1, x1, x7
        adcs    x2, x2, x6
        adcs    x3, x3, xzr
        adcs    x4, x4, xzr
        adcs    x5, x5, xzr
        csetm   x8, lo
        mov     x9, #4294967295
        and     x9, x9, x8
        adds    x0, x0, x9
        eor     x9, x9, x8
        adcs    x1, x1, x9
        mov     x9, #-2
        and     x9, x9, x8
        adcs    x2, x2, x9
        adcs    x3, x3, x8
        adcs    x4, x4, x8
        adc     x5, x5, x8
        stp     x0, x1, [x25]
        stp     x2, x3, [x25, #16]
        stp     x4, x5, [x25, #32]
        ldp     x0, x1, [sp, #192]
        mov     x6, #4294967295
        subs    x6, x6, x0
        mov     x7, #-4294967296
        sbcs    x7, x7, x1
        ldp     x0, x1, [sp, #208]
        mov     x8, #-2
        sbcs    x8, x8, x0
        mov     x13, #-1
        sbcs    x9, x13, x1
        ldp     x0, x1, [sp, #224]
        sbcs    x10, x13, x0
        sbc     x11, x13, x1
        lsl     x0, x6, #3
        extr    x1, x7, x6, #61
        extr    x2, x8, x7, #61
        extr    x3, x9, x8, #61
        extr    x4, x10, x9, #61
        extr    x5, x11, x10, #61
        lsr     x6, x11, #61
        add     x6, x6, #1
        ldp     x8, x9, [sp, #240]
        ldp     x10, x11, [sp, #256]
        ldp     x12, x13, [sp, #272]
        mov     x14, #3
        mul     x15, x14, x8
        umulh   x8, x14, x8
        adds    x0, x0, x15
        mul     x15, x14, x9
        umulh   x9, x14, x9
        adcs    x1, x1, x15
        mul     x15, x14, x10
        umulh   x10, x14, x10
        adcs    x2, x2, x15
        mul     x15, x14, x11
        umulh   x11, x14, x11
        adcs    x3, x3, x15
        mul     x15, x14, x12
        umulh   x12, x14, x12
        adcs    x4, x4, x15
        mul     x15, x14, x13
        umulh   x13, x14, x13
        adcs    x5, x5, x15
        adc     x6, x6, xzr
        adds    x1, x1, x8
        adcs    x2, x2, x9
        adcs    x3, x3, x10
        adcs    x4, x4, x11
        adcs    x5, x5, x12
        adcs    x6, x6, x13
        lsl     x7, x6, #32
        subs    x8, x6, x7
        sbc     x7, x7, xzr
        adds    x0, x0, x8
        adcs    x1, x1, x7
        adcs    x2, x2, x6
        adcs    x3, x3, xzr
        adcs    x4, x4, xzr
        adcs    x5, x5, xzr
        csetm   x6, lo
        mov     x7, #4294967295
        and     x7, x7, x6
        adds    x0, x0, x7
        eor     x7, x7, x6
        adcs    x1, x1, x7
        mov     x7, #-2
        and     x7, x7, x6
        adcs    x2, x2, x7
        adcs    x3, x3, x6
        adcs    x4, x4, x6
        adc     x5, x5, x6
        stp     x0, x1, [x25, #48]
        stp     x2, x3, [x25, #64]
        stp     x4, x5, [x25, #80]
        ldp     x19, x20, [sp, #336]
        ldp     x21, x22, [sp, #352]
        ldp     x23, x24, [sp, #368]
        ldp     x25, x26, [sp, #384]
        add     sp, sp, #400
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
