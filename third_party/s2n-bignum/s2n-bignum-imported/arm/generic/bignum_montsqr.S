// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery square, z := (x^2 / 2^{64k}) mod m
// Inputs x[k], m[k]; output z[k]
//
//    extern void bignum_montsqr
//      (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *m);
//
// Does z := (x^2 / 2^{64k}) mod m, assuming x^2 <= 2^{64k} * m, which is
// guaranteed in particular if x < m initially (the "intended" case).
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = x, X3 = m
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montsqr)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montsqr)
        .text
        .balign 4

#define k x0
#define z x1
#define x x2
#define m x3

// Negated modular inverse
#define w x4
// Top carry for k'th position
#define c0 x5
// Additional top carry for (k+1)'th position
#define c1 x6
// Outer loop counter
#define i x7
// Home for i'th digit or Montgomery multiplier
#define d x8
// Inner loop counter
#define j x9

#define h x10
#define e x11
#define l x12
#define a x13

// This is just a short-term temporary used in zero-test subtraction.
// It's aliased to the same register as "a" which is always safe here.

#define t x13

// Some more intuitive names for temp regs in initial word-level negmodinv.
// These just use c0 and c1 again, which aren't initialized early on.

#define one x5
#define e1 x5
#define e2 x6
#define e4 x5
#define e8 x6


S2N_BN_SYMBOL(bignum_montsqr):

// If k = 0 the whole operation is trivial

        cbz     k, bignum_montsqr_end

// Compute word-level negated modular inverse w for m == m[0].
// This is essentially the same as word_negmodinv.

        ldr     a, [m]
        lsl     w, a, #2
        sub     w, a, w
        eor     w, w, #2
        mov     one, #1
        madd    e1, a, w, one
        mul     e2, e1, e1
        madd    w, e1, w, w
        mul     e4, e2, e2
        madd    w, e2, w, w
        mul     e8, e4, e4
        madd    w, e4, w, w
        madd    w, e8, w, w

// Initialize the output c0::z to zero so we can then consistently add rows.
// It would be a bit more efficient to special-case the zeroth row, but
// this keeps the code slightly simpler.

        mov     i, xzr
bignum_montsqr_zoop:
        str     xzr, [z, i, lsl #3]
        add     i, i, #1
        cmp     i, k
        bcc     bignum_montsqr_zoop
        mov     c0, xzr

// Outer loop pulling down digits d=x[i], multiplying by x and reducing

        mov     i, xzr
bignum_montsqr_outerloop:

// Multiply-add loop where we always have CF + previous high part h to add in
// Note that in general we do need yet one more carry in this phase and hence
// initialize c1 with the top carry.

        ldr     d, [x, i, lsl #3]
        mov     j, xzr
        adds    h, xzr, xzr
bignum_montsqr_maddloop:
        ldr     a, [x, j, lsl #3]
        ldr     e, [z, j, lsl #3]
        mul     l, d, a
        adcs    e, e, h
        umulh   h, d, a
        adc     h, h, xzr
        adds    e, e, l
        str     e, [z, j, lsl #3]
        add     j, j, #1
        sub     t, j, k
        cbnz    t, bignum_montsqr_maddloop
        adcs    c0, c0, h
        adc     c1, xzr, xzr

// Montgomery reduction loop, similar but offsetting writebacks

        ldr     e, [z]
        mul     d, e, w
        ldr     a, [m]
        mul     l, d, a
        umulh   h, d, a
        adds    e, e, l         // Will be zero but want the carry
        mov     j, #1
        sub     t, k, #1
        cbz     t, bignum_montsqr_montend
bignum_montsqr_montloop:
        ldr     a, [m, j, lsl #3]
        ldr     e, [z, j, lsl #3]
        mul     l, d, a
        adcs    e, e, h
        umulh   h, d, a
        adc     h, h, xzr
        adds    e, e, l
        sub     l, j, #1
        str     e, [z, l, lsl #3]
        add     j, j, #1
        sub     t, j, k
        cbnz    t, bignum_montsqr_montloop
bignum_montsqr_montend:
        adcs    h, c0, h
        adc     c0, c1, xzr
        sub     l, j, #1
        str     h, [z, l, lsl #3]

// End of outer loop

        add     i, i, #1
        cmp     i, k
        bcc     bignum_montsqr_outerloop

// Now do a comparison of (c0::z) with (0::m) to set a final correction mask
// indicating that (c0::z) >= m and so we need to subtract m.

        subs    j, xzr, xzr
bignum_montsqr_cmploop:
        ldr     a, [z, j, lsl #3]
        ldr     e, [m, j, lsl #3]
        sbcs    xzr, a, e
        add     j, j, #1
        sub     t, j, k
        cbnz    t, bignum_montsqr_cmploop

        sbcs    xzr, c0, xzr
        csetm   c0, cs

// Now do a masked subtraction of m for the final reduced result.

        subs    j, xzr, xzr
bignum_montsqr_corrloop:
        ldr     a, [z, j, lsl #3]
        ldr     e, [m, j, lsl #3]
        and     e, e, c0
        sbcs    a, a, e
        str     a, [z, j, lsl #3]
        add     j, j, #1
        sub     t, j, k
        cbnz    t, bignum_montsqr_corrloop

bignum_montsqr_end:
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
