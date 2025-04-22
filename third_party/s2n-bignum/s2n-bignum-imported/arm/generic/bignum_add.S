// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Add, z := x + y
// Inputs x[m], y[n]; outputs function return (carry-out) and z[p]
//
//    extern uint64_t bignum_add
//     (uint64_t p, uint64_t *z,
//      uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);
//
// Does the z := x + y operation, truncating modulo p words in general and
// returning a top carry (0 or 1) in the p'th place, only adding the input
// words below p (as well as m and n respectively) to get the sum and carry.
//
// Standard ARM ABI: X0 = p, X1 = z, X2 = m, X3 = x, X4 = n, X5 = y, returns X0
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_add)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_add)
        .text
        .balign 4

#define p x0
#define z x1
#define m x2
#define x x3
#define n x4
#define y x5
#define i x6
#define a x7
#define d x8


S2N_BN_SYMBOL(bignum_add):

// First clamp the two input sizes m := min(p,m) and n := min(p,n) since
// we'll never need words past the p'th. Can now assume m <= p and n <= p.
// Then compare the modified m and n and branch accordingly

        cmp     m, p
        csel    m, p, m, cs
        cmp     n, p
        csel    n, p, n, cs
        cmp     m, n
        bcc     bignum_add_ylonger

// The case where x is longer or of the same size (p >= m >= n)

        sub     p, p, m
        sub     m, m, n
        ands    i, xzr, xzr
        cbz     n, bignum_add_xmainskip
bignum_add_xmainloop:
        ldr     a, [x, i, lsl #3]
        ldr     d, [y, i, lsl #3]
        adcs    a, a, d
        str     a, [z, i, lsl #3]
        add     i, i, #1
        sub     n, n, #1
        cbnz    n, bignum_add_xmainloop
bignum_add_xmainskip:
        cbz     m, bignum_add_xtopskip
bignum_add_xtoploop:
        ldr     a, [x, i, lsl #3]
        adcs    a, a, xzr
        str     a, [z, i, lsl #3]
        add     i, i, #1
        sub     m, m, #1
        cbnz    m, bignum_add_xtoploop
bignum_add_xtopskip:
        cbnz    p, bignum_add_tails
        cset    x0, cs
        ret

// The case where y is longer (p >= n > m)

bignum_add_ylonger:
        sub     p, p, n
        sub     n, n, m
        ands    i, xzr, xzr
        cbz     m, bignum_add_ytoploop
bignum_add_ymainloop:
        ldr     a, [x, i, lsl #3]
        ldr     d, [y, i, lsl #3]
        adcs    a, a, d
        str     a, [z, i, lsl #3]
        add     i, i, #1
        sub     m, m, #1
        cbnz    m, bignum_add_ymainloop
bignum_add_ytoploop:
        ldr     a, [y, i, lsl #3]
        adcs    a, xzr, a
        str     a, [z, i, lsl #3]
        add     i, i, #1
        sub     n, n, #1
        cbnz    n, bignum_add_ytoploop
bignum_add_ytopskip:
        cbnz    p, bignum_add_tails
        cset    x0, cs
        ret

// Adding a non-trivial tail, when p > max(m,n)

bignum_add_tails:
        cset    a, cs
        str     a, [z, i, lsl #3]
        b       bignum_add_tail
bignum_add_tailloop:
        str     xzr, [z, i, lsl #3]
bignum_add_tail:
        add     i, i, #1
        sub     p, p, #1
        cbnz    p, bignum_add_tailloop
        mov     x0, xzr
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
