// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Compare bignums, x < y
// Inputs x[m], y[n]; output function return
//
//    extern uint64_t bignum_lt
//     (uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);
//
// Standard ARM ABI: X0 = m, X1 = x, X2 = n, X3 = y, returns X0
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_lt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_lt)
        .text
        .balign 4

#define m x0
#define x x1
#define n x2
#define y x3
#define i x4
#define a x5
#define d x6


S2N_BN_SYMBOL(bignum_lt):

// Zero the main index counter for both branches

        mov     i, xzr

// Speculatively form m := m - n and do case split

        subs    m, m, n
        bcc     ylonger

// The case where x is longer or of the same size (m >= n)
// Note that CF=1 initially by the fact that we reach this point

        cbz     n, xtest
xmainloop:
        ldr     a, [x, i, lsl #3]
        ldr     d, [y, i, lsl #3]
        sbcs    xzr, a, d
        add     i, i, #1
        sub     n, n, #1
        cbnz    n, xmainloop
xtest:
        cbz     m, xskip
xtoploop:
        ldr     a, [x, i, lsl #3]
        sbcs    xzr, a, xzr
        add     i, i, #1
        sub     m, m, #1
        cbnz    m, xtoploop
xskip:
        cset    x0, cc
        ret

// The case where y is longer (n > m)
// The first "adds" also makes sure CF=1 initially in this branch

ylonger:
        adds    m, m, n
        cbz     m, ytoploop
        sub     n, n, m
ymainloop:
        ldr     a, [x, i, lsl #3]
        ldr     d, [y, i, lsl #3]
        sbcs    xzr, a, d
        add     i, i, #1
        sub     m, m, #1
        cbnz    m, ymainloop
ytoploop:
        ldr     a, [y, i, lsl #3]
        sbcs    xzr, xzr, a
        add     i, i, #1
        sub     n, n, #1
        cbnz    n, ytoploop

        cset    x0, cc
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
