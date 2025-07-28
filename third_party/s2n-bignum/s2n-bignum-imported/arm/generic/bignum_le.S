// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Compare bignums, x <= y
// Inputs x[m], y[n]; output function return
//
//    extern uint64_t bignum_le
//     (uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);
//
// Standard ARM ABI: X0 = m, X1 = x, X2 = n, X3 = y, returns X0
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_le)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_le)
        .text
        .balign 4

#define m x0
#define x x1
#define n x2
#define y x3
#define i x4
#define a x5
#define d x6


S2N_BN_SYMBOL(bignum_le):

// Zero the main index counter for both branches

        mov     i, xzr

// Speculatively form n := n - m and do case split

        subs    n, n, m
        bcc     bignum_le_ylonger

// The case where y is longer or of the same size (n >= m)
// Note that CF=1 initially by the fact that we reach this point

        cbz     m, bignum_le_xtest
bignum_le_xmainloop:
        ldr     a, [y, i, lsl #3]
        ldr     d, [x, i, lsl #3]
        sbcs    xzr, a, d
        add     i, i, #1
        sub     m, m, #1
        cbnz    m, bignum_le_xmainloop
bignum_le_xtest:
        cbz     n, bignum_le_xskip
bignum_le_xtoploop:
        ldr     a, [y, i, lsl #3]
        sbcs    xzr, a, xzr
        add     i, i, #1
        sub     n, n, #1
        cbnz    n, bignum_le_xtoploop
bignum_le_xskip:
        cset    x0, cs
        ret

// The case where x is longer (m > n)
// The first "adds" also makes sure CF=1 initially in this branch

bignum_le_ylonger:
        adds    n, n, m
        cbz     n, bignum_le_ytoploop
        sub     m, m, n
bignum_le_ymainloop:
        ldr     a, [y, i, lsl #3]
        ldr     d, [x, i, lsl #3]
        sbcs    xzr, a, d
        add     i, i, #1
        sub     n, n, #1
        cbnz    n, bignum_le_ymainloop
bignum_le_ytoploop:
        ldr     a, [x, i, lsl #3]
        sbcs    xzr, xzr, a
        add     i, i, #1
        sub     m, m, #1
        cbnz    m, bignum_le_ytoploop

        cset    x0, cs
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
