// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Compare bignums, x >= y
// Inputs x[m], y[n]; output function return
//
//    extern uint64_t bignum_ge(uint64_t m, const uint64_t *x, uint64_t n,
//                              const uint64_t *y);
//
// Standard ARM ABI: X0 = m, X1 = x, X2 = n, X3 = y, returns X0
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_ge)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_ge)
        .text
        .balign 4

#define m x0
#define x x1
#define n x2
#define y x3
#define i x4
#define a x5
#define d x6


S2N_BN_SYMBOL(bignum_ge):

// Zero the main index counter for both branches

        mov     i, xzr

// Speculatively form m := m - n and do case split

        subs    m, m, n
        bcc     bignum_ge_ylonger

// The case where x is longer or of the same size (m >= n)
// Note that CF=1 initially by the fact that we reach this point

        cbz     n, bignum_ge_xtest
bignum_ge_xmainloop:
        ldr     a, [x, i, lsl #3]
        ldr     d, [y, i, lsl #3]
        sbcs    xzr, a, d
        add     i, i, #1
        sub     n, n, #1
        cbnz    n, bignum_ge_xmainloop
bignum_ge_xtest:
        cbz     m, bignum_ge_xskip
bignum_ge_xtoploop:
        ldr     a, [x, i, lsl #3]
        sbcs    xzr, a, xzr
        add     i, i, #1
        sub     m, m, #1
        cbnz    m, bignum_ge_xtoploop
bignum_ge_xskip:
        cset    x0, cs
        ret

// The case where y is longer (n > m)
// The first "adds" also makes sure CF=1 initially in this branch

bignum_ge_ylonger:
        adds    m, m, n
        cbz     m, bignum_ge_ytoploop
        sub     n, n, m
bignum_ge_ymainloop:
        ldr     a, [x, i, lsl #3]
        ldr     d, [y, i, lsl #3]
        sbcs    xzr, a, d
        add     i, i, #1
        sub     m, m, #1
        cbnz    m, bignum_ge_ymainloop
bignum_ge_ytoploop:
        ldr     a, [y, i, lsl #3]
        sbcs    xzr, xzr, a
        add     i, i, #1
        sub     n, n, #1
        cbnz    n, bignum_ge_ytoploop

        cset    x0, cs
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
