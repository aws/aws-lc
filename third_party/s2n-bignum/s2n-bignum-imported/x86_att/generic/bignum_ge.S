// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Compare bignums, x >= y
// Inputs x[m], y[n]; output function return
//
//    extern uint64_t bignum_ge
//     (uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);
//
// Standard x86-64 ABI: RDI = m, RSI = x, RDX = n, RCX = y, returns RAX
// Microsoft x64 ABI:   RCX = m, RDX = x, R8 = n, R9 = y, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_ge)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_ge)
        .text

#define m %rdi
#define x %rsi
#define n %rdx
#define y %rcx
#define i %r8
#define a %rax

#define ashort %eax



S2N_BN_SYMBOL(bignum_ge):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
        movq    %r9, %rcx
#endif

// Zero the main index counter for both branches

        xorq    i, i

// Speculatively form m := m - n and do case split

        subq    n, m
        jc      bignum_ge_ylonger

// The case where x is longer or of the same size (m >= n)

        incq    m
        testq   n, n
        jz      bignum_ge_xtest
bignum_ge_xmainloop:
        movq    (x,i,8), a
        sbbq    (y,i,8), a
        incq    i
        decq    n
        jnz     bignum_ge_xmainloop
        jmp     bignum_ge_xtest
bignum_ge_xtoploop:
        movq    (x,i,8), a
        sbbq    $0, a
        incq    i
bignum_ge_xtest:
        decq    m
        jnz     bignum_ge_xtoploop
        sbbq    a, a
        incq    a
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

// The case where y is longer (n > m)

bignum_ge_ylonger:
        addq    n, m
        subq    m, n
        testq   m, m
        jz      bignum_ge_ytoploop
bignum_ge_ymainloop:
        movq    (x,i,8), a
        sbbq    (y,i,8), a
        incq    i
        decq    m
        jnz     bignum_ge_ymainloop
bignum_ge_ytoploop:
        movl    $0, ashort
        sbbq    (y,i,8), a
        incq    i
        decq    n
        jnz     bignum_ge_ytoploop

        sbbq    a, a
        incq    a
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
