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
        jc      ylonger

// The case where x is longer or of the same size (m >= n)

        incq    m
        testq   n, n
        jz      xtest
xmainloop:
        movq    (x,i,8), a
        sbbq    (y,i,8), a
        incq    i
        decq    n
        jnz     xmainloop
        jmp     xtest
xtoploop:
        movq    (x,i,8), a
        sbbq    $0, a
        incq    i
xtest:
        decq    m
        jnz     xtoploop
        sbbq    a, a
        incq    a
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

// The case where y is longer (n > m)

ylonger:
        addq    n, m
        subq    m, n
        testq   m, m
        jz      ytoploop
ymainloop:
        movq    (x,i,8), a
        sbbq    (y,i,8), a
        incq    i
        decq    m
        jnz     ymainloop
ytoploop:
        movl    $0, ashort
        sbbq    (y,i,8), a
        incq    i
        decq    n
        jnz     ytoploop

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
