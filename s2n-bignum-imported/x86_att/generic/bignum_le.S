// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Compare bignums, x <= y
// Inputs x[m], y[n]; output function return
//
//    extern uint64_t bignum_le(uint64_t m, const uint64_t *x, uint64_t n,
//                              const uint64_t *y);
//
// Standard x86-64 ABI: RDI = m, RSI = x, RDX = n, RCX = y, returns RAX
// Microsoft x64 ABI:   RCX = m, RDX = x, R8 = n, R9 = y, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_le)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_le)
        .text

#define m %rdi
#define x %rsi
#define n %rdx
#define y %rcx
#define i %r8
#define a %rax

#define ashort %eax



S2N_BN_SYMBOL(bignum_le):
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

// Speculatively form n := n - m and do case split

        subq    m, n
        jc      bignum_le_ylonger

// The case where y is longer or of the same size (n >= m)

        incq    n
        testq   m, m
        jz      bignum_le_xtest
bignum_le_xmainloop:
        movq    (y,i,8), a
        sbbq    (x,i,8), a
        incq    i
        decq    m
        jnz     bignum_le_xmainloop
        jmp     bignum_le_xtest
bignum_le_xtoploop:
        movq    (y,i,8), a
        sbbq    $0, a
        incq    i
bignum_le_xtest:
        decq    n
        jnz     bignum_le_xtoploop
        sbbq    a, a
        incq    a
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

// The case where x is longer (m > n)

bignum_le_ylonger:
        addq    m, n
        subq    n, m
        testq   n, n
        jz      bignum_le_ytoploop
bignum_le_ymainloop:
        movq    (y,i,8), a
        sbbq    (x,i,8), a
        incq    i
        decq    n
        jnz     bignum_le_ymainloop
bignum_le_ytoploop:
        movl    $0, ashort
        sbbq    (x,i,8), a
        incq    i
        decq    m
        jnz     bignum_le_ytoploop

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
