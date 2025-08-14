// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Add, z := x + y
// Inputs x[m], y[n]; outputs function return (carry-out) and z[p]
//
//    extern uint64_t bignum_add(uint64_t p, uint64_t *z, uint64_t m,
//                               const uint64_t *x, uint64_t n, const uint64_t *y);
//
// Does the z := x + y operation, truncating modulo p words in general and
// returning a top carry (0 or 1) in the p'th place, only adding the input
// words below p (as well as m and n respectively) to get the sum and carry.
//
// Standard x86-64 ABI: RDI = p, RSI = z, RDX = m, RCX = x, R8 = n, R9 = y, returns RAX
// Microsoft x64 ABI:   RCX = p, RDX = z, R8 = m, R9 = x, [RSP+40] = n, [RSP+48] = y, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_add)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_add)
        .text

#define p %rdi
#define z %rsi
#define m %rdx
#define x %rcx
#define n %r8
#define y %r9
#define i %r10
#define a %rax

#define ashort %eax



S2N_BN_SYMBOL(bignum_add):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
        movq    %r9, %rcx
        movq    56(%rsp), %r8
        movq    64(%rsp), %r9
#endif

// Zero the main index counter for both branches

        xorq    i, i

// First clamp the two input sizes m := min(p,m) and n := min(p,n) since
// we'll never need words past the p'th. Can now assume m <= p and n <= p.
// Then compare the modified m and n and branch accordingly

        cmpq    m, p
        cmovcq  p, m
        cmpq    n, p
        cmovcq  p, n
        cmpq    n, m
        jc      bignum_add_ylonger

// The case where x is longer or of the same size (p >= m >= n)

        subq    m, p
        subq    n, m
        incq    m
        testq   n, n
        jz      bignum_add_xtest
bignum_add_xmainloop:
        movq    (x,i,8), a
        adcq    (y,i,8), a
        movq    a, (z,i,8)
        incq    i
        decq    n
        jnz     bignum_add_xmainloop
        jmp     bignum_add_xtest
bignum_add_xtoploop:
        movq    (x,i,8), a
        adcq    $0, a
        movq    a, (z,i,8)
        incq    i
bignum_add_xtest:
        decq    m
        jnz     bignum_add_xtoploop
        movl    $0, ashort
        adcq    $0, a
        testq   p, p
        jnz     bignum_add_tails
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

// The case where y is longer (p >= n > m)

bignum_add_ylonger:

        subq    n, p
        subq    m, n
        testq   m, m
        jz      bignum_add_ytoploop
bignum_add_ymainloop:
        movq    (x,i,8), a
        adcq    (y,i,8), a
        movq    a, (z,i,8)
        incq    i
        decq    m
        jnz     bignum_add_ymainloop
bignum_add_ytoploop:
        movq    (y,i,8), a
        adcq    $0, a
        movq    a, (z,i,8)
        incq    i
        decq    n
        jnz     bignum_add_ytoploop
        movl    $0, ashort
        adcq    $0, a
        testq   p, p
        jnz     bignum_add_tails
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

// Adding a non-trivial tail, when p > max(m,n)

bignum_add_tails:
        movq    a, (z,i,8)
        xorq    a, a
        jmp     bignum_add_tail
bignum_add_tailloop:
        movq    a, (z,i,8)
bignum_add_tail:
        incq    i
        decq    p
        jnz     bignum_add_tailloop
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
