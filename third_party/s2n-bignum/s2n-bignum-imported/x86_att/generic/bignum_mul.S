// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply z := x * y
// Inputs x[m], y[n]; output z[k]
//
//    extern void bignum_mul(uint64_t k, uint64_t *z, uint64_t m, const uint64_t *x,
//                           uint64_t n, const uint64_t *y);
//
// Does the "z := x * y" operation where x is m digits, y is n, result z is k.
// Truncates the result in general unless k >= m + n
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = m, RCX = x, R8 = n, R9 = y
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = m, R9 = x, [RSP+40] = n, [RSP+48] = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mul)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mul)
        .text

// These are actually right

#define p %rdi
#define z %rsi
#define n %r8

// These are not

#define c %r15
#define h %r14
#define l %r13
#define x %r12
#define y %r11
#define i %rbx
#define k %r10
#define m %rbp

// These are always local scratch since multiplier result is in these

#define a %rax
#define d %rdx



S2N_BN_SYMBOL(bignum_mul):
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

// We use too many registers, and also we need %rax:%rdx for multiplications

        pushq   %rbx
        pushq   %rbp
        pushq   %r12
        pushq   %r13
        pushq   %r14
        pushq   %r15
        movq    %rdx, m

// If the result size is zero, do nothing
// Note that even if either or both inputs has size zero, we can't
// just give up because we at least need to zero the output array
// If we did a multiply-add variant, however, then we could

        testq   p, p
        jz      bignum_mul_end

// Set initial 2-part sum to zero (we zero c inside the body)

        xorq    h, h
        xorq    l, l

// Otherwise do outer loop k = 0 ... k = p - 1

        xorq    k, k

bignum_mul_outerloop:

// Zero our carry term first; we eventually want it and a zero is useful now
// Set a =  max 0 (k + 1 - n), i = min (k + 1) m
// This defines the range a <= j < i for the inner summation
// Note that since k < p < 2^64 we can assume k + 1 doesn't overflow
// And since we want to increment it anyway, we might as well do it now

        xorq    c, c // c = 0
        incq    k               // k = k + 1

        movq    k, a // a = k + 1
        subq    n, a // a = k + 1 - n
        cmovcq  c, a // a = max 0 (k + 1 - n)

        movq    m, i // i = m
        cmpq    m, k // CF <=> k + 1 < m
        cmovcq  k, i // i = min (k + 1) m

// Turn i into a loop count, and skip things if it's <= 0
// Otherwise set up initial pointers x -> x0[a] and y -> y0[k - a]
// and then launch into the main inner loop, postdecrementing i

        movq    k, d
        subq    i, d
        subq    a, i
        jbe     bignum_mul_innerend
        leaq    (%rcx,a,8), x
        leaq    -8(%r9,d,8), y

bignum_mul_innerloop:
        movq    (y,i,8), %rax
        mulq      (x)
        addq    $8, x
        addq    %rax, l
        adcq    %rdx, h
        adcq    $0, c
        decq    i
        jnz     bignum_mul_innerloop

bignum_mul_innerend:

        movq    l, (z)
        movq    h, l
        movq    c, h
        addq    $8, z

        cmpq    p, k
        jc      bignum_mul_outerloop

bignum_mul_end:
        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12
        popq    %rbp
        popq    %rbx
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
