// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Negated multiply-add with single-word multiplier, z := z - c * y
// Inputs c, y[n]; outputs function return (carry-out) and z[k]
//
//    extern uint64_t bignum_cmnegadd
//     (uint64_t k, uint64_t *z, uint64_t c, uint64_t n, uint64_t *y);
//
// Does the "z := z - c * y" operation where y is n digits, result z is p.
// Truncates the result in general.
//
// The return value is a high/carry word that is meaningful when n <= p.
// It is interpreted negatively as z' - 2^{64k} * return = z - c * y.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = c, RCX = n, R8 = y, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = c, R9 = n, [RSP+40] = y, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_cmnegadd)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_cmnegadd)
        .text

#define p %rdi
#define z %rsi
#define c %r9
#define n %rcx
#define x %r8

#define i %r10
#define h %r11

#define r %rbx

#define hshort %r11d
#define ishort %r10d



S2N_BN_SYMBOL(bignum_cmnegadd):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
        movq    %r9, %rcx
        movq    56(%rsp), %r8
#endif

// Seems hard to avoid one more register

        pushq   %rbx

// First clamp the input size n := min(p,n) since we can never need to read
// past the p'th term of the input to generate p-digit output.
// Subtract p := p - min(n,p) so it holds the size of the extra tail needed

        cmpq    n, p
        cmovcq  p, n
        subq    n, p

// Initialize high part h = 0; if n = 0 do nothing but return that zero

        xorq    h, h
        testq   n, n
        jz      bignum_cmnegadd_end

// Move c into a safer register as multiplies overwrite %rdx

        movq    %rdx, c

// Initialization of the loop: 2^64 * CF + [h,z_0'] = z_0 + c * ~x_0 + c

        movq    (x), %rax
        notq    %rax
        mulq    c
        addq    c, %rax
        adcq    $0, %rdx
        addq    %rax, (z)
        movq    %rdx, h
        movl    $1, ishort
        decq    n
        jz      bignum_cmnegadd_tail

// Main loop, where we always have CF + previous high part h to add in

bignum_cmnegadd_loop:
        adcq    (z,i,8), h
        sbbq    r, r
        movq    (x,i,8), %rax
        notq    %rax
        mulq    c
        subq    r, %rdx
        addq    h, %rax
        movq    %rax, (z,i,8)
        movq    %rdx, h
        incq    i
        decq    n
        jnz     bignum_cmnegadd_loop

// At this point we have 2^{64n} * (h + CF) + z' = z + c * (2^{64n} - x)
// so z' - 2^{64n} * (c - (h + CF)) = z - c * x.
// Since z - c * x < 2^{64n} we must have c - (h + CF) >= 0.
// Accumulate the negative carry in h for consistency with trivial cases.

bignum_cmnegadd_tail:
        sbbq    h, c
        movq    c, h

// Propagate the carry all the way to the end with h as extra carry word

        testq   p, p
        jz      bignum_cmnegadd_end

        subq    h, (z,i,8)
        movl    $0, hshort
        incq    i
        decq    p
        jz      bignum_cmnegadd_highend

bignum_cmnegadd_tloop:
        sbbq    h, (z,i,8)
        incq    i
        decq    p
        jnz     bignum_cmnegadd_tloop

bignum_cmnegadd_highend:

// Adjust the high word with the carry from subtraction

        adcq    $0, h

// Return the high/carry word

bignum_cmnegadd_end:
        movq    h, %rax

        popq    %rbx
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
