// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Almost-Montgomery multiply, z :== (x * y / 2^{64k}) (congruent mod m)
// Inputs x[k], y[k], m[k]; output z[k]
//
//    extern void bignum_amontmul
//     (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *y, uint64_t *m);
//
// Does z :== (x * y / 2^{64k}) mod m, meaning that the result, in the native
// size k, is congruent modulo m, but might not be fully reduced mod m. This
// is why it is called *almost* Montgomery multiplication.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = x, RCX = y, R8 = m
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = x, R9 = y, [RSP+40] = m
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_amontmul)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_amontmul)
        .text

// We copy x into r9 but it comes in in rdx originally

#define k rdi
#define z rsi
#define x r9
#define y rcx
#define m r8

// General temp, low part of product and mul input
#define a rax
// General temp, High part of product
#define b rdx
// Inner loop counter
#define j rbx
// Home for i'th digit or Montgomery multiplier
#define d rbp
#define h r10
#define e r11
#define n r12
#define i r13
#define c0 r14
#define c1 r15

// This one variable we store on the stack as we are a register short.
// At least it's only used once per iteration of the outer loop (k times)
// and with a single read each time, after one initial write. The variable
// is the word-level negated modular inverse

#define w QWORD PTR [rsp]

// Some more intuitive names for temp regs in initial word-level negmodinv.

#define t1 rbx
#define t2 rdx

#define ashort eax
#define jshort ebx


S2N_BN_SYMBOL(bignum_amontmul):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
        mov     r8, [rsp+56]
#endif

// Save registers and allocate space on stack for non-register variable w

        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15
        sub     rsp, 8

// If k = 0 the whole operation is trivial

        test    k, k
        jz      bignum_amontmul_end

// Move x input into its permanent home, since we need rdx for multiplications

        mov     x, rdx

// Compute word-level negated modular inverse w for m == m[0].

        mov     a, [m]

        mov     t2, a
        mov     t1, a
        shl     t2, 2
        sub     t1, t2
        xor     t1, 2

        mov     t2, t1
        imul    t2, a
        mov     ashort, 2
        add     a, t2
        add     t2, 1

        imul    t1, a

        imul    t2, t2
        mov     ashort, 1
        add     a, t2
        imul    t1, a

        imul    t2, t2
        mov     ashort, 1
        add     a, t2
        imul    t1, a

        imul    t2, t2
        mov     ashort, 1
        add     a, t2
        imul    t1, a

        mov     w, t1

// Initialize the output c0::z to zero so we can then consistently add rows.
// It would be a bit more efficient to special-case the zeroth row, but
// this keeps the code slightly simpler.

        xor     i, i            // Also initializes i for main loop
        xor     j, j
bignum_amontmul_zoop:
        mov     [z+8*j], i
        inc     j
        cmp     j, k
        jc      bignum_amontmul_zoop

        xor     c0, c0

// Outer loop pulling down digits d=x[i], multiplying by y and reducing

bignum_amontmul_outerloop:

// Multiply-add loop where we always have CF + previous high part h to add in.
// Note that in general we do need yet one more carry in this phase and hence
// initialize c1 with the top carry.

        mov     d, [x+8*i]
        xor     j, j
        xor     h, h
        xor     c1, c1
        mov     n, k

bignum_amontmul_maddloop:
        adc     h, [z+8*j]
        sbb     e, e
        mov     a, [y+8*j]
        mul     d
        sub     rdx, e
        add     a, h
        mov     [z+8*j], a
        mov     h, rdx
        inc     j
        dec     n
        jnz     bignum_amontmul_maddloop
        adc     c0, h
        adc     c1, c1

// Montgomery reduction loop, similar but offsetting writebacks

        mov     e, [z]
        mov     d, w
        imul    d, e
        mov     a, [m]
        mul     d
        add     a, e            // Will be zero but want the carry
        mov     h, rdx
        mov     jshort, 1
        mov     n, k
        dec     n
        jz      bignum_amontmul_montend

bignum_amontmul_montloop:
        adc     h, [z+8*j]
        sbb     e, e
        mov     a, [m+8*j]
        mul     d
        sub     rdx, e
        add     a, h
        mov     [z+8*j-8], a
        mov     h, rdx
        inc     j
        dec     n
        jnz     bignum_amontmul_montloop

bignum_amontmul_montend:
        adc     h, c0
        adc     c1, 0
        mov     c0, c1
        mov     [z+8*j-8], h

// End of outer loop.

        inc     i
        cmp     i, k
        jc      bignum_amontmul_outerloop

// Now convert carry word, which is always in {0,1}, into a mask "d"
// and do a masked subtraction of m for the final almost-Montgomery result.

        xor     d, d
        sub     d, c0
        xor     e, e
        xor     j, j
bignum_amontmul_corrloop:
        mov     a, [m+8*j]
        and     a, d
        neg     e
        sbb     [z+8*j], a
        sbb     e, e
        inc     j
        cmp     j, k
        jc      bignum_amontmul_corrloop

bignum_amontmul_end:

        add     rsp, 8
        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
