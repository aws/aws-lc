// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Count leading zero digits (64-bit words)
// Input x[k]; output function return
//
//    extern uint64_t bignum_cld (uint64_t k, uint64_t *x);
//
// In the case of a zero bignum as input the result is k
//
// Standard x86-64 ABI: RDI = k, RSI = x, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = x, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_cld)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_cld)
        .text

#define k %rdi
#define x %rsi
#define i %rax
#define a %rcx
#define j %rdx



S2N_BN_SYMBOL(bignum_cld):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

// Initialize the index i and also prepare default return value of 0 (i = %rax)

        xorq    i, i

// If the bignum is zero-length, just return k = 0

        testq   k, k
        jz      bignum_cld_end

// Run over the words j = 0..i-1, and set i := j + 1 when hitting nonzero a[j]

        xorq    j, j
bignum_cld_loop:
        movq    (x,j,8), a
        incq    j
        testq   a, a
        cmovnzq j, i
        cmpq    k, j
        jnz     bignum_cld_loop

        negq    %rax
        addq    %rdi, %rax

bignum_cld_end:
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
