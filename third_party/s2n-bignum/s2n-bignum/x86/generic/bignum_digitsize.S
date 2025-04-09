// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Return size of bignum in digits (64-bit word)
// Input x[k]; output function return
//
//    extern uint64_t bignum_digitsize (uint64_t k, uint64_t *x);
//
// In the case of a zero bignum as input the result is 0
//
// Standard x86-64 ABI: RDI = k, RSI = x, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = x, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_digitsize)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_digitsize)
        .text

#define k rdi
#define x rsi
#define i rax
#define a rcx
#define j rdx



S2N_BN_SYMBOL(bignum_digitsize):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Initialize the index i and also prepare default return value of 0 (i = rax)

        xor     i, i

// If the bignum is zero-length, just return 0

        test    k, k
        jz      bignum_digitsize_end

// Run over the words j = 0..i-1, and set i := j + 1 when hitting nonzero a[j]

        xor     j, j
bignum_digitsize_loop:
        mov     a, [x+8*j]
        inc     j
        test    a, a
        cmovnz  i, j
        cmp     j, k
        jnz     bignum_digitsize_loop

bignum_digitsize_end:
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
