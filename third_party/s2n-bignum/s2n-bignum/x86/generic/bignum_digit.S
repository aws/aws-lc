// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Select digit x[n]
// Inputs x[k], n; output function return
//
//    extern uint64_t bignum_digit (uint64_t k, uint64_t *x, uint64_t n);
//
// n'th digit of a k-digit (digit=64 bits) bignum, in constant-time style.
// Indexing starts at 0, which is the least significant digit (little-endian).
// Returns zero if n >= k, i.e. we read a digit off the end of the bignum.
//
// Standard x86-64 ABI: RDI = k, RSI = x, RDX = n, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = x, R8 = n, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_digit)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_digit)
        .text

#define k rdi
#define x rsi
#define n rdx

#define d rax
#define i rcx
#define a r8

S2N_BN_SYMBOL(bignum_digit):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Set the default digit to 0, and for length zero finish immediately

        xor     d, d
        test    k,k
        jz      bignum_digit_end

// Main loop: run over all the digits and take note of the n'th one

        xor     i, i
bignum_digit_loop:
        mov     a, [x+8*i]
        cmp     i, n
        cmovz   d, a
        inc     i
        cmp     i, k
        jc      bignum_digit_loop

// Return

bignum_digit_end:
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
