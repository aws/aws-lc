// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Count trailing zero digits (64-bit words)
// Input x[k]; output function return
//
//    extern uint64_t bignum_ctd (uint64_t k, uint64_t *x);
//
// In the case of a zero bignum as input the result is k
//
// Standard x86-64 ABI: RDI = k, RSI = x, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = x, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_ctd)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_ctd)
        .text

#define k rdi
#define x rsi
#define i rdx
#define a rax



S2N_BN_SYMBOL(bignum_ctd):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// If the bignum is zero-length, just return 0

        xor     rax, rax
        test    k, k
        jz      bignum_ctd_end

// Record in i that the lowest nonzero word is i - 1, where i = k + 1 means
// that the bignum was entirely zero

        mov     i, k
        inc     i
bignum_ctd_loop:
        mov     a, [x+8*k-8]
        test    a, a
        cmovne  i, k
        dec     k
        jnz     bignum_ctd_loop

// We now want to return i - 1

        dec     i
        mov     rax, i
bignum_ctd_end:
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
