// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Test bignum for zero-ness, x = 0
// Input x[k]; output function return
//
//    extern uint64_t bignum_iszero (uint64_t k, uint64_t *x);
//
// Standard x86-64 ABI: RDI = k, RSI = x, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = x, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_iszero)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_iszero)
        .text

#define a %rax
#define k %rdi
#define x %rsi

S2N_BN_SYMBOL(bignum_iszero):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif
        xorq    a, a
        testq   k, k
        jz      bignum_iszero_end

bignum_iszero_loop:
        orq     -8(x,k,8), a
        decq    k
        jnz     bignum_iszero_loop

// Set a standard C condition based on whether a is nonzero

        negq    a
        sbbq    a, a

bignum_iszero_end:
        incq    a
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
