// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Test bignum for odd-ness
// Input x[k]; output function return
//
//    extern uint64_t bignum_odd(uint64_t k, const uint64_t *x);
//
// Standard x86-64 ABI: RDI = k, RSI = x, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = x, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_odd)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_odd)
        .text

S2N_BN_SYMBOL(bignum_odd):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

// Set default return value of 0 and finish if k = 0 (trivially not odd)

        xorl    %eax, %eax
        testq   %rdi, %rdi
        jz      bignum_odd_end

// Otherwise return lowest bit of the input

        movl    $1, %eax
        andq    (%rsi), %rax

bignum_odd_end:

#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
