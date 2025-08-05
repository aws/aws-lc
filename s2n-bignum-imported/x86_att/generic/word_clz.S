// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Count leading zero bits in a single word
// Input a; output function return
//
//    extern uint64_t word_clz(uint64_t a);
//
// Standard x86-64 ABI: RDI = a, returns RAX
// Microsoft x64 ABI:   RCX = a, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(word_clz)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(word_clz)
        .text

S2N_BN_SYMBOL(word_clz):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
#endif

// First do %rax = 63 - bsr(a), which is right except (maybe) for zero inputs

        bsrq    %rdi, %rax
        xorq    $63, %rax

// Force return of 64 in the zero-input case

        movl    $64, %edx
        testq   %rdi, %rdi
        cmoveq  %rdx, %rax

#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
