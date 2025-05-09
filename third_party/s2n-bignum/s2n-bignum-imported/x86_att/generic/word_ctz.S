// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Count trailing zero bits in a single word
// Input a; output function return
//
//    extern uint64_t word_ctz (uint64_t a);
//
// Standard x86-64 ABI: RDI = a, returns RAX
// Microsoft x64 ABI:   RCX = a, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(word_ctz)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(word_ctz)
        .text

S2N_BN_SYMBOL(word_ctz):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
#endif

// First just do %rax = bsf(a), which is right except (maybe) for zero inputs

        bsfq    %rdi, %rax

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
