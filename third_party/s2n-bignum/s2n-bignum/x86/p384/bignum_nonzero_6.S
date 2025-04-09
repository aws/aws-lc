// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// 384-bit nonzeroness test, returning 1 if x is nonzero, 0 if x is zero
// Input x[6]; output function return
//
//    extern uint64_t bignum_nonzero_6(uint64_t x[static 6]);
//
// Standard x86-64 ABI: RDI = x, returns RAX
// Microsoft x64 ABI:   RCX = x, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_nonzero_6)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_nonzero_6)
        .text

#define x rdi
#define a rax
#define d rdx
#define dshort edx



S2N_BN_SYMBOL(bignum_nonzero_6):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
#endif

// Generate a = an OR of all the words in the bignum

        mov     a, [x]
        mov     d, [x+8]
        or      a, [x+16]
        or      d, [x+24]
        or      a, [x+32]
        or      d, [x+40]
        or      a, d

// Set a standard C condition based on whether a is nonzero

        mov     dshort, 1
        cmovnz  a, d

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
