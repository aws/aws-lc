// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Test bignum for even-ness
// Input x[k]; output function return
//
//    extern uint64_t bignum_even (uint64_t k, uint64_t *x);
//
// Standard x86-64 ABI: RDI = k, RSI = x, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = x, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_even)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_even)
        .text

S2N_BN_SYMBOL(bignum_even):

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load RAX with the lowest digit for k > 0, else 0

        xor     rax, rax
        test    rdi, rdi
        cmovnz  rax, [rsi]

// Now just return the LSB, flipped by XORING

        and     rax, 1
        xor     rax, 1
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
