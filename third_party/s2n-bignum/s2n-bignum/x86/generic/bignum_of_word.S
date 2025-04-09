// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert single digit to bignum, z := n
// Input n; output z[k]
//
//    extern void bignum_of_word (uint64_t k, uint64_t *z, uint64_t n);
//
// Create a k-digit (digit=64 bits) bignum at z with value n (mod 2^k)
// where n is a word. The "mod 2^k" only matters in the degenerate k = 0 case.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = n
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = n
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_of_word)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_of_word)
        .text

S2N_BN_SYMBOL(bignum_of_word):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// If k = 0 do nothing

        test    rdi, rdi
        jz      bignum_of_word_end

bignum_of_word_nontrivial:

// Write lowest word and jump to end if k = 1

        mov     [rsi],rdx
        dec     rdi
        jz      bignum_of_word_end

// Zero rdx and write it to all z[i] for i = k-1 down to 1
// It's a bit more compact to iterate "high to low" like this.
// But at the cost of bumping up rsi by lea rsi, [rsi+8]
// each time round the loop (which also modifies one more reg)
// we could go "low to high" if it helps with prefetch etc.

        xor     rdx, rdx
bignum_of_word_loop:
        mov     [rsi+8*rdi],rdx
        dec     rdi
        jnz     bignum_of_word_loop

bignum_of_word_end:
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
