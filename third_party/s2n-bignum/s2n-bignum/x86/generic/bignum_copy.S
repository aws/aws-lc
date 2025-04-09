// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Copy bignum with zero-extension or truncation, z := x
// Input x[n]; output z[k]
//
//    extern void bignum_copy
//      (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x);
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = n, RCX = x
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = n, R9 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_copy)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_copy)
        .text

#define k rdi
#define z rsi
#define n rdx
#define x rcx

#define i r8
#define a rax



S2N_BN_SYMBOL(bignum_copy):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif

// Replace RDX = n with RDX = min(k,n) so we are definitely safe copying those
// Initialize the element counter to 0

        cmp     k, n
        cmovc   n, k
        xor     i, i

// If min(k,n) = 0 jump to the padding stage

        test    n, n
        jz      bignum_copy_padding

bignum_copy_copyloop:
        mov     a, [x+8*i]
        mov     [z+8*i], a
        inc     i
        cmp     i, n
        jc      bignum_copy_copyloop

bignum_copy_padding:
        cmp     i, k
        jnc     bignum_copy_end
        xor     a, a

bignum_copy_padloop:
        mov     [z+8*i], a
        inc     i
        cmp     i, k
        jc      bignum_copy_padloop

bignum_copy_end:
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
