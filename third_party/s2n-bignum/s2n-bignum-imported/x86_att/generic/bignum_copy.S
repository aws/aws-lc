// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Copy bignum with zero-extension or truncation, z := x
// Input x[n]; output z[k]
//
//    extern void bignum_copy(uint64_t k, uint64_t *z, uint64_t n, const uint64_t *x);
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = n, RCX = x
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = n, R9 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_copy)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_copy)
        .text

#define k %rdi
#define z %rsi
#define n %rdx
#define x %rcx

#define i %r8
#define a %rax



S2N_BN_SYMBOL(bignum_copy):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
        movq    %r9, %rcx
#endif

// Replace RDX = n with RDX = min(k,n) so we are definitely safe copying those
// Initialize the element counter to 0

        cmpq    n, k
        cmovcq  k, n
        xorq    i, i

// If min(k,n) = 0 jump to the padding stage

        testq   n, n
        jz      bignum_copy_padding

bignum_copy_copyloop:
        movq    (x,i,8), a
        movq    a, (z,i,8)
        incq    i
        cmpq    n, i
        jc      bignum_copy_copyloop

bignum_copy_padding:
        cmpq    k, i
        jnc     bignum_copy_end
        xorq    a, a

bignum_copy_padloop:
        movq    a, (z,i,8)
        incq    i
        cmpq    k, i
        jc      bignum_copy_padloop

bignum_copy_end:
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
