// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiplex/select z := x (if p nonzero) or z := y (if p zero)
// Inputs p, x[k], y[k]; output z[k]
//
//    extern void bignum_mux(uint64_t p, uint64_t k, uint64_t *z, const uint64_t *x,
//                           const uint64_t *y);
//
// It is assumed that all numbers x, y and z have the same size k digits.
//
// Standard x86-64 ABI: RDI = p, RSI = k, RDX = z, RCX = x, R8 = y
// Microsoft x64 ABI:   RCX = p, RDX = k, R8 = z, R9 = x, [RSP+40] = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mux)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mux)
        .text

#define b %rdi
#define k %rsi
#define z %rdx
#define x %rcx
#define y %r8
#define i %r9
#define a %rax



S2N_BN_SYMBOL(bignum_mux):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
        movq    %r9, %rcx
        movq    56(%rsp), %r8
#endif
        testq   k, k
        jz      bignum_mux_end                     // If length = 0 do nothing

        xorq    i, i
        negq    b                       // CF <=> (b != 0)
bignum_mux_loop:
        movq    (x,i,8), a
        movq    (y,i,8), b
        cmovncq b, a // CF ? a : b
        movq    a, (z,i,8)
        incq    i
        decq    k
        jnz     bignum_mux_loop
bignum_mux_end:
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
