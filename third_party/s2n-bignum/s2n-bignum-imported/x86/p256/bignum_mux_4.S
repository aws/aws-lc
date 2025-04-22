// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// 256-bit multiplex/select z := x (if p nonzero) or z := y (if p zero)
// Inputs p, x[4], y[4]; output z[4]
//
//    extern void bignum_mux_4
//     (uint64_t p, uint64_t z[static 4],
//      uint64_t x[static 4], uint64_t y[static 4]);
//
// It is assumed that all numbers x, y and z have the same size 4 digits.
//
// Standard x86-64 ABI: RDI = p, RSI = z, RDX = x, RCX = y
// Microsoft x64 ABI:   RCX = p, RDX = z, R8 = x, R9 = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mux_4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mux_4)
        .text

#define p rdi
#define z rsi
#define x rdx
#define y rcx
#define a rax
#define b r8


S2N_BN_SYMBOL(bignum_mux_4):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif
        test    p, p

        mov     a, [x]
        mov     b, [y]
        cmovz   a, b
        mov     [z], a

        mov     a, [x+8]
        mov     b, [y+8]
        cmovz   a, b
        mov     [z+8], a

        mov     a, [x+16]
        mov     b, [y+16]
        cmovz   a, b
        mov     [z+16], a

        mov     a, [x+24]
        mov     b, [y+24]
        cmovz   a, b
        mov     [z+24], a

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
