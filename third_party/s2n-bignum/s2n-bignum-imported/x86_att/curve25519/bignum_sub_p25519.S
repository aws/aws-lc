// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Subtract modulo p_25519, z := (x - y) mod p_25519
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_sub_p25519
//     (uint64_t z[static 4], uint64_t x[static 4], uint64_t y[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_sub_p25519)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_sub_p25519)
        .text

#define z %rdi
#define x %rsi
#define y %rdx

#define d0 %r8
#define d1 %r9
#define d2 %r10
#define d3 %r11

#define zero %rax
#define zeroe %eax
#define c %rcx
#define cshort %ecx

S2N_BN_SYMBOL(bignum_sub_p25519):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
#endif

// Load and subtract the two inputs as [d3;d2;d1;d0] = x - y (modulo 2^256)

        movq    (x), d0
        subq    (y), d0
        movq    8(x), d1
        sbbq    8(y), d1
        movq    16(x), d2
        sbbq    16(y), d2
        movq    24(x), d3
        sbbq    24(y), d3

// Now if x < y we want to add back p_25519, which staying within 4 digits
// means subtracting 19, since p_25519 = 2^255 - 19.
// Let c be that constant 19 when x < y, zero otherwise.

        sbbq    c, c
        xorl    zeroe, zeroe
        andq    $19, c

// Correct by adding the optional constant and masking to 255 bits

        subq    c, d0
        movq    d0, (z)
        sbbq    zero, d1
        movq    d1, 8(z)
        sbbq    zero, d2
        movq    d2, 16(z)
        sbbq    zero, d3
        btr     $63, d3
        movq    d3, 24(z)
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
