// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// Convert 9-digit 528-bit bignum to little-endian bytes
//
//    extern void bignum_tolebytes_p521
//     (uint8_t z[static 66], uint64_t x[static 9]);
//
// This is assuming the input x is < 2^528 so that it fits in 66 bytes.
// In particular this holds if x < p_521 < 2^521 < 2^528.
//
// Since x86 is little-endian, this is just copying.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tolebytes_p521)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tolebytes_p521)
        .text

#define z %rdi
#define x %rsi
#define a %rax

S2N_BN_SYMBOL(bignum_tolebytes_p521):

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

        movq    (x), a
        movq    a, (z)

        movq    8(x), a
        movq    a, 8(z)

        movq    16(x), a
        movq    a, 16(z)

        movq    24(x), a
        movq    a, 24(z)

        movq    32(x), a
        movq    a, 32(z)

        movq    40(x), a
        movq    a, 40(z)

        movq    48(x), a
        movq    a, 48(z)

        movq    56(x), a
        movq    a, 56(z)

        movq    64(x), a
        movw    %ax, 64(z)

#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
