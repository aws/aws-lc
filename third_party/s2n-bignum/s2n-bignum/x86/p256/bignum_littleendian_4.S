// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert 4-digit (256-bit) bignum to/from little-endian form
// Input x[4]; output z[4]
//
//    extern void bignum_littleendian_4
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// The same function is given two other prototypes whose names reflect the
// treatment of one or other argument as a byte array rather than word array:
//
//    extern void bignum_fromlebytes_4
//     (uint64_t z[static 4], uint8_t x[static 32]);
//
//    extern void bignum_tolebytes_4
//     (uint8_t z[static 32], uint64_t x[static 4]);
//
// Since x86 is little-endian, this is just copying.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_littleendian_4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_littleendian_4)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_fromlebytes_4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_fromlebytes_4)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tolebytes_4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tolebytes_4)

        .text

#define z rdi
#define x rsi
#define a rax

S2N_BN_SYMBOL(bignum_littleendian_4):
S2N_BN_SYMBOL(bignum_fromlebytes_4):
S2N_BN_SYMBOL(bignum_tolebytes_4):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
#endif

        mov     a, [x]
        mov     [z], a

        mov     a, [x+8]
        mov     [z+8], a

        mov     a, [x+16]
        mov     [z+16], a

        mov     a, [x+24]
        mov     [z+24], a

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
