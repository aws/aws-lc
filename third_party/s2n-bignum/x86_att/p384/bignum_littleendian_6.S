// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert 6-digit (384-bit) bignum to/from little-endian form
// Input x[6]; output z[6]
//
//    extern void bignum_littleendian_6
//     (uint64_t z[static 6], uint64_t x[static 6]);
//
// The same function is given two other prototypes whose names reflect the
// treatment of one or other argument as a byte array rather than word array:
//
//    extern void bignum_fromlebytes_6
//     (uint64_t z[static 6], uint8_t x[static 48]);
//
//    extern void bignum_tolebytes_6
//     (uint8_t z[static 48], uint64_t x[static 6]);
//
// Since x86 is little-endian, this is just copying.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_littleendian_6)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_littleendian_6)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_fromlebytes_6)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_fromlebytes_6)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tolebytes_6)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tolebytes_6)

        .text

#define z %rdi
#define x %rsi
#define a %rax

S2N_BN_SYMBOL(bignum_littleendian_6):
S2N_BN_SYMBOL(bignum_fromlebytes_6):
S2N_BN_SYMBOL(bignum_tolebytes_6):

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

#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
