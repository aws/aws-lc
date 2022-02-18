/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

// ----------------------------------------------------------------------------
// Convert little-endian bytes to 9-digit 528-bit bignum
//
//    extern void bignum_fromlebytes_p521
//     (uint64_t z[static 9],uint8_t x[static 66])
//
// The result will be < 2^528 since it is translated from 66 bytes.
// It is mainly intended for inputs x < p_521 < 2^521 < 2^528.
//
// Since x86 is little-endian, this is just copying.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------


        .globl  bignum_fromlebytes_p521
        .globl  _bignum_fromlebytes_p521
        .text

#define z %rdi
#define x %rsi
#define a %rax

bignum_fromlebytes_p521:
_bignum_fromlebytes_p521:

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

                xorl    %eax, %eax
                movw    64(x), %ax
                movq    a, 64(z)

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
