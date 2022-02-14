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

        .intel_syntax noprefix
        .globl  bignum_fromlebytes_p521
        .text

#define z rdi
#define x rsi
#define a rax

bignum_fromlebytes_p521:

                mov     a, [x]
                mov     [z], a

                mov     a, [x+8]
                mov     [z+8], a

                mov     a, [x+16]
                mov     [z+16], a

                mov     a, [x+24]
                mov     [z+24], a

                mov     a, [x+32]
                mov     [z+32], a

                mov     a, [x+40]
                mov     [z+40], a

                mov     a, [x+48]
                mov     [z+48], a

                mov     a, [x+56]
                mov     [z+56], a

                xor     eax, eax
                mov     ax, [x+64]
                mov     [z+64], a

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
