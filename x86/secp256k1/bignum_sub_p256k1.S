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
// Subtract modulo p_256k1, z := (x - y) mod p_256k1
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_sub_p256k1
//     (uint64_t z[static 4], uint64_t x[static 4], uint64_t y[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_sub_p256k1
        .text

#define z rdi
#define x rsi
#define y rdx

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11

#define zero rax
#define zeroe eax
#define c rcx

bignum_sub_p256k1:

// Zero a register first

        xor     zeroe, zeroe

// Load and subtract the two inputs as [d3;d2;d1;d0] = x - y (modulo 2^256)

        mov     d0, [x]
        sub     d0, [y]
        mov     d1, [x+8]
        sbb     d1, [y+8]
        mov     d2, [x+16]
        sbb     d2, [y+16]
        mov     d3, [x+24]
        sbb     d3, [y+24]

// Now if x < y we want to add back p_256k1, which staying within 4 digits
// means subtracting 4294968273, since p_256k1 = 2^256 - 4294968273.
// Let c be that constant 4294968273 when x < y, zero otherwise.

        mov     c, 4294968273
        cmovnc  c, zero

// Now correct by adding masked p_256k1, i.e. subtracting c, and write back

        sub     d0, c
        mov     [z], d0
        sbb     d1, zero
        mov     [z+8], d1
        sbb     d2, zero
        mov     [z+16], d2
        sbb     d3, zero
        mov     [z+24], d3

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
