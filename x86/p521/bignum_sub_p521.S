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
// Subtract modulo p_521, z := (x - y) mod p_521
// Inputs x[9], y[9]; output z[9]
//
//    extern void bignum_sub_p521
//     (uint64_t z[static 9], uint64_t x[static 9], uint64_t y[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_sub_p521
        .text

#define z rdi
#define x rsi
#define y rdx

#define d0 rax
#define d1 rcx
#define d2 r8
#define d3 r9
#define d4 r10
#define d5 r11
#define d6 r12
#define d7 rbx

// Re-use one input pointer as other variable once safe to do so

#define d8 rsi



bignum_sub_p521:

// Save more registers to play with

        push    rbx
        push    r12

// First just subtract the numbers as [d8;d7;d6;d5;d4;d3;d2;d1;d0] = x - y

        mov     d0, [x]
        sub     d0, [y]
        mov     d1, [x+8]
        sbb     d1, [y+8]
        mov     d2, [x+16]
        sbb     d2, [y+16]
        mov     d3, [x+24]
        sbb     d3, [y+24]
        mov     d4, [x+32]
        sbb     d4, [y+32]
        mov     d5, [x+40]
        sbb     d5, [y+40]
        mov     d6, [x+48]
        sbb     d6, [y+48]
        mov     d7, [x+56]
        sbb     d7, [y+56]
        mov     d8, [x+64]
        sbb     d8, [y+64]

// Now if x < y we want (x - y) + p_521 == (x - y) - 1 (mod 2^521)
// Otherwise we just want the existing x - y result. So subtract
// 1 iff the initial subtraction carried, then mask to 521 bits.
// Write back the results as generated.

        sbb     d0, 0
        mov     [z], d0
        sbb     d1, 0
        mov     [z+8], d1
        sbb     d2, 0
        mov     [z+16], d2
        sbb     d3, 0
        mov     [z+24], d3
        sbb     d4, 0
        mov     [z+32], d4
        sbb     d5, 0
        mov     [z+40], d5
        sbb     d6, 0
        mov     [z+48], d6
        sbb     d7, 0
        mov     [z+56], d7
        sbb     d8, 0
        and     d8, 0x1FF
        mov     [z+64], d8

// Restore registers and return

        pop     r12
        pop     rbx

        ret
