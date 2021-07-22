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
// Convert from almost-Montgomery form, z := (x / 2^384) mod p_384
// Input x[6]; output z[6]
//
//    extern void bignum_deamont_p384
//     (uint64_t z[static 6], uint64_t x[static 6]);
//
// Convert a 6-digit bignum x out of its (optionally almost) Montgomery form,
// "almost" meaning any 6-digit input will work, with no range restriction.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_deamont_p384
        .text

#define z rdi
#define x rsi

// Additional temps in the correction phase

#define u rax
#define v rcx
#define w rdx

#define vshort ecx

// Core one-step "short" Montgomery reduction macro. Takes input in
// [d5;d4;d3;d2;d1;d0] and returns result in [d6;d5;d4;d3;d2;d1],
// adding to the existing contents of [d5;d4;d3;d2;d1;d0]. This
// is intended only for 6-word inputs as in mapping out of Montgomery,
// not for the general case of Montgomery multiplication. It is fine
// for d6 to be the same register as d0.
//
// Parms:  montreds d6,d5,d4,d3,d2,d1,d0
//
// We want to add (2^384 - 2^128 - 2^96 + 2^32 - 1) * w
// where w = [d0 + (d0<<32)] mod 2^64

.macro montreds d6,d5,d4,d3,d2,d1,d0
// Our correction multiplier is w = [d0 + (d0<<32)] mod 2^64
                mov     rdx, \d0
                shl     rdx, 32
                add     rdx, \d0
// Construct [rsi;rcx;rax;-] = (2^384 - p_384) * w
// We know the lowest word will cancel so we can re-use d0 as a temp
                xor     rsi, rsi
                mov     rax, 0xffffffff00000001
                mulx    rax, rcx, rax
                mov     ecx, 0x00000000ffffffff
                mulx    rcx, \d0, rcx
                adc     rax, \d0
                adc     rcx, rdx
                adc     rsi, 0
// Now subtract that and add 2^384 * w
                sub     \d1, rax
                sbb     \d2, rcx
                sbb     \d3, rsi
                sbb     \d4, 0
                sbb     \d5, 0
                mov     \d6, rdx
                sbb     \d6, 0
.endm



bignum_deamont_p384:

// Save more registers to play with

        push    r12
        push    r13

// Set up an initial window [r13,r12,r11,r10,r9,r8] = x

        mov     r8, [x+8*0]
        mov     r9, [x+8*1]
        mov     r10, [x+8*2]
        mov     r11, [x+8*3]
        mov     r12, [x+8*4]
        mov     r13, [x+8*5]

// Montgomery reduce window 0

        montreds r8,r13,r12,r11,r10,r9,r8

// Montgomery reduce window 1

        montreds r9,r8,r13,r12,r11,r10,r9

// Montgomery reduce window 2

        montreds r10,r9,r8,r13,r12,r11,r10

// Montgomery reduce window 3

        montreds r11,r10,r9,r8,r13,r12,r11

// Montgomery reduce window 4

        montreds r12,r11,r10,r9,r8,r13,r12

// Montgomery reduce window 5

        montreds r13,r12,r11,r10,r9,r8,r13

// Do a test addition of dd = [r13;r12;r11;r10;r9;r8] and
// 2^384 - p_384 = [0;0;0;1;v;u], hence setting CF iff
// dd + (2^384 - p_384) >= 2^384, hence iff dd >= p_384.

        mov     u, 0xffffffff00000001
        mov     vshort, 0x00000000ffffffff

        mov     w, r8
        add     w, u
        mov     w, r9
        adc     w, v
        mov     w, r10
        adc     w, 1
        mov     w, r11
        adc     w, 0
        mov     w, r12
        adc     w, 0
        mov     w, r13
        adc     w, 0

// Convert CF to a bitmask in w

        sbb     w, w

// Masked addition of 2^384 - p_384, hence subtraction of p_384

        and     u, w
        and     v, w
        and     w, 1

        add    r8, u
        adc    r9, v
        adc    r10, w
        adc    r11, 0
        adc    r12, 0
        adc    r13, 0

// Write back the result

        mov     [z], r8
        mov     [z+8*1], r9
        mov     [z+8*2], r10
        mov     [z+8*3], r11
        mov     [z+8*4], r12
        mov     [z+8*5], r13

// Restore registers and return

        pop     r13
        pop     r12

        ret
