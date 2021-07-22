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
// Reduce modulo group order, z := x mod n_384
// Input x[6]; output z[6]
//
//    extern void bignum_mod_n384_6
//      (uint64_t z[static 6], uint64_t x[static 6]);
//
// Reduction is modulo the group order of the NIST curve P-384.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_mod_n384_6
        .text

#define z rdi
#define x rsi

#define d0 rdx
#define d1 rcx
#define d2 r8
#define d3 r9
#define d4 r10
#define d5 r11

#define a rax

// Re-use the input pointer as a temporary once we're done

#define c rsi



bignum_mod_n384_6:

// Load the input and compute x + (2^384 - n_384)

        mov     a, 0x1313e695333ad68d
        mov     d0, [x]
        add     d0, a
        mov     d1, 0xa7e5f24db74f5885
        adc     d1, [x+8]
        mov     d2, 0x389cb27e0bc8d220
        adc     d2, [x+16]
        mov     d3, [x+24]
        adc     d3, 0
        mov     d4, [x+32]
        adc     d4, 0
        mov     d5, [x+40]
        adc     d5, 0

// Now CF is set iff 2^384 <= x + (2^384 - n_384), i.e. iff n_384 <= x.
// Create a mask for the condition x < n. We now want to subtract the
// masked (2^384 - n_384), but because we're running out of registers
// without using a save-restore sequence, we need some contortions.
// Create the lowest digit (re-using a kept from above)

        sbb     c, c
        not     c
        and     a, c

// Do the first digit of addition and writeback

        sub     d0, a
        mov     [z], d0

// Preserve carry chain and do the next digit

        sbb     d0, d0
        mov     a, 0xa7e5f24db74f5885
        and     a, c
        neg     d0
        sbb     d1, a
        mov     [z+8], d1

// Preserve carry chain once more and do remaining digits

        sbb     d0, d0
        mov     a, 0x389cb27e0bc8d220
        and     a, c
        neg     d0
        sbb     d2, a
        mov     [z+16], d2
        sbb     d3, 0
        mov     [z+24], d3
        sbb     d4, 0
        mov     [z+32], d4
        sbb     d5, 0
        mov     [z+40], d5

        ret
