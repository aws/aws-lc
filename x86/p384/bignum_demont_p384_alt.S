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
// Convert from Montgomery form z := (x / 2^384) mod p_384, assuming x reduced
// Input x[6]; output z[6]
//
//    extern void bignum_demont_p384_alt
//     (uint64_t z[static 6], uint64_t x[static 6]);
//
// This assumes the input is < p_384 for correctness. If this is not the case,
// use the variant "bignum_deamont_p384" instead.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_demont_p384_alt
        .text

#define z rdi
#define x rsi

// Core one-step "short" Montgomery reduction macro. Takes input in
// [d5;d4;d3;d2;d1;d0] and returns result in [d6;d5;d4;d3;d2;d1],
// adding to the existing [d5;d4;d3;d2;d1] and re-using d0 as a
// temporary internally, as well as rax, rcx and rdx.
// It is OK for d6 and d0 to be the same register (they often are)
//
// We want to add (2^384 - 2^128 - 2^96 + 2^32 - 1) * w
// where w = [d0 + (d0<<32)] mod 2^64
//
//       montreds(d6,d5,d4,d3,d2,d1,d0)

#define montreds(d6,d5,d4,d3,d2,d1,d0)                                  \
/* Our correction multiplier is w = [d0 + (d0<<32)] mod 2^64 */         \
                mov     rcx, d0;                                        \
                shl     rcx, 32;                                        \
                add     rcx, d0;                                        \
/* Construct [rax;rdx;d0;-] = (2^384 - p_384) * w            */         \
/* We know the lowest word will cancel so we can re-use d0   */         \
/* and rcx as temps.                                         */         \
                mov     rax, 0xffffffff00000001;                        \
                mul     rcx;                                            \
                mov     d0, rdx;                                        \
                mov     rax, 0x00000000ffffffff;                        \
                mul     rcx;                                            \
                add     d0, rax;                                        \
                mov     eax, 0;                                         \
                adc     rdx, rcx;                                       \
                adc     eax, eax;                                       \
/* Now subtract that and add 2^384 * w                       */         \
                sub     d1, d0;                                         \
                sbb     d2, rdx;                                        \
                sbb     d3, rax;                                        \
                sbb     d4, 0;                                          \
                sbb     d5, 0;                                          \
                mov     d6, rcx;                                        \
                sbb     d6, 0

bignum_demont_p384_alt:

// Save more registers to play with

        push    r12
        push    r13

// Set up an initial window [r13,r12,r11,r10,r9,r8] = x

        mov     r8, [x]
        mov     r9, [x+8]
        mov     r10, [x+16]
        mov     r11, [x+24]
        mov     r12, [x+32]
        mov     r13, [x+40]

// Montgomery reduce window 0

        montreds(r8,r13,r12,r11,r10,r9,r8)

// Montgomery reduce window 1

        montreds(r9,r8,r13,r12,r11,r10,r9)

// Montgomery reduce window 2

        montreds(r10,r9,r8,r13,r12,r11,r10)

// Montgomery reduce window 3

        montreds(r11,r10,r9,r8,r13,r12,r11)

// Montgomery reduce window 4

        montreds(r12,r11,r10,r9,r8,r13,r12)

// Montgomery reduce window 5

        montreds(r13,r12,r11,r10,r9,r8,r13)

// Write back the result

        mov     [z], r8
        mov     [z+8], r9
        mov     [z+16], r10
        mov     [z+24], r11
        mov     [z+32], r12
        mov     [z+40], r13

// Restore registers and return

        pop     r13
        pop     r12

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
