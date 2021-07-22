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
// Reduce modulo field characteristic, z := x mod p_384
// Input x[6]; output z[6]
//
//    extern void bignum_mod_p384_6
//     (uint64_t z[static 6], uint64_t x[static 6]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_mod_p384_6
        .text

#define z rdi
#define x rsi

#define d0 rdx
#define d1 rcx
#define d2 r8
#define d3 r9
#define d4 r10
#define d5 r11
#define c rax

#define cshort eax

// Re-use the input pointer as a temporary once we're done

#define a rsi



bignum_mod_p384_6:

// Load the input and subtract p_384 from it

        mov     d0, [x]
        mov     cshort, 0x00000000ffffffff
        sub     d0, c
        mov     d1, [x+8]
        not     c
        sbb     d1, c
        mov     d2, [x+16]
        sbb     d2, -2
        mov     d3, [x+24]
        sbb     d3, -1
        mov     d4, [x+32]
        sbb     d4, -1
        mov     d5, [x+40]
        sbb     d5, -1

// Capture the top carry as a bitmask to indicate we need to add p_384 back on,
// which we actually do in a more convenient way by subtracting r_384
// where r_384 = [-1; 0; 0; 0; 1; 0x00000000ffffffff; 0xffffffff00000001]
// We don't quite have enough ABI-modifiable registers to create all three
// nonzero digits of r while maintaining d0..d5, but make the first two now.

        not     c
        sbb     a, a
        and     c, a                    // c = masked 0x00000000ffffffff
        xor     a, a
        sub     a, c                    // a = masked 0xffffffff00000001

// Do the first two digits of addition and writeback

        sub     d0, a
        mov     [z], d0
        sbb     d1, c
        mov     [z+8], d1

// Preserve the carry chain while creating the extra masked digit since
// the logical operation will clear CF

        sbb     d0, d0
        and     c, a                    // c = masked 0x0000000000000001
        neg     d0

// Do the rest of the addition and writeback

        sbb     d2, c
        mov     [z+16], d2
        sbb     d3, 0
        mov     [z+24], d3
        sbb     d4, 0
        mov     [z+32], d4
        sbb     d5, 0
        mov     [z+40], d5

        ret
