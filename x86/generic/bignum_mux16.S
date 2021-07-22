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
// Select element from 16-element table, z := xs[k*i]
// Inputs xs[16*k], i; output z[k]
//
//    extern void bignum_mux16
//     (uint64_t k, uint64_t *z, uint64_t *xs, uint64_t i);
//
// It is assumed that all numbers xs[16] and the target z have the same size k
// The pointer xs is to a contiguous array of size 16, elements size-k bignums
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = xs, RCX = i
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_mux16
        .text

#define k rdi
#define z rsi

// These get moved from original registers

#define x rcx
#define i rax

// Other registers

#define a rdx
#define b r8
#define j r9
#define n r10



bignum_mux16:


// Copy size into decrementable counter, or skip everything if k = 0

                test    k, k
                jz      end                     // If length = 0 do nothing
                mov     n, k

// Multiply i by k so we can compare pointer offsets directly with it

                mov     rax, rcx
                mov     rcx, rdx
                mul     k

// Main loop

loop:
                mov     a, [x]
                mov     j, k
.rep 15
                mov     b, [x+8*j]
                cmp     j, i
                cmove   a, b
                add     j, k
.endr
                mov     [z], a
                add     z, 8
                add     x, 8
                dec     n
                jnz     loop

end:
                ret
