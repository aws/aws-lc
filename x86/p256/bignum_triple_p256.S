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
// Triple modulo p_256, z := (3 * x) mod p_256
// Input x[4]; output z[4]
//
//    extern void bignum_triple_p256
//      (uint64_t z[static 4], uint64_t x[static 4]);
//
// The input x can be any 4-digit bignum, not necessarily reduced modulo p_256,
// and the result is always fully reduced, i.e. z = (3 * x) mod p_256.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

#define z rdi
#define x rsi

// Main digits of intermediate results

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11

// Multipliers (constant 3 in first stage, quotient estimate q in second)
// and briefly h = q - 1 = the top of intermediate result, all aliased to rdx

#define m rdx
#define q rdx
#define h rdx

// Other temporary variables

#define a rax
#define c rcx

#define mshort edx
#define ashort eax



.intel_syntax noprefix
        .text
        .globl  bignum_triple_p256

bignum_triple_p256:

// First do the multiplication by 3, getting z = [h; d3; ...; d0]

                mov     mshort, 3
                mulx    d1, d0, [x]
                mulx    d2, a, [x+8]
                add     d1, a
                mulx    d3, a, [x+16]
                adc     d2, a
                mulx    h, a, [x+24]
                adc     d3, a
                adc     h, 0

// For this limited range a simple quotient estimate of q = h + 1 works, where
// h = floor(z / 2^256). Then -p_256 <= z - q * p_256 < p_256, so we just need
// to subtract q * p_256 and then if that's negative, add back p_256.

                inc     q

// Now compute the initial pre-reduced result z - p_256 * q
// = z - (2^256 - 2^224 + 2^192 + 2^96 - 1) * q
// = z - 2^192 * 0xffffffff00000001 * q - 2^64 * 0x0000000100000000 * q + q

                add     d0, q
                mov     a, 0x0000000100000000
                mulx    c, a, a
                sbb     a, 0
                sbb     c, 0
                sub     d1, a
                sbb     d2, c
                mov     a, 0xffffffff00000001
                mulx    c, a, a
                sbb     d3, a
                sbb     q, c

// q is now effectively the top word of the 5-digits result; this step
// compensates for q = h + 1

                dec     q

// Use that as a bitmask for a masked addition of p_256 and write back

                mov     ashort, 0x00000000ffffffff
                and     a, q
                xor     c, c
                sub     c, a
                add     d0, q
                mov     [z], d0
                adc     d1, a
                mov     [z+8], d1
                adc     d2, 0
                mov     [z+16],d2
                adc     d3, c
                mov     [z+24],d3

                ret
