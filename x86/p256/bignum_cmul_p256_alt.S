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
// Multiply by a single word modulo p_256, z := (c * x) mod p_256, assuming
// x reduced
// Inputs c, x[4]; output z[4]
//
//    extern void bignum_cmul_p256_alt
//     (uint64_t z[static 4], uint64_t c, uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = c, RDX = x
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_cmul_p256_alt
        .text

#define z rdi

// Temporarily moved here for initial multiply then thrown away

#define x rcx
#define m rsi

// Other variables

#define d rdx
#define a rax
#define c rcx

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11
#define h rsi

#define ashort eax
#define hshort esi

// Multiplier again for second stage

#define q rcx

bignum_cmul_p256_alt:

// Shuffle inputs (since we want rdx for the high parts of products)

                mov     x, rdx

// Multiply, accumulating the result as 2^256 * h + [d3;d2;d1;d0]

                mov     a, [x]
                mul     m
                mov     d0, a
                mov     d1, d

                mov     a, [x+8]
                mul     m
                xor     d2, d2
                add     d1, a
                adc     d2, d

                mov     a, [x+16]
                mul     m
                xor     d3, d3
                add     d2, a
                adc     d3, d

                mov     a, [x+24]
                mul     m
                xor     hshort, hshort
                add     d3, a
                adc     h, d

// Writing the product as z = 2^256 * h + 2^192 * d3 + t = 2^192 * hl + t, our
// intended quotient approximation is (hl + hl>>32 + 1)>>64. Note that by
// hypothesis our product is <= (2^64 - 1) * (p_256 - 1), so there is no need
// to max this out to avoid wrapping.

                mov     a, h
                shld    a, d3, 32
                mov     q, h
                shr     q, 32
                xor     d, d
                sub     d, 1
                adc     a, d3
                adc     q, h

// Now compute the initial pre-reduced result z - p_256 * q
// = z - (2^256 - 2^224 + 2^192 + 2^96 - 1) * q
// = z - 2^192 * 0xffffffff00000001 * q - 2^64 * 0x0000000100000000 * q + q

                mov     a, 0x0000000100000000
                mul     q
                add     d0, q
                sbb     a, 0
                sbb     d, 0
                sub     d1, a
                sbb     d2, d
                sbb     d3, 0
                sbb     h, 0
                mov     a, 0xffffffff00000001
                mul     q
                sub     d3, a
                sbb     h, d

// Now our top word h is either zero or all 1s, and we use this to discriminate
// whether a correction is needed because our result is negative, as a bitmask
// Do a masked addition of p_256 and write back

                mov     ashort, 0x00000000ffffffff
                and     a, h
                xor     c, c
                sub     c, a
                add     d0, h
                mov     [z], d0
                adc     d1, a
                mov     [z+8], d1
                adc     d2, 0
                mov     [z+16],d2
                adc     d3, c
                mov     [z+24],d3

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
