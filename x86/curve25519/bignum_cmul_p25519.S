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
// Multiply by a single word modulo p_25519, z := (c * x) mod p_25519, assuming
// x reduced
// Inputs c, x[4]; output z[4]
//
//    extern void bignum_cmul_p25519
//     (uint64_t z[static 4], uint64_t c, uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = c, RDX = x
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_cmul_p25519
        .globl  _bignum_cmul_p25519
        .text

#define z rdi

// Temporarily moved here for initial multiply

#define x rcx
#define c rcx
#define cshort ecx

// Used as a zero register after the initial move

#define zero rsi
#define zeroe esi

// Likewise this is thrown away after initial multiply

#define d rdx
#define a rax
#define ashort eax

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11

bignum_cmul_p25519:
_bignum_cmul_p25519:

// Shuffle inputs (since we want multiplier in rdx)

                mov     x, rdx
                mov     d, rsi

// Multiply, accumulating the result as [d4;d3;d2;d1;d0]

                mulx    d1, d0, [x]
                mulx    d2, a, [x+8]
                add     d1, a
                mulx    d3, a, [x+16]
                adc     d2, a
                mulx    a, d, [x+24]
                adc     d3, d
                adc     a, 0

// Let [d4;d3;d2;d1;d0] = 2^255 * h + l, and use q = h + 1 as the initial
// quotient estimate, which is either right or 1 too big.

                shld    a, d3, 1
                mov     cshort, 19
                inc     a
                bts     d3, 63
                mul     c
                xor     zeroe, zeroe
                add     d0, a
                adc     d1, d
                adc     d2, zero
                adc     d3, zero

// Correct if CF = 0 by subtracting 19, either way masking to
// 255 bits, i.e. by effectively adding p_25519 to the "full" answer

                cmovc   c, zero
                sub     d0, c
                sbb     d1, zero
                sbb     d2, zero
                sbb     d3, zero
                btr     d3, 63

// Write everything back

                mov     [z], d0
                mov     [z+8], d1
                mov     [z+16], d2
                mov     [z+24], d3

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
