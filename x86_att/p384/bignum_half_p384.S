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
// Halve modulo p_384, z := (x / 2) mod p_384, assuming x reduced
// Input x[6]; output z[6]
//
//    extern void bignum_half_p384
//     (uint64_t z[static 6], uint64_t x[static 6]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------


        .globl  bignum_half_p384
        .globl  _bignum_half_p384
        .text

#define z %rdi
#define x %rsi

#define a %rax
#define d0 %rcx
#define d1 %rdx
#define d2 %r8
#define d3 %r9
#define d4 %r10
#define d5 %r11

#define d0short %ecx
#define d3short %r9d



bignum_half_p384:
_bignum_half_p384:

// Load lowest digit and get a mask for its lowest bit in d3

                movq    (x), a
                movl    $1, d3short
                andq    a, d3
                negq    d3

// Create a masked version of p_384 (top 3 words = the mask itself)

                movl    $0x00000000ffffffff, d0short
                andq    d3, d0
                movq    d0, d1
                xorq    d3, d1
                movq    d3, d2
                addq    d2, d2
                andq    d3, d2
                movq    d3, d4
                movq    d3, d5

// Perform addition with masked p_384. Catch the carry in a, as a bitmask
// for convenience though we only use its LSB below with SHRD

                addq    a, d0
                adcq    8(x), d1
                adcq    16(x), d2
                adcq    24(x), d3
                adcq    32(x), d4
                adcq    40(x), d5
                sbbq    a, a

// Shift right, pushing the carry back down, and store back

                shrdq   $1, d1, d0
                movq    d0, (z)
                shrdq   $1, d2, d1
                movq    d1, 8(z)
                shrdq   $1, d3, d2
                movq    d2, 16(z)
                shrdq   $1, d4, d3
                movq    d3, 24(z)
                shrdq   $1, d5, d4
                movq    d4, 32(z)
                shrdq   $1, a, d5
                movq    d5, 40(z)

// Return

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
