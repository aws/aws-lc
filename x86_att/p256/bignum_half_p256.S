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
// Halve modulo p_256, z := (x / 2) mod p_256, assuming x reduced
// Input x[4]; output z[4]
//
//    extern void bignum_half_p256
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------


        .globl  bignum_half_p256
        .text

#define z %rdi
#define x %rsi

#define a %rax
#define d0 %rcx
#define d1 %rdx
#define d2 %r8
#define d3 %r9

#define d0short %ecx
#define d1short %edx



bignum_half_p256:

// Load lowest digit and get a mask for its lowest bit in d0

                movq    (x), a
                movl    $1, d0short
                andq    a, d0
                negq    d0

// Create a masked version of p_256

                movl    $0x00000000ffffffff, d1short
                xorq    d3, d3
                andq    d0, d1
                subq    d1, d3
                xorq    d2, d2

// Perform addition with masked p_256. Catch the carry in a, as a bitmask
// for convenience though we only use its LSB below with SHRD

                addq    a, d0
                adcq    8(x), d1
                adcq    16(x), d2
                adcq    24(x), d3
                sbbq    a, a

// Shift right, pushing the carry back down, and store back

                shrdq   $1, d1, d0
                movq    d0, (z)
                shrdq   $1, d2, d1
                movq    d1, 8(z)
                shrdq   $1, d3, d2
                movq    d2, 16(z)
                shrdq   $1, a, d3
                movq    d3, 24(z)

// Return

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
