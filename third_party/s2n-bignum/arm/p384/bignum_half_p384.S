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
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------

        .globl  bignum_half_p384
        .globl  _bignum_half_p384
        .text
        .balign 4

#define z x0
#define x x1

#define d0 x2
#define d1 x3
#define d2 x4
#define d3 x5
#define d4 x6
#define d5 x7
#define d6 x8
#define d7 x9
#define m x10
#define n x11


bignum_half_p384:
_bignum_half_p384:

// Load the 4 digits of x

                ldp     d0, d1, [x]
                ldp     d2, d3, [x, #16]
                ldp     d4, d5, [x, #32]

// Get a bitmask corresponding to the lowest bit of the input

                and     m, d0, #1
                neg     m, m

// Do a masked addition of p_384, catching carry in a 7th word

                mov     n, #0x00000000ffffffff
                and     n, n, m
                adds    d0, d0, n
                mov     n, #0xffffffff00000000
                and     n, n, m
                adcs    d1, d1, n
                mov     n, #0xfffffffffffffffe
                and     n, n, m
                adcs    d2, d2, n
                adcs    d3, d3, m
                adcs    d4, d4, m
                adcs    d5, d5, m
                adc     d6, xzr, xzr

// Now shift that sum right one place

                extr    d0, d1, d0, #1
                extr    d1, d2, d1, #1
                extr    d2, d3, d2, #1
                extr    d3, d4, d3, #1
                extr    d4, d5, d4, #1
                extr    d5, d6, d5, #1

// Store back

                stp     d0, d1, [z]
                stp     d2, d3, [z, #16]
                stp     d4, d5, [z, #32]

// Return

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
