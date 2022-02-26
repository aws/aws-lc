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
// Add modulo p_25519, z := (x + y) mod p_25519, assuming x and y reduced
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_add_p25519
//     (uint64_t z[static 4], uint64_t x[static 4], uint64_t y[static 4]);
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = y
// ----------------------------------------------------------------------------

        .globl  bignum_add_p25519
        .globl  _bignum_add_p25519
        .text
        .balign 4

#define z x0
#define x x1
#define y x2
#define d0 x3
#define d1 x4
#define d2 x5
#define d3 x6
#define c0 x7
#define c1 x8
#define c2 x9
#define c3 x10

bignum_add_p25519:
_bignum_add_p25519:

// Add as [d3; d2; d1; d0] = x + y; since we assume x, y < 2^255 - 19
// this sum fits in 256 bits

                ldp     d0, d1, [x]
                ldp     c0, c1, [y]
                adds    d0, d0, c0
                adcs    d1, d1, c1
                ldp     d2, d3, [x, #16]
                ldp     c0, c1, [y, #16]
                adcs    d2, d2, c0
                adc     d3, d3, c1

// Now x + y >= 2^255 - 19 <=> x + y + (2^255 + 19) >= 2^256
// Form [c3; c2; c1; c0] = (x + y) + (2^255 + 19), with CF for the comparison

                mov     c3, #0x8000000000000000
                adds    c0, d0, #19
                adcs    c1, d1, xzr
                adcs    c2, d2, xzr
                adcs    c3, d3, c3

// If the comparison holds, select [c3; c2; c1; c0]. There's no need to mask
// it since in this case it is ((x + y) + (2^255 + 19)) - 2^256 because the
// top carry is lost, which is the desired (x + y) - (2^255 - 19).

                csel    d0, d0, c0, cc
                csel    d1, d1, c1, cc
                csel    d2, d2, c2, cc
                csel    d3, d3, c3, cc

// Store the result

                stp     d0, d1, [z]
                stp     d2, d3, [z, #16]

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
