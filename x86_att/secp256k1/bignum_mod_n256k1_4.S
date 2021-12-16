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
// Reduce modulo group order, z := x mod n_256k1
// Input x[4]; output z[4]
//
//    extern void bignum_mod_n256k1_4
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// Reduction is modulo the group order of the secp256k1 curve.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------


        .globl  bignum_mod_n256k1_4
        .text

#define z %rdi
#define x %rsi

#define d0 %rdx
#define d1 %rcx
#define d2 %r8
#define d3 %r9

#define n0 %rax
#define n1 %r10
#define n2 %r11

#define n2short %r11d

// Can re-use this as a temporary once we've loaded the input

#define c %rsi

bignum_mod_n256k1_4:

// Load a set of registers [0; n2; n1; n0] = 2^256 - n_256k1

        movq    $0x402da1732fc9bebf, n0
        movq    $0x4551231950b75fc4, n1
        movl    $1, n2short

// Load the input and compute x + (2^256 - n_256k1)

        movq    (x), d0
        addq    n0, d0
        movq    8(x), d1
        adcq    n1, d1
        movq    16(x), d2
        adcq    n2, d2
        movq    24(x), d3
        adcq    $0, d3

// Now CF is set iff 2^256 <= x + (2^256 - n_256k1), i.e. iff n_256k1 <= x.
// Create a mask for the condition x < n, and mask the three nontrivial digits
// ready to undo the previous addition with a compensating subtraction

        sbbq    c, c
        notq    c
        andq    c, n0
        andq    c, n1
        andq    c, n2

// Now subtract mask * (2^256 - n_256k1) again and store

        subq    n0, d0
        movq    d0, (z)
        sbbq    n1, d1
        movq    d1, 8(z)
        sbbq    n2, d2
        movq    d2, 16(z)
        sbbq    $0, d3
        movq    d3, 24(z)

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
