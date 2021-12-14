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
// Add modulo p_256k1, z := (x + y) mod p_256k1, assuming x and y reduced
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_add_p256k1
//     (uint64_t z[static 4], uint64_t x[static 4], uint64_t y[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// ----------------------------------------------------------------------------


        .globl  bignum_add_p256k1
        .text

#define z %rdi
#define x %rsi
#define y %rdx

#define d0 %rcx
#define d1 %r8
#define d2 %r9
#define d3 %r10

#define dd %rax

// These two re-use inputs x and y when safe to do so

#define l %rsi
#define c %rdx

bignum_add_p256k1:

// Load and add the two inputs as 2^256 * (-c) + [d3;d2;d1;d0] = x + y

        movq    (x), d0
        addq    (y), d0
        movq    8(x), d1
        adcq    8(y), d1
        movq    16(x), d2
        adcq    16(y), d2
        movq    24(x), d3
        adcq    24(y), d3
        sbbq    c, c

// Create dd = d3 AND d2 AND d1 to condense the later comparison
// We hope this will interleave with the addition, though we can't
// express that directly as the AND operation destroys the carry flag.

        movq    d1, dd
        andq    d2, dd
        andq    d3, dd

// Decide whether z >= p_256k1 <=> z + 4294968273 >= 2^256.
// For the lowest word use d0 + 4294968273 >= 2^64 <=> ~4294968273 < d0

        movq    $~4294968273, l
        cmpq    d0, l
        adcq    $0, dd
        sbbq    $0, c

// Now c <> 0 <=> z >= p_256k1, so mask the constant l accordingly

        notq    l
        cmovzq  c, l

// If z >= p_256k1 do z := z - p_256k1, i.e. add l in 4 digits

        addq    l, d0
        movq    d0, (z)
        adcq    $0, d1
        movq    d1, 8(z)
        adcq    $0, d2
        movq    d2, 16(z)
        adcq    $0, d3
        movq    d3, 24(z)

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
