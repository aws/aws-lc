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
// Subtract modulo p_256, z := (x - y) mod p_256
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_sub_p256
//     (uint64_t z[static 4], uint64_t x[static 4], uint64_t y[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// ----------------------------------------------------------------------------


        .globl  bignum_sub_p256
        .text

#define z %rdi
#define x %rsi
#define y %rdx

#define d0 %rax
#define d1 %rcx
#define d2 %r8
#define d3 %r9

#define n1 %r10
#define n3 %rdx
#define c %r11

#define n1short %r10d



bignum_sub_p256:

// Load and subtract the two inputs as [d3;d2;d1;d0] = x - y (modulo 2^256)

        movq    (x), d0
        subq    (y), d0
        movq    8(x), d1
        sbbq    8(y), d1
        movq    16(x), d2
        sbbq    16(y), d2
        movq    24(x), d3
        sbbq    24(y), d3

// Capture the carry, which indicates x < y, and create corresponding masked
// correction p_256' = [n3; 0; n1; c] to add

        movl    $0x00000000ffffffff, n1short
        sbbq    c, c
        xorq    n3, n3
        andq    c, n1
        subq    n1, n3

// Do the corrective addition and copy to output

        addq    c, d0
        movq    d0, (z)
        adcq    n1, d1
        movq    d1, 8(z)
        adcq    $0, d2
        movq    d2, 16(z)
        adcq    n3, d3
        movq    d3, 24(z)

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
