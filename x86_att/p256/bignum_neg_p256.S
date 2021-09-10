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
// Negate modulo p_256, z := (-x) mod p_256, assuming x reduced
// Input x[4]; output z[4]
//
//    extern void bignum_neg_p256 (uint64_t z[static 4], uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------


        .globl  bignum_neg_p256
        .text

#define z %rdi
#define x %rsi

#define q %rdx

#define d0 %rax
#define d1 %rcx
#define d2 %r8
#define d3 %r9

#define n1 %r10
#define n3 %r11

#define d0short %eax
#define n1short %r10d

bignum_neg_p256:

// Load the input digits as [d3;d2;d1;d0] and also set a bitmask q
// for the input being nonzero, so that we avoid doing -0 = p_256
// and hence maintain strict modular reduction

                movq    (x), d0
                movq    8(x), d1
                movq    d0, n1
                orq     d1, n1
                movq    16(x), d2
                movq    24(x), d3
                movq    d2, n3
                orq     d3, n3
                orq     n1, n3
                negq    n3
                sbbq    q, q

// Load the non-trivial words of p_256 = [n3;0;n1;-1] and mask them with q

                movl    $0x00000000ffffffff, n1short
                movq    $0xffffffff00000001, n3
                andq    q, n1
                andq    q, n3

// Do the subtraction, getting it as [n3;d0;n1;q] to avoid moves

                subq    d0, q
                movl    $0, d0short
                sbbq    d1, n1
                sbbq    d2, d0
                sbbq    d3, n3

// Write back

                movq    q, (z)
                movq    n1, 8(z)
                movq    d0, 16(z)
                movq    n3, 24(z)

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
