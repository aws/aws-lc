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
// Multiply by a single word modulo p_256k1, z := (c * x) mod p_256k1, assuming
// x reduced
// Inputs c, x[4]; output z[4]
//
//    extern void bignum_cmul_p256k1
//     (uint64_t z[static 4], uint64_t c, uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = c, RDX = x
// ----------------------------------------------------------------------------


        .globl  bignum_cmul_p256k1
        .text

#define z %rdi

// Temporarily moved here for initial multiply

#define x %rcx
#define c %rcx

// Likewise this is thrown away after initial multiply

#define d %rdx
#define h %rdx

#define a %rax
#define ashort %eax
#define q %rax

#define d0 %rsi
#define d1 %r8
#define d2 %r9
#define d3 %r10

bignum_cmul_p256k1:

// Shuffle inputs (since we want multiplier in %rdx)

                movq    %rdx, x
                movq    %rsi, d

// Multiply, accumulating the result as 2^256 * h + [d3;d2;d1;d0]

                mulxq   (x), d0, d1
                mulxq   8(x), a, d2
                addq    a, d1
                mulxq   16(x), a, d3
                adcq    a, d2
                mulxq   24(x), a, h
                adcq    a, d3
                adcq    $0, h

// Now the quotient estimate is q = h + 1, and then we do the reduction,
// writing z = [d3;d2;d1;d0], as z' = (2^256 * h + z) - q * p_256k1 =
// (2^256 * h + z) - q * (2^256 - 4294968273) = -2^256 + (z + 4294968273 * q)

                leaq    1(h), q
                movq    $4294968273, c
                mulq    c

                addq    %rax, d0
                adcq    %rdx, d1
                adcq    $0, d2
                adcq    $0, d3

// Because of the implicit -2^256, CF means >= 0 so z' is the answer; ~CF
// means z' < 0 so we add p_256k1, which in 4 digits means subtracting c.

                movq    $0, a
                cmovcq  a, c

                subq    c, d0
                movq    d0, (z)
                sbbq    a, d1
                movq    d1, 8(z)
                sbbq    a, d2
                movq    d2, 16(z)
                sbbq    a, d3
                movq    d3, 24(z)

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
