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
// Double modulo p_521, z := (2 * x) mod p_521, assuming x reduced
// Input x[9]; output z[9]
//
//    extern void bignum_double_p521
//     (uint64_t z[static 9], uint64_t x[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------


        .globl  bignum_double_p521
        .globl  _bignum_double_p521
        .text

#define z %rdi
#define x %rsi

#define a %rax
#define c %rcx



bignum_double_p521:
_bignum_double_p521:

// We can decide whether 2 * x >= p_521 just by 2 * x >= 2^521, which
// as we assume x < p_521 amounts to looking at bit 8 of the top word

        movq    64(x), c
        btq     $8, c

// Now if 2 * x >= p_521 we want 2 * x - p_521 = (2 * x + 1) - 2^521
// and otherwise just 2 * x. Feed in the condition as the carry bit
// to get 2 * x + [2 * x >= p_521] then just mask it off to 521 bits.

        movq    (x), a
        adcq    a, a
        movq    a, (z)

        movq    8(x), a
        adcq    a, a
        movq    a, 8(z)

        movq    16(x), a
        adcq    a, a
        movq    a, 16(z)

        movq    24(x), a
        adcq    a, a
        movq    a, 24(z)

        movq    32(x), a
        adcq    a, a
        movq    a, 32(z)

        movq    40(x), a
        adcq    a, a
        movq    a, 40(z)

        movq    48(x), a
        adcq    a, a
        movq    a, 48(z)

        movq    56(x), a
        adcq    a, a
        movq    a, 56(z)

        adcq    c, c
        andq    $0x1FF, c
        movq    c, 64(z)

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
