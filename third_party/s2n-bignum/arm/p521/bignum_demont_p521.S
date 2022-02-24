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
// Convert from Montgomery form z := (x / 2^576) mod p_521, assuming x reduced
// Input x[9]; output z[9]
//
//    extern void bignum_demont_p521
//     (uint64_t z[static 9], uint64_t x[static 9]);
//
// This assumes the input is < p_521 for correctness. If this is not the case,
// use the variant "bignum_deamont_p521" instead.
//
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------

        .globl  bignum_demont_p521
        .globl  _bignum_demont_p521
        .text
        .balign 4

// Input parameters

#define z x0
#define x x1

// Rotating registers for the intermediate windows

#define d0 x2
#define d1 x3
#define d2 x4
#define d3 x5
#define d4 x2
#define d5 x3
#define d6 x4
#define d7 x5
#define d8 x2
#define c x6

bignum_demont_p521:
_bignum_demont_p521:

// Rotate, as a 521-bit quantity, by 9*64 - 521 = 55 bits right.

                ldp     d0, d1, [x]
                lsl     c, d0, #9
                extr    d0, d1, d0, #55
                ldp     d2, d3, [x, #16]
                extr    d1, d2, d1, #55
                stp     d0, d1, [z]
                extr    d2, d3, d2, #55
                ldp     d4, d5, [x, #32]
                extr    d3, d4, d3, #55
                stp     d2, d3, [z, #16]
                extr    d4, d5, d4, #55
                ldp     d6, d7, [x, #48]
                extr    d5, d6, d5, #55
                stp     d4, d5, [z, #32]
                extr    d6, d7, d6, #55
                ldr     d8, [x, #64]
                orr     d8, d8, c
                extr    d7, d8, d7, #55
                stp     d6, d7, [z, #48]
                lsr     d8, d8, #55
                str     d8, [z, #64]
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
