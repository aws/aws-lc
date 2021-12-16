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
// Negate modulo p_256k1, z := (-x) mod p_256k1, assuming x reduced
// Input x[4]; output z[4]
//
//    extern void bignum_neg_p256k1
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------

        .globl  bignum_neg_p256k1
        .text
        .balign 4

#define z x0
#define x x1

#define p x2
#define d0 x3
#define d1 x4
#define d2 x5
#define d3 x6
#define c x7

bignum_neg_p256k1:

// Load the 4 digits of x and let c be an OR of all the digits

                ldp     d0, d1, [x]
                orr     c, d0, d1
                ldp     d2, d3, [x, #16]
                orr     c, c, d2
                orr     c, c, d3

// Turn q into a strict bitmask, and c a masked constant -4294968273,
// computing it in effect as ~4294968272 = ~(2^32 + 976)

                cmp     c, xzr
                csetm   p, ne
                mov     c, #976
                orr     c, c, #0x100000000
                bic     c, p, c

// Now just do [2^256 - 4294968273] - x where the constant is masked

                subs    d0, c, d0
                sbcs    d1, p, d1
                sbcs    d2, p, d2
                sbc     d3, p, d3

// Write back result and return

                stp     d0, d1, [z]
                stp     d2, d3, [z, #16]

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
