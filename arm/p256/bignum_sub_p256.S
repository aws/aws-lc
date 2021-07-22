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
// Standard ARM ABI: X0 = z, X1 = x, X2 = y
// ----------------------------------------------------------------------------

        .globl  bignum_sub_p256
        .text

#define z x0
#define x x1
#define y x2
#define c x3
#define l x4
#define d0 x5
#define d1 x6
#define d2 x7
#define d3 x8


bignum_sub_p256:

// First just subtract the numbers as [d3; d2; d1; d0]
// Set a mask based on (inverted) carry indicating x < y = correction is needed

                ldp     d0, d1, [x]
                ldp     l, c, [y]
                subs    d0, d0, l
                sbcs    d1, d1, c
                ldp     d2, d3, [x, #16]
                ldp     l, c, [y, #16]
                sbcs    d2, d2, l
                sbcs    d3, d3, c

// Create a mask for the condition x < y, when we need to correct

                csetm   c, cc

// Now correct by adding masked p_256

                adds    d0, d0, c
                mov     l, #0x00000000ffffffff
                and     l, l, c
                adcs    d1, d1, l
                adcs    d2, d2, xzr
                mov     l, #0xffffffff00000001
                and     l, l, c
                adc     d3, d3, l

// Store the result

                stp     d0, d1, [z]
                stp     d2, d3, [z, #16]

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
