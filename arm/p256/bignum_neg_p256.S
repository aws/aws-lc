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
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------

#define z x0
#define x x1

#define p x2
#define t x3

#define d0 x4
#define d1 x5
#define d2 x6
#define d3 x7

.text
.globl bignum_neg_p256

bignum_neg_p256:

// Load the 4 digits of x

                ldp     d0, d1, [x]
                ldp     d2, d3, [x, #16]

// Set a bitmask p for the input being nonzero, so that we avoid doing
// -0 = p_256 and hence maintain strict modular reduction

                orr     t, d0, d1
                orr     p, d2, d3
                orr     p, p, t
                cmp     p, #0
                csetm   p, ne

// Load the nontrivial words of p_256 = [n3;0;n1;-1], mask them
// with p and subtract

                subs    d0, p, d0

                mov     t, #0x00000000ffffffff
                and     t, t, p
                sbcs    d1, t, d1

                sbcs    d2, xzr, d2

                mov     t, #0xffffffff00000001
                and     t, t, p
                sbc     d3, t, d3

// Write back the result

                stp     d0, d1, [z]
                stp     d2, d3, [z, #16]

// Return

                ret
