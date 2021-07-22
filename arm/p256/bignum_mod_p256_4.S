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
// Reduce modulo field characteristic, z := x mod p_256
// Input x[4]; output z[4]
//
//    extern void bignum_mod_p256_4
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------

        .globl  bignum_mod_p256_4
        .text

#define z x0
#define x x1

#define n0 x2
#define n1 x3
#define n2 x4
#define n3 x5

#define d0 x6
#define d1 x7
#define d2 x8
#define d3 x9


bignum_mod_p256_4:

// Load the three nonzero words of p_256 = [n3;0;n2;n1]

                mov     n0, #0xffffffffffffffff
                mov     n1, #0x00000000ffffffff
                mov     n3, #0xffffffff00000001

// Load the input number

                ldp     d0, d1, [x]
                ldp     d2, d3, [x, #16]

// Do the subtraction.

                subs    n0, d0, n0
                sbcs    n1, d1, n1
                sbcs    n2, d2, xzr
                sbcs    n3, d3, n3

// Now if the carry is *clear* (inversion at work) the subtraction carried
// and hence we should have done nothing, so we reset each n_i = d_i

                csel    n0, d0, n0, cc
                csel    n1, d1, n1, cc
                csel    n2, d2, n2, cc
                csel    n3, d3, n3, cc

// Store the end result

                stp     n0, n1, [z]
                stp     n2, n3, [z, #16]

                ret
