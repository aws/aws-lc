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
// Select element from 16-element table, z := xs[k*i]
// Inputs xs[16*k], i; output z[k]
//
//    extern void bignum_mux16
//     (uint64_t k, uint64_t *z, uint64_t *xs, uint64_t i);
//
// It is assumed that all numbers xs[16] and the target z have the same size k
// The pointer xs is to a contiguous array of size 16, elements size-k bignums
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = xs, X3 = i
// ----------------------------------------------------------------------------

        .globl  bignum_mux16
        .text

#define k x0
#define z x1
#define x x2
#define i x3

#define a x4
#define b x5
#define j x6
#define n x7


bignum_mux16:

// Copy size into decrementable counter, skip everything if k = 0

                adds    n, k, xzr
                beq     end

// Multiply i by k so we can compare pointer offsets directly with it

                mul     i, i, k

loop:

                ldr     a, [x]
                mov     j, k
        .rep 15
                ldr     b, [x, j, lsl #3]
                cmp     j, i
                csel    a, b, a, eq
                add     j, j, k
        .endr
                str     a, [z]

                add     z, z, #8
                add     x, x, #8
                subs    n, n, #1
                bne     loop

end:
                ret
