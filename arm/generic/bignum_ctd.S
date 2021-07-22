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
// Count trailing zero digits (64-bit words)
// Input x[k]; output function return
//
//    extern uint64_t bignum_ctd (uint64_t k, uint64_t *x);
//
// In the case of a zero bignum as input the result is k
//
// Standard ARM ABI: X0 = k, X1 = x, returns X0
// ----------------------------------------------------------------------------

        .globl  bignum_ctd
        .text

#define k x0
#define x x1
#define i x2
#define a x3


bignum_ctd:

// If the bignum is zero-length, x0 is already the right answer of 0

                cbz     k, end

// Record in i that the lowest nonzero word is i, where i = k means
// that the bignum was entirely zero

                mov     i, k
loop:
                sub     k, k, #1
                ldr     a, [x, k, lsl #3]
                cmp     a, #0
                csel    i, k, i, ne
                cbnz    k, loop

// Now return i

                mov     x0, i

end:
                ret
