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
// Count leading zero digits (64-bit words)
// Input x[k]; output function return
//
//    extern uint64_t bignum_cld (uint64_t k, uint64_t *x);
//
// In the case of a zero bignum as input the result is k
//
// Standard ARM ABI: X0 = k, X1 = x, returns X0
// ----------------------------------------------------------------------------

        .globl  bignum_cld
        .text

#define k x0
#define x x1
#define i x2
#define a x3
#define j x4


bignum_cld:

// If the bignum is zero-length, x0 is already the right answer of k = 0

                cbz     k, end

// Run over the words j = 0..i-1, and set i := j + 1 when hitting nonzero a[j]

                mov     i, xzr
                mov     j, xzr
loop:
                ldr     a, [x, j, lsl #3]
                add     j, j, #1
                cmp     a, #0
                csel    i, j, i, ne
                cmp     j, k
                bne     loop

                sub     x0, x0, i
end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
