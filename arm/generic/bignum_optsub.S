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
// Optionally subtract, z := x - y (if p nonzero) or z := x (if p zero)
// Inputs x[k], p, y[k]; outputs function return (carry-out) and z[k]
//
//    extern uint64_t bignum_optsub
//     (uint64_t k, uint64_t *z, uint64_t *x, uint64_t p, uint64_t *y);
//
// It is assumed that all numbers x, y and z have the same size k digits.
// Returns carry-out as per usual subtraction, always 0 if p was zero.
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = x, X3 = p, X4 = y, returns X0
// ----------------------------------------------------------------------------

        .globl  bignum_optsub
        .text

#define k x0
#define z x1
#define x x2
#define p x3
#define m x3
#define y x4
#define a x5
#define b x6
#define i x7


bignum_optsub:

// if k = 0 do nothing. This is also the right top carry in X0

                cbz     k, end

// Convert p into a strict bitmask (same register in fact)

                cmp     p, xzr
                csetm   m, ne

// Set i = 0 *and* make sure initial ~CF = 0

                subs    i, xzr, xzr

// Main loop

loop:
                ldr     a, [x, i]
                ldr     b, [y, i]
                and     b, b, m
                sbcs    a, a, b
                str     a, [z, i]
                add     i, i, #8
                sub     k, k, #1
                cbnz    k, loop

// Return (non-inverted) carry flag

                cset    x0, cc

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
