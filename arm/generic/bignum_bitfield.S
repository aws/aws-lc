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
// Select bitfield starting at bit n with length l <= 64
// Inputs x[k], n, l; output function return
//
//    extern uint64_t bignum_bitfield
//     (uint64_t k, uint64_t *x, uint64_t n, uint64_t l);
//
// One-word bitfield from a k-digit (digit=64 bits) bignum, in constant-time
// style. Bitfield starts at bit n and has length l, indexing from 0 (=LSB).
// Digits above the top are treated uniformly as zero, as usual. Since the
// result is returned in a single word, effectively we use l' = min(64,l)
// for the length.
//
// Standard ARM ABI: X0 = k, X1 = x, X2 = n, X3 = l, returns X0
// ----------------------------------------------------------------------------

#define k x0
#define x x1
#define n x2
#define l x3

#define d x4
#define e x5
#define i x6
#define a x7
#define m x8

.text
.globl bignum_bitfield

bignum_bitfield:

// For length zero finish immediately (the return value in x0 is 0)

                cbz     k, end

// Decompose the index into n = 64 * n + m, then increment n for next part

                and     m, n, #63
                lsr     n, n, #6
                add     n, n, #1

// Run over the digits setting d = n'th and e = (n+1)'th

                mov     i, xzr
                mov     e, xzr
loop:
                ldr     a, [x, i, lsl #3]
                cmp     i, n
                csel    d, a, d, cc
                csel    e, a, e, eq
                add     i, i, #1
                cmp     i, k
                bcc     loop

// Override d with 0 if we ran off the end (e will retain original 0).

                cmp     i, n
                csel    d, xzr, d, cc

// Override e if we have m = 0 (i.e. original n was divisible by 64)
// This is because then we want to shift it right by 64 below.

                cmp     m, xzr
                csel    e, xzr, e, eq

// Combine shifted digits to get the bitfield(n,64)

                lsr     d, d, m
                neg     m, m
                lsl     e, e, m
                orr     a, d, e

// Now mask it down to get bitfield (n,l)

                cmp     l, #64
                cset    m, cc
                lsl     m, m, l
                sub     m, m, #1
                and     x0, a, m
end:
                ret
