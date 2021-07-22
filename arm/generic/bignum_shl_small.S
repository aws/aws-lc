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
// Shift bignum left by c < 64 bits z := x * 2^c
// Inputs x[n], c; outputs function return (carry-out) and z[k]
//
//    extern uint64_t bignum_shl_small
//     (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x, uint64_t c);
//
// Does the "z := x << c" operation where x is n digits, result z is p.
// The shift count c is masked to 6 bits so it actually uses c' = c mod 64.
// The return value is the "next word" of a p+1 bit result, if n <= p.
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = n, X3 = x, X4 = c, returns X0
// ----------------------------------------------------------------------------

        .globl  bignum_shl_small
        .text

#define p x0
#define z x1
#define n x2
#define x x3
#define c x4

#define d x5
#define a x6
#define b x7
#define m x8
#define t x9
#define i x10


bignum_shl_small:

// First clamp the input size n := min(p,n) since we can never need to read
// past the p'th term of the input to generate p-digit output.

                cmp     n, p
                csel    n, p, n, cs

// Initialize counter i and "previous word" carry b to zero
// and skip main loop if n = 0

                mov     b, xzr
                mov     i, xzr
                cbz     n, tail

// Set up a mask for nonzero shift and a negated version of the shift.
// Note that all basic word-level shifts are predictably masked to 6 bits.

                ands    xzr, c, #63
                csetm   m, ne
                neg     d, c

// Now the main loop
loop:
                ldr     t, [x, i, lsl #3]
                lsl     a, t, c
                orr     a, a, b
                lsr     b, t, d
                and     b, b, m
                str     a, [z, i, lsl #3]
                add     i, i, #1
                cmp     i, n
                bcc     loop

// If we are at the end, finish, otherwise write carry word then zeros

tail:

                cmp     i, p
                bcs     end
                str     b, [z, i, lsl #3]
                mov     b, xzr
                add     i, i, #1
                cmp     i, p
                bcs     end

tloop:
                str     xzr, [z, i, lsl #3]
                add     i, i, #1
                cmp     i, p
                bcc     tloop

// Return top word

end:

                mov     x0, b
                ret
