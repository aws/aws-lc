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
// Multiply by a single word, z := c * y
// Inputs c, y[n]; outputs function return (carry-out) and z[k]
//
//    extern uint64_t bignum_cmul
//     (uint64_t k, uint64_t *z, uint64_t c, uint64_t n, uint64_t *y);
//
// Does the "z := c * y" operation where y is n digits, result z is p.
// Truncates the result in general unless p >= n + 1.
//
// The return value is a high/carry word that is meaningful when p >= n as
// giving the high part of the result. Since this is always zero if p > n,
// it is mainly of interest in the special case p = n, i.e. where the source
// and destination have the same nominal size, when it gives the extra word
// of the full result.
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = c, X3 = n, X4 = y, returns X0
// ----------------------------------------------------------------------------

#define p x0
#define z x1
#define c x2
#define n x3
#define x x4

#define i x5
#define h x6
#define l x7
#define a x8

.text
.globl bignum_cmul

bignum_cmul:

// First clamp the input size n := min(p,n) since we can never need to read
// past the p'th term of the input to generate p-digit output.
// Subtract p := p - min(n,p) so it holds the size of the extra tail needed

                cmp     n, p
                csel    n, p, n, cs
                sub     p, p, n

// Initialize current input/output pointer offset i and high part h.
// But then if n = 0 skip the multiplication and go to the tail part

                mov     h, xzr
                mov     i, xzr
                cbz     n, tail

// Initialization of the loop: [h,l] = c * x_0

                ldr     a, [x]
                mul     l, c, a
                umulh   h, c, a
                str     l, [z]
                add     i, i, 8
                subs    n, n, 1
                beq     tail

// Main loop (force CF = 0 at the beginning)

                adds    xzr, xzr, xzr
loop:
                ldr     a, [x, i]
                mul     l, c, a
                adcs    l, l, h
                umulh   h, c, a
                str     l, [z, i]
                add     i, i, 8
                sub     n, n, 1
                cbnz    n, loop

                adc     h, h, xzr

tail:
                cbz     p, end
                str     h, [z, i]
                mov     h, xzr
                subs    p, p, 1
                beq     end

tloop:
                add     i, i, 8
                str     xzr, [z, i]
                sub     p, p, 1
                cbnz    p, tloop

// Return the high/carry word

end:
                mov     x0, h
                ret
