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
// Montgomery reduce, z := (x' / 2^{64p}) MOD m
// Inputs x[n], m[k], p; output z[k]
//
//    extern void bignum_montredc
//     (uint64_t k, uint64_t *z,
//      uint64_t n, uint64_t *x, uint64_t *m, uint64_t p);
//
// Does a := (x' / 2^{64p}) mod m where x' = x if n <= p + k and in general
// is the lowest (p+k) digits of x, assuming x' <= 2^{64p} * m. That is,
// p-fold Montgomery reduction w.r.t. a k-digit modulus m giving a k-digit
// answer.
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = n, X3 = x, X4 = m, X5 = p
// ----------------------------------------------------------------------------

#define k x0
#define z x1
#define n x2
#define x x3
#define m x4
#define p x5

// Negated modular inverse
#define w x6
// Outer loop counter
#define i x7
// Inner loop counter
#define j x8
// Home for Montgomery multiplier
#define d x9
// Top carry for current window
#define c x14

#define h x10
#define e x11
#define l x12
#define a x13

// Some more intuitive names for temp regs in initial word-level negmodinv.
// These just use i and j again, which aren't used early on.

#define one x7
#define e1 x7
#define e2 x8
#define e4 x7
#define e8 x8

.text
.globl bignum_montredc

bignum_montredc:

// If k = 0 the whole operation is trivial

                cbz     k, end

// Compute word-level negated modular inverse w for m == m[0].
// This is essentially the same as word_negmodinv.

                ldr     a, [m]
                lsl     w, a, 2
                sub     w, a, w
                eor     w, w, 2
                mov     one, 1
                madd    e1, a, w, one
                mul     e2, e1, e1
                madd    w, e1, w, w
                mul     e4, e2, e2
                madd    w, e2, w, w
                mul     e8, e4, e4
                madd    w, e4, w, w
                madd    w, e8, w, w

// Initialize z to the lowest k digits of the input, zero-padding if n < k.

                cmp     n, k
                csel    j, k, n, cs
                mov     i, xzr
                cbz     j, padloop
copyloop:
                ldr     a, [x, i, LSL 3]
                str     a, [z, i, LSL 3]
                add     i, i, 1
                cmp     i, j
                bcc     copyloop

                cmp     i, k
                bcs     initialized

padloop:
                str     xzr, [z, i, LSL 3]
                add     i, i, 1
                cmp     i, k
                bcc     padloop

initialized:
                mov     c, xzr

// Now if p = 0 we just need the corrective tail, and even that is
// only needed for the case when the input is exactly the modulus,
// to maintain the <= 2^64p * n precondition

                cbz     p, corrective

// Outer loop, just doing a standard Montgomery reduction on z

                mov     i, xzr
outerloop:

                ldr     e, [z]
                mul     d, e, w
                ldr     a, [m]
                mul     l, d, a
                umulh   h, d, a
                adds    e, e, l         // Will be zero but want the carry
                mov     j, 1
                sub     a, k, 1
                cbz     a, montend
montloop:
                ldr     a, [m, j, LSL 3]
                ldr     e, [z, j, LSL 3]
                mul     l, d, a
                adcs    e, e, h
                umulh   h, d, a
                adc     h, h, xzr
                adds    e, e, l
                sub     l, j, 1
                str     e, [z, l, LSL 3]
                add     j, j, 1
                sub     a, j, k
                cbnz    a, montloop
montend:
                adcs    h, h, c
                adc     c, xzr, xzr
                add     j, j, i
                cmp     j, n
                bcs     offtheend
                ldr     a, [x, j, LSL 3]
                adds    h, h, a
                adc     c, c, xzr
offtheend:
                sub     j, k, 1
                str     h, [z, j, LSL 3]

// End of outer loop

                add     i, i, 1
                cmp     i, p
                bcc     outerloop

// Now do a comparison of (c::z) with (0::m) to set a final correction mask
// indicating that (c::z) >= m and so we need to subtract m.

corrective:

                subs    j, xzr, xzr
cmploop:
                ldr     a, [z, j, LSL 3]
                ldr     e, [m, j, LSL 3]
                sbcs    xzr, a, e
                add     j, j, 1
                sub     a, j, k
                cbnz    a, cmploop

                sbcs    xzr, c, xzr
                csetm   c, cs

// Now do a masked subtraction of m for the final reduced result.

                subs    j, xzr, xzr
corrloop:
                ldr     a, [z, j, LSL 3]
                ldr     e, [m, j, LSL 3]
                and     e, e, c
                sbcs    a, a, e
                str     a, [z, j, LSL 3]
                add     j, j, 1
                sub     a, j, k
                cbnz    a, corrloop

end:
                ret
