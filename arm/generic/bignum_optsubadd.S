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
// Optionally subtract or add, z := x + sgn(p) * y interpreting p as signed
// Inputs x[k], p, y[k]; outputs function return (carry-out) and z[k]
//
//    extern uint64_t bignum_optsubadd
//     (uint64_t k, uint64_t *z, uint64_t *x, uint64_t p, uint64_t *y);
//
// If p has top bit set (i.e. is negative as a signed int) return z := x - y
// Else if p is nonzero (i.e. is positive as a signed int) return z := x + y
// Otherwise (i.e. p is zero) return z := x
//
// Return in X0 = the top carry, which will be 0 or 1, and appropriate for
// addition or subtraction respectively (and always zero for p = 0)
//
// 2^{64*k} * -carryout + z = x - y [for subtraction]
// 2^{64*k} * carryout + z = x + y [for addition]
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = x, X3 = p, X4 = y, returns X0
// ----------------------------------------------------------------------------

#define k x0
#define z x1
#define x x2
#define p x3
#define y x4

#define m x3
#define q x5
#define a x6
#define b x7
#define i x8

.text
.globl bignum_optsubadd

bignum_optsubadd:

// if k = 0 do nothing. This is also the right top carry in X0

                cbz     k, end

// Turn the input p into two bitmasks, m indicating to use the y input at
// all (same register as p) and q indicating a sign-flip

                cmp     p, xzr
                csetm   m, ne
                csetm   q, mi

// Generate an initial carry-in for the negating case only to add 1; this
// is because we are actually going to do complements of the words of y

                adds    xzr, q, q

// Main loop

                mov     i, xzr
loop:
                ldr     b, [y, i]
                eor     b, b, q
                ldr     a, [x, i]
                and     b, b, m
                adcs    a, a, b
                str     a, [z, i]
                add     i, i, #8
                sub     k, k, #1
                cbnz    k, loop

// Return carry flag, fixing up inversion for negative case

                adc     x0, xzr, xzr
                neg     q, q
                eor     x0, x0, q

end:
                ret
