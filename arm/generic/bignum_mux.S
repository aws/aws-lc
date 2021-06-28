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
// Multiplex/select z := x (if p nonzero) or z := y (if p zero)
// Inputs p, x[k], y[k]; output z[k]
//
//    extern void bignum_mux
//     (uint64_t p, uint64_t k, uint64_t *z, uint64_t *x, uint64_t *y);
//
// It is assumed that all numbers x, y and z have the same size k digits.
//
// Standard ARM ABI: X0 = p, X1 = k, X2 = z, X3 = x, X4 = y
// ----------------------------------------------------------------------------

#define b x0
#define k x1
#define z x2
#define x x3
#define y x4
#define a x5

.text
.globl bignum_mux

bignum_mux:

                cbz     k, end                  // if k = 0 skip the loop
                cmp     b, 0                    // Set condition codes b = 0

// We've set cc's from b once and for all and can now re-use "b" as a temporary

loop:
                sub     k, k, 1
                ldr     a, [x, k, LSL 3]
                ldr     b, [y, k, LSL 3]
                csel    a, a, b, ne
                str     a, [z, k, LSL 3]
                cbnz    k, loop

end:
                ret
