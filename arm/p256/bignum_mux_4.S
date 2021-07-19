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
// 256-bit multiplex/select z := x (if p nonzero) or z := y (if p zero)
// Inputs p, x[4], y[4]; output z[4]
//
//    extern void bignum_mux_4
//     (uint64_t p, uint64_t z[static 4],
//      uint64_t x[static 4], uint64_t y[static 4]);
//
// It is assumed that all numbers x, y and z have the same size 4 digits.
//
// Standard ARM ABI: X0 = p, X1 = z, X2 = x, X3 = y
// ----------------------------------------------------------------------------

#define p x0
#define z x1
#define x x2
#define y x3
#define a x4

.text
.globl bignum_mux_4

bignum_mux_4:

                cmp     p, #0                    // Set condition codes p = 0

                .set    i, 0
                .rep    4
                ldr     a, [x, #8*i]
                ldr     p, [y, #8*i]
                csel    a, a, p, ne
                str     a, [z, #8*i]
                .set    i, (i+1)
                .endr

                ret
