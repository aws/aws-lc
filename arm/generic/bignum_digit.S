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
// Select digit x[n]
// Inputs x[k], n; output function return
//
//    extern uint64_t bignum_digit (uint64_t k, uint64_t *x, uint64_t n);
//
// n'th digit of a k-digit (digit=64 bits) bignum, in constant-time style.
// Indexing starts at 0, which is the least significant digit (little-endian).
// Returns zero if n >= k, i.e. we read a digit off the end of the bignum.
//
// Standard ARM ABI: X0 = k, X1 = x, X2 = n, returns X0
// ----------------------------------------------------------------------------

#define k x0
#define x x1
#define n x2

#define d x3
#define i x4
#define a x5

.text
.globl bignum_digit

bignum_digit:

// For length zero finish immediately (the return value in x0 is 0)

                cbz     k, end

// Set default of zero, run over all the digits and take note of the n'th one

                mov     d, xzr
                mov     i, xzr
loop:
                ldr     a, [x, i, lsl #3]
                cmp     i, n
                csel    d, a, d, eq
                add     i, i, #1
                cmp     i, k
                bcc     loop

// Return

                mov     x0, d

end:
                ret
