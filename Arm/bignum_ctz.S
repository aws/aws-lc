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
// Count trailing zero bits
// Input x[k]; output function return
//
//    extern uint64_t bignum_ctz (uint64_t k, uint64_t *x);
//
//
// In the case of a zero bignum as input the result is 64 * k
//
// In principle this has a precondition k < 2^58, but obviously that
// is always true in practice because of address space limitations
//
// Standard ARM ABI: X0 = k, X1 = x, returns X0
// ----------------------------------------------------------------------------

#define k x0
#define x x1
#define i x2
#define w x3
#define a x4

.text
.globl bignum_ctz

bignum_ctz:

// If the bignum is zero-length, x0 is already the right answer of 0

                cbz     k, end

// Use w = a[i] to store nonzero words in a top-down sweep
// Set the initial default to be as if we had a 1 word directly above

                mov     i, k
                mov     w, 1

loop:
                sub     k, k, 1
                ldr     a, [x, k, LSL 3]
                cmp     a, 0
                csel    i, k, i, ne
                csel    w, a, w, ne
                cbnz    k, loop

// Now w = a[i] is the lowest nonzero word, or in the zero case the
// default of the "extra" 1 = a[k]. We now want 64*i + ctz(w).
//
// ARM doesn't have a direct word ctz instruction, so we emulate it via
// ctz(w) = 64 - clz(~w & (w-1)). This is depending, for cases of the form
// ctz(....1), on the behavior clz(0) = 64, which is guaranteed according
// to the ARM manual.

                mvn     a, w
                sub     w, w, 1
                add     i, i, 1
                and     w, w, a
                lsl     i, i, 6
                clz     a, w
                sub     x0, i, a

end:
                ret
