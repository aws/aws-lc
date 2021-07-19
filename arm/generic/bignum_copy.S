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
// Copy bignum with zero-extension or truncation, z := x
// Input x[n]; output z[k]
//
//    extern void bignum_copy
//      (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x);
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = n, X3 = x
// ----------------------------------------------------------------------------

#define k x0
#define z x1
#define n x2
#define x x3

#define i x4
#define a x5

.text
.globl bignum_copy

bignum_copy:

// Replace n with min(k,n) so we are definitely safe copying those
// Initialize the element counter to 0

                cmp     k, n
                csel    n, k, n, cc
                mov     i, #0

// If min(k,n) = 0 jump to the padding stage

                cbz     n, padding

copyloop:
                ldr     a, [x, i, lsl #3]
                str     a, [z, i, lsl #3]
                add     i, i, #1
                cmp     i, n
                bcc     copyloop

padding:
                cmp     i, k
                bcs     end
padloop:
                str     xzr, [z, i, lsl #3]
                add     i, i, #1
                cmp     i, k
                bcc     padloop

end:            ret
