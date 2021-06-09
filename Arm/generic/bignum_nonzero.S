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
// Test bignum for nonzero-ness x =/= 0
// Input x[k]; output function return
//
//    extern uint64_t bignum_nonzero (uint64_t k, uint64_t *x);
//
// Standard ARM ABI: X0 = k, X1 = x, returns X0
// ----------------------------------------------------------------------------

#define k x0
#define x x1
#define a x2
#define c x3

.text
.globl bignum_nonzero

bignum_nonzero:

                mov     c, xzr                  // c will be or of the digits
                cbz     k, end                  // if k = 0 skip the loop

loop:
                sub     k, k, 1
                ldr     a, [x, k, LSL 3]
                orr     c, c, a
                cbnz    k, loop

                cmp     c, xzr
                cset    x0, ne

end:
                ret
