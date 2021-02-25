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
// Test bignum for even-ness
// Input x[k]; output function return
//
//    extern uint64_t bignum_even (uint64_t k, uint64_t *x);
//
// Standard ARM ABI: X0 = k, X1 = x, returns X0
// ----------------------------------------------------------------------------

.text
.globl bignum_even

bignum_even:

                cbz     x0, end                 // if k = 0, that's the return!
                ldr     x0, [x1]
                and     x0, x0, 1

end:
                eor     x0, x0, 1
                ret
