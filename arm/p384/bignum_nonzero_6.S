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
// 384-bit nonzeroness test, returning 1 if x is nonzero, 0 if x is zero
// Input x[6]; output function return
//
//    extern uint64_t bignum_nonzero_6(uint64_t x[static 6]);
//
// Standard ARM ABI: X0 = x, returns X0
// ----------------------------------------------------------------------------

        .globl  bignum_nonzero_6
        .globl  _bignum_nonzero_6
        .text
        .balign 4

#define x x0
#define a x1
#define d x2
#define c x3


bignum_nonzero_6:
_bignum_nonzero_6:

// Generate a = an OR of all the words in the bignum

                ldp     a, d, [x]
                orr     a, a, d
                ldp     c, d, [x, #16]
                orr     c, c, d
                orr     a, a, c
                ldp     c, d, [x, #32]
                orr     c, c, d
                orr     a, a, c

// Set a standard C condition based on whether a is nonzero

                cmp     a, xzr
                cset    x0, ne

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
